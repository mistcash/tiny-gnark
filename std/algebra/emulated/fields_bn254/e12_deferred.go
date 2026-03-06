package fields_bn254

import (
	"fmt"
	"math/big"

	"github.com/consensys/gnark/constraint/solver"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/std/math/emulated"
	"github.com/consensys/gnark/std/multicommit"
)

func init() {
	solver.RegisterHint(e12PolyMulDivHint, nativeToFqHint)
}

// Sparsity constants for E12 polynomial checks.
const (
	SparsityFull     = 0 // all 12 coefficients non-zero
	SparsitySparse5  = 1 // only {0,1,3,7,9} non-zero (line evaluation)
	SparsitySparse10 = 2 // {0,1,2,3,4,6,7,8,9,10} non-zero (product of two lines)
	SparsityOne      = 3 // identity element (A0=1, rest=0)
)

// e12PolyStep stores one polynomial identity to be verified:
//
//	∏ factors(w) = R(w) + Q(w) · P12(w)  in Fq[w]
//
// where P12(w) = w^12 - 18w^6 + 82.
type e12PolyStep struct {
	factors  []*E12
	sparsity []int
	r        *E12      // remainder (12 Fq coefficients)
	q        []*baseEl // quotient polynomial coefficients in Fq
}

// E12DeferredChecker collects E12 polynomial identity checks and verifies them
// in batch using the Schwartz-Zippel lemma.
//
// Each step asserts that ∏ factors(w) = R(w) + Q(w)·P12(w) in Fq[w].
// The Finalize method obtains a random challenge x ∈ Fq (via multicommit)
// and checks that ∏ F_i(x) = R(x) + Q(x)·P12(x) in Fq for each step.
// The individual Fq operations (fp.Eval, fp.Mul, fp.AssertIsEqual) create
// deferred checks that are batched and verified by the emulated field's own
// Schwartz-Zippel mechanism.
type E12DeferredChecker struct {
	api   frontend.API
	fp    *curveF
	steps []*e12PolyStep
}

// NewE12DeferredChecker creates a new deferred checker.
func NewE12DeferredChecker(api frontend.API, fp *curveF) *E12DeferredChecker {
	return &E12DeferredChecker{api: api, fp: fp}
}

// AddMulCheck adds a polynomial identity check: ∏ factors(w) = R(w) + Q(w)·P12(w).
// Returns R, the reduced product modulo P12(w), as an E12 element.
func (dc *E12DeferredChecker) AddMulCheck(factors []*E12, sparsity []int) *E12 {
	if len(factors) != len(sparsity) {
		panic("factors and sparsity length mismatch")
	}
	if len(factors) < 2 {
		panic("need at least 2 factors")
	}

	// Product degree = 11*n, quotient degree = 11*n - 12
	totalDeg := len(factors) * 11
	qDeg := totalDeg - 12
	if qDeg < 0 {
		qDeg = 0
	}
	nbQCoeffs := qDeg + 1

	// Hint inputs: all 12 coefficients per factor
	var hintInputs []*baseEl
	for _, f := range factors {
		hintInputs = append(hintInputs, &f.A0, &f.A1, &f.A2, &f.A3, &f.A4, &f.A5,
			&f.A6, &f.A7, &f.A8, &f.A9, &f.A10, &f.A11)
	}

	// Outputs: R(12) + Q(nbQCoeffs)
	nbOutputs := 12 + nbQCoeffs

	res, err := dc.fp.NewHint(e12PolyMulDivHint, nbOutputs, hintInputs...)
	if err != nil {
		panic(err)
	}

	r := &E12{
		A0: *res[0], A1: *res[1], A2: *res[2], A3: *res[3],
		A4: *res[4], A5: *res[5], A6: *res[6], A7: *res[7],
		A8: *res[8], A9: *res[9], A10: *res[10], A11: *res[11],
	}
	q := make([]*baseEl, nbQCoeffs)
	for i := 0; i < nbQCoeffs; i++ {
		q[i] = res[12+i]
	}

	dc.steps = append(dc.steps, &e12PolyStep{
		factors:  factors,
		sparsity: sparsity,
		r:        r,
		q:        q,
	})

	return r
}

// Finalize verifies all accumulated polynomial identity checks.
//
// For each step, we check the polynomial identity ∏ F_i(x) = R(x) + Q(x)·P12(x)
// at a random point x ∈ Fq, obtained by converting a multicommit challenge.
//
// All Fq arithmetic (fp.Eval, fp.Mul, fp.AssertIsEqual) creates deferred checks
// that are later verified by the emulated field's own batched Schwartz-Zippel.
func (dc *E12DeferredChecker) Finalize() {
	if len(dc.steps) == 0 {
		return
	}

	// Collect all variables to commit to (binds factors, R, Q values)
	var toCommit []frontend.Variable
	for _, step := range dc.steps {
		for _, f := range step.factors {
			for _, c := range e12Coefficients(f) {
				toCommit = append(toCommit, c.Limbs...)
			}
		}
		for _, c := range e12Coefficients(step.r) {
			toCommit = append(toCommit, c.Limbs...)
		}
		for _, qi := range step.q {
			toCommit = append(toCommit, qi.Limbs...)
		}
	}

	multicommit.WithCommitment(dc.api, func(api frontend.API, commitment frontend.Variable) error {
		// Convert native commitment to Fq element
		x, err := dc.fp.NewHintWithNativeInput(nativeToFqHint, 1, commitment)
		if err != nil {
			return fmt.Errorf("native to Fq: %w", err)
		}
		xFq := x[0]

		// Reconstruction check: verify the Fq element matches the native commitment.
		// The native commitment c ∈ Fr. Since p > r for BN254, c < p, so c is a
		// valid Fq element. We check that Σ limbs[i] * 2^{64i} ≡ c (mod r).
		nbLimbs := len(xFq.Limbs)
		reconstructed := xFq.Limbs[0]
		base := new(big.Int).SetUint64(1)
		for i := 1; i < nbLimbs; i++ {
			base.Lsh(base, 64)
			reconstructed = api.Add(reconstructed, api.Mul(xFq.Limbs[i], base))
		}
		api.AssertIsEqual(reconstructed, commitment)

		// Compute powers of x: x^1, x^2, ..., x^maxDeg
		maxDeg := 12 // at least for P12 evaluation
		for _, step := range dc.steps {
			d := len(step.factors) * 11
			if d > maxDeg {
				maxDeg = d
			}
			qDeg := len(step.q) - 1
			if qDeg > maxDeg {
				maxDeg = qDeg
			}
		}

		xPow := make([]*baseEl, maxDeg+1)
		xPow[0] = dc.fp.One()
		xPow[1] = xFq
		for i := 2; i <= maxDeg; i++ {
			xPow[i] = dc.fp.Mul(xPow[i-1], xFq)
		}

		// Evaluate P12(x) = x^12 - 18*x^6 + 82
		eighteen := big.NewInt(18)
		eightyTwo := big.NewInt(82)
		p12x := dc.fp.Sub(xPow[12], dc.fp.MulConst(xPow[6], eighteen))
		p12x = dc.fp.Add(p12x, dc.fp.NewElement(eightyTwo))

		// Verify each step
		for _, step := range dc.steps {
			dc.verifyStep(step, xPow, p12x)
		}

		return nil
	}, toCommit...)
}

// verifyStep checks one polynomial identity at the random point x.
func (dc *E12DeferredChecker) verifyStep(step *e12PolyStep, xPow []*baseEl, p12x *baseEl) {
	// Evaluate each factor at x
	product := dc.evalE12AtX(step.factors[0], step.sparsity[0], xPow)
	for i := 1; i < len(step.factors); i++ {
		fi := dc.evalE12AtX(step.factors[i], step.sparsity[i], xPow)
		product = dc.fp.Mul(product, fi)
	}

	// Evaluate R(x)
	rEval := dc.evalE12AtX(step.r, SparsityFull, xPow)

	// Evaluate Q(x)
	qEval := dc.evalFqPolyAtX(step.q, xPow)

	// RHS = R(x) + Q(x) · P12(x)
	qp12 := dc.fp.Mul(qEval, p12x)
	rhs := dc.fp.Add(rEval, qp12)

	// Assert product == RHS
	dc.fp.AssertIsEqual(product, rhs)
}

// evalE12AtX evaluates an E12 polynomial at x using fp.Eval.
//
// For a full E12: result = a0 + a1*x + a2*x^2 + ... + a11*x^11
// For sparse variants, only non-zero coefficients are included.
func (dc *E12DeferredChecker) evalE12AtX(e *E12, sparsity int, xPow []*baseEl) *baseEl {
	if sparsity == SparsityOne {
		return dc.fp.One()
	}

	coeffs := e12Coefficients(e)

	var indices []int
	switch sparsity {
	case SparsitySparse5:
		indices = []int{0, 1, 3, 7, 9}
	case SparsitySparse10:
		indices = []int{0, 1, 2, 3, 4, 6, 7, 8, 9, 10}
	default:
		indices = []int{0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11}
	}

	// Build fp.Eval terms: each term is [a_j, x^j] (or just [a_j] for j=0)
	terms := make([][]*baseEl, len(indices))
	coefs := make([]int, len(indices))
	for i, j := range indices {
		if j == 0 {
			terms[i] = []*baseEl{coeffs[j]}
		} else {
			terms[i] = []*baseEl{coeffs[j], xPow[j]}
		}
		coefs[i] = 1
	}

	return dc.fp.Eval(terms, coefs)
}

// evalFqPolyAtX evaluates a polynomial with Fq coefficients at x using fp.Eval.
//
//	P(x) = q[0] + q[1]*x + q[2]*x^2 + ...
func (dc *E12DeferredChecker) evalFqPolyAtX(q []*baseEl, xPow []*baseEl) *baseEl {
	if len(q) == 0 {
		return dc.fp.Zero()
	}

	terms := make([][]*baseEl, len(q))
	coefs := make([]int, len(q))
	for j := range q {
		if j == 0 {
			terms[j] = []*baseEl{q[j]}
		} else {
			terms[j] = []*baseEl{q[j], xPow[j]}
		}
		coefs[j] = 1
	}

	return dc.fp.Eval(terms, coefs)
}

// e12Coefficients returns the 12 coefficient pointers of an E12 element.
func e12Coefficients(e *E12) [12]*baseEl {
	return [12]*baseEl{&e.A0, &e.A1, &e.A2, &e.A3, &e.A4, &e.A5,
		&e.A6, &e.A7, &e.A8, &e.A9, &e.A10, &e.A11}
}

// nativeToFqHint converts a native field element to an Fq element.
// Input: 1 native value (the multicommit challenge)
// Output: 1 Fq element (same value, since p > r for BN254)
func nativeToFqHint(nativeMod *big.Int, nativeInputs, nativeOutputs []*big.Int) error {
	return emulated.UnwrapHintWithNativeInput(nativeInputs, nativeOutputs,
		func(mod *big.Int, nativeIns, emuOuts []*big.Int) error {
			if len(nativeIns) != 1 {
				return fmt.Errorf("expected 1 native input, got %d", len(nativeIns))
			}
			if len(emuOuts) != 1 {
				return fmt.Errorf("expected 1 emulated output, got %d", len(emuOuts))
			}
			// The native value is in [0, r). Since p > r for BN254, it's valid in Fq.
			emuOuts[0].Set(nativeIns[0])
			return nil
		})
}

// e12PolyMulDivHint computes the polynomial product ∏ factors(w) in Fq[w],
// then performs Euclidean division by P12(w) = w^12 - 18w^6 + 82.
//
// Inputs: factor coefficients (12 Fq values per factor)
// Outputs: R (12 Fq) + Q (variable Fq)
func e12PolyMulDivHint(nativeMod *big.Int, nativeInputs, nativeOutputs []*big.Int) error {
	return emulated.UnwrapHint(nativeInputs, nativeOutputs,
		func(mod *big.Int, inputs, outputs []*big.Int) error {
			nbFactors := len(inputs) / 12
			if nbFactors*12 != len(inputs) {
				return fmt.Errorf("inputs length %d not divisible by 12", len(inputs))
			}

			// Read factors
			factors := make([][12]*big.Int, nbFactors)
			for i := 0; i < nbFactors; i++ {
				for j := 0; j < 12; j++ {
					factors[i][j] = new(big.Int).Set(inputs[i*12+j])
				}
			}

			// Compute product in Fq[w]
			product := make([]*big.Int, 12)
			for j := 0; j < 12; j++ {
				product[j] = new(big.Int).Set(factors[0][j])
			}
			for i := 1; i < nbFactors; i++ {
				product = polyMulFq(product, factors[i][:], mod)
			}

			// Euclidean division by P12 over Fq
			quotient, remainder := polyDivByP12(product, mod)

			// Output R (12 coefficients)
			for j := 0; j < 12; j++ {
				outputs[j].Set(remainder[j])
			}

			// Output Q
			nbQCoeffs := len(outputs) - 12
			for j := 0; j < nbQCoeffs; j++ {
				if j < len(quotient) {
					outputs[12+j].Set(quotient[j])
				} else {
					outputs[12+j].SetInt64(0)
				}
			}

			return nil
		})
}

// polyMulFq multiplies two polynomials over Fq.
func polyMulFq(a, b []*big.Int, mod *big.Int) []*big.Int {
	if len(a) == 0 || len(b) == 0 {
		return []*big.Int{new(big.Int)}
	}
	result := make([]*big.Int, len(a)+len(b)-1)
	for i := range result {
		result[i] = new(big.Int)
	}
	tmp := new(big.Int)
	for i, ai := range a {
		for j, bj := range b {
			tmp.Mul(ai, bj)
			result[i+j].Add(result[i+j], tmp)
			result[i+j].Mod(result[i+j], mod)
		}
	}
	return result
}

// polyDivByP12 performs Euclidean division of poly by P12(w) = w^12 - 18w^6 + 82 over Fq.
func polyDivByP12(poly []*big.Int, p *big.Int) ([]*big.Int, []*big.Int) {
	n := len(poly)
	if n <= 12 {
		rem := make([]*big.Int, 12)
		for i := 0; i < 12; i++ {
			if i < n {
				rem[i] = new(big.Int).Mod(poly[i], p)
			} else {
				rem[i] = new(big.Int)
			}
		}
		return []*big.Int{}, rem
	}

	work := make([]*big.Int, n)
	for i := range poly {
		work[i] = new(big.Int).Set(poly[i])
	}

	qLen := n - 12
	quotient := make([]*big.Int, qLen)
	eighteen := big.NewInt(18)
	eightyTwo := big.NewInt(82)
	tmp := new(big.Int)

	for d := n - 1; d >= 12; d-- {
		qi := d - 12
		quotient[qi] = new(big.Int).Mod(work[d], p)
		work[d].SetInt64(0)

		// P12 = w^12 - 18w^6 + 82, leading coeff = 1 (monic)
		// Subtract quotient[qi] * (-18w^6 + 82) from lower terms
		tmp.Mul(eighteen, quotient[qi])
		work[d-6].Add(work[d-6], tmp)
		work[d-6].Mod(work[d-6], p)

		tmp.Mul(eightyTwo, quotient[qi])
		work[d-12].Sub(work[d-12], tmp)
		work[d-12].Mod(work[d-12], p)
	}

	remainder := make([]*big.Int, 12)
	for i := 0; i < 12; i++ {
		remainder[i] = new(big.Int).Mod(work[i], p)
	}

	return quotient, remainder
}
