package sw_bn254

import (
	"errors"
	"fmt"
	"math/big"

	"github.com/consensys/gnark/std/algebra/emulated/fields_bn254"
)

// PairingCheckDeferred calculates the reduced pairing for a set of points and
// asserts if the result is one, using deferred polynomial identity checks as
// described in the Probabilistic Pairing Proofs paper.
//
// Instead of performing E12 multiplications eagerly (each creating 12 deferred
// mulCheck instances), this method defers the entire polynomial identity check
// for each Miller loop step. Each step's identity
//
//	F²(w)·L₁(w)·L₂(w)·... = R(w) + Q(w)·P12(w)
//
// is verified via Schwartz-Zippel at a random challenge point, significantly
// reducing the number of native constraints.
//
// This function checks that the Qᵢ are in the correct subgroup, but does not
// check Pᵢ. See AssertIsOnG1.
func (pr *Pairing) PairingCheckDeferred(P []*G1Affine, Q []*G2Affine) error {
	nP := len(P)
	nQ := len(Q)
	if nP == 0 || nP != nQ {
		return errors.New("invalid inputs sizes")
	}

	// Hint the non-residue witness (same as regular PairingCheck)
	inputs := make([]*baseEl, 0, 2*nP+4*nQ)
	for _, p := range P {
		inputs = append(inputs, &p.X, &p.Y)
	}
	for _, q := range Q {
		inputs = append(inputs, &q.P.X.A0, &q.P.X.A1, &q.P.Y.A0, &q.P.Y.A1)
	}
	hint, err := pr.curveF.NewHint(pairingCheckHint, 18, inputs...)
	if err != nil {
		panic(err)
	}
	residueWitnessInv := pr.Ext12.FromTower([12]*baseEl{hint[0], hint[1], hint[2], hint[3], hint[4], hint[5], hint[6], hint[7], hint[8], hint[9], hint[10], hint[11]})

	nine := big.NewInt(9)
	cubicNonResiduePower := GTEl{
		A0:  *pr.curveF.Sub(hint[12], pr.curveF.MulConst(hint[13], nine)),
		A1:  *pr.curveF.Zero(),
		A2:  *pr.curveF.Sub(hint[14], pr.curveF.MulConst(hint[15], nine)),
		A3:  *pr.curveF.Zero(),
		A4:  *pr.curveF.Sub(hint[16], pr.curveF.MulConst(hint[17], nine)),
		A5:  *pr.curveF.Zero(),
		A6:  *hint[13],
		A7:  *pr.curveF.Zero(),
		A8:  *hint[15],
		A9:  *pr.curveF.Zero(),
		A10: *hint[17],
		A11: *pr.curveF.Zero(),
	}

	// Precompute lines for each Q
	lines := make([]lineEvaluations, nQ)
	for i := range Q {
		if Q[i].Lines == nil {
			Qlines := pr.computeLines(&Q[i].P)
			Q[i].Lines = &Qlines
		}
		lines[i] = *Q[i].Lines
	}

	// Create deferred checker
	dc := fields_bn254.NewE12DeferredChecker(pr.api, pr.curveF)

	// Run the Miller loop using deferred polynomial checks
	res := pr.millerLoopLinesDeferred(dc, P, lines, residueWitnessInv)

	// Final check: res * cubicNonResiduePower * residueWitnessInv^{q³-q²+q} == 1
	//
	// Instead of doing these as regular E12 multiplications, we can add them
	// as deferred checks too. However, the Frobenius operations and the ExpByU
	// are complex. For now, we do the final check using regular operations and
	// defer only the Miller loop body.

	t2 := pr.Ext12.Mul(&cubicNonResiduePower, res)

	t1 := pr.FrobeniusCube(residueWitnessInv)
	t0 := pr.FrobeniusSquare(residueWitnessInv)
	t1 = pr.Ext12.DivUnchecked(t1, t0)
	t0 = pr.Frobenius(residueWitnessInv)
	t1 = pr.Ext12.Mul(t1, t0)

	t2 = pr.Ext12.Mul(t2, t1)

	pr.AssertIsEqual(t2, pr.Ext12.One())

	// Finalize all deferred polynomial checks
	dc.Finalize()

	return nil
}

// millerLoopLinesDeferred computes the multi-Miller loop using deferred
// polynomial identity checks instead of direct E12 multiplications.
//
// For each iteration of the Miller loop, instead of computing:
//
//	res = res² · ∏ lines
//
// using E12 Square and MulBy01379 (which each create 12 mulCheck instances),
// we collect all factors and create a SINGLE polynomial identity check:
//
//	res² · ∏ lines = R + Q · P12  in Fq[w]
//
// The hint computes R and Q, and the deferred checker verifies the identity.
func (pr *Pairing) millerLoopLinesDeferred(dc *fields_bn254.E12DeferredChecker, P []*G1Affine, lines []lineEvaluations, init *GTEl) *GTEl {
	n := len(P)

	// Precomputations
	yInv := make([]*baseEl, n)
	xNegOverY := make([]*baseEl, n)

	for k := 0; k < n; k++ {
		isYZero := pr.curveF.IsZero(&P[k].Y)
		y := pr.curveF.Select(isYZero, pr.curveF.One(), &P[k].Y)
		yInv[k] = pr.curveF.Select(isYZero, pr.curveF.Zero(), pr.curveF.Inverse(y))
		xNegOverY[k] = pr.curveF.Mul(&P[k].X, yInv[k])
		xNegOverY[k] = pr.curveF.Neg(xNegOverY[k])
	}

	// Start with init (residueWitnessInv) as accumulator
	res := init
	initInv := pr.Ext12.Inverse(init)

	// First iteration: i = len(loopCounter)-2
	j := len(loopCounter) - 2

	// Build the first line evaluations as sparse E12 elements
	// For the first iteration with first=false (we have init), we just
	// do a regular step.

	for i := j; i >= 0; i-- {
		// For each step, we build the list of factors for the polynomial identity:
		//   res(w)² · (init or initInv if non-zero bit) · ∏ line_evals = R(w) mod P12(w)
		//
		// Factors: [res, res] for squaring, plus lines per pair, plus init/initInv for ±1 bits.

		var factors []*GTEl
		var sparsity []int

		// First factor: res (for squaring, we need res twice)
		factors = append(factors, res, res)
		sparsity = append(sparsity, fields_bn254.SparsityFull, fields_bn254.SparsityFull)

		switch loopCounter[i] {
		case 0:
			// Zero bit: just squaring + line evals
			for k := 0; k < n; k++ {
				lineE12 := pr.makeLineE12(lines[k][0][i], xNegOverY[k], yInv[k])
				factors = append(factors, lineE12)
				sparsity = append(sparsity, fields_bn254.SparsitySparse5)
			}
		case 1:
			// Positive bit: squaring + init + double line evals per pair
			factors = append(factors, init)
			sparsity = append(sparsity, fields_bn254.SparsityFull)
			for k := 0; k < n; k++ {
				// Doubling line
				lineD := pr.makeLineE12(lines[k][0][i], xNegOverY[k], yInv[k])
				factors = append(factors, lineD)
				sparsity = append(sparsity, fields_bn254.SparsitySparse5)
				// Addition line
				lineA := pr.makeLineE12(lines[k][1][i], xNegOverY[k], yInv[k])
				factors = append(factors, lineA)
				sparsity = append(sparsity, fields_bn254.SparsitySparse5)
			}
		case -1:
			// Negative bit: squaring + initInv + double line evals per pair
			factors = append(factors, initInv)
			sparsity = append(sparsity, fields_bn254.SparsityFull)
			for k := 0; k < n; k++ {
				lineD := pr.makeLineE12(lines[k][0][i], xNegOverY[k], yInv[k])
				factors = append(factors, lineD)
				sparsity = append(sparsity, fields_bn254.SparsitySparse5)
				lineA := pr.makeLineE12(lines[k][1][i], xNegOverY[k], yInv[k])
				factors = append(factors, lineA)
				sparsity = append(sparsity, fields_bn254.SparsitySparse5)
			}
		default:
			panic(fmt.Sprintf("invalid loop counter value %d", loopCounter[i]))
		}

		// Use deferred checker to verify the polynomial identity and get the result
		res = dc.AddMulCheck(factors, sparsity)
	}

	// Frobenius correction lines (index 65)
	for k := 0; k < n; k++ {
		lineD := pr.makeLineE12(lines[k][0][65], xNegOverY[k], yInv[k])
		lineA := pr.makeLineE12(lines[k][1][65], xNegOverY[k], yInv[k])

		// res = res · lineD · lineA
		result := dc.AddMulCheck([]*GTEl{res, lineD, lineA},
			[]int{fields_bn254.SparsityFull, fields_bn254.SparsitySparse5, fields_bn254.SparsitySparse5})
		res = result
	}

	return res
}

// makeLineE12 constructs a sparse E12 element from a line evaluation.
// A line evaluation has the form:
//
//	A0  = 1
//	A1  = c3.A0 - 9·c3.A1
//	A3  = c4.A0 - 9·c4.A1
//	A7  = c3.A1
//	A9  = c4.A1
//	(all other coefficients = 0)
//
// where c3 = line.R0 * xNegOverY, c4 = line.R1 * yInv.
func (pr *Pairing) makeLineE12(line *lineEvaluation, xNegOverY, yInv *baseEl) *GTEl {
	c3 := pr.Ext2.MulByElement(&line.R0, xNegOverY)
	c4 := pr.Ext2.MulByElement(&line.R1, yInv)
	nine := big.NewInt(9)
	return &GTEl{
		A0:  *pr.curveF.One(),
		A1:  *pr.curveF.Sub(&c3.A0, pr.curveF.MulConst(&c3.A1, nine)),
		A2:  *pr.curveF.Zero(),
		A3:  *pr.curveF.Sub(&c4.A0, pr.curveF.MulConst(&c4.A1, nine)),
		A4:  *pr.curveF.Zero(),
		A5:  *pr.curveF.Zero(),
		A6:  *pr.curveF.Zero(),
		A7:  c3.A1,
		A8:  *pr.curveF.Zero(),
		A9:  c4.A1,
		A10: *pr.curveF.Zero(),
		A11: *pr.curveF.Zero(),
	}
}
