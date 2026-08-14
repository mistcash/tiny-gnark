package emulated

// Soundness test for the RLC aggregation of deferred emulated-field checks.
//
// The aggregated check
//
//	Σ_i z^i (a_i(X)b_i(X) - r_i(X)) = p(X)·K(X) + (2^w - X)·C(X)
//
// is only binding if K is tied to the per-check quotients k_i. It is not: K is
// a hinted, un-range-checked prover message. For any claimed remainders there
// is a constant K = Φ(2^w)/p mod q and a matching C that satisfy the identity,
// so the check accepts arbitrary products. See EmulatedFieldsRLC.md, Theorem 1.
//
// The test runs on M127, where the per-check quotient range check is genuinely
// binding, so the same forgery is rejected by the pre-RLC verifier. A failure
// here is therefore attributable to the aggregation alone.
//
// This test is expected to FAIL while the quotient accumulator is in use. It is
// the gate any future aggregation work should be held to.

import (
	"math/big"
	"sync"
	"testing"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/constraint/solver"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/r1cs"
	limbs "github.com/consensys/gnark/std/internal/limbcomposition"
)

// M127 emulates the Mersenne prime 2^127-1: an emulated modulus much smaller
// than the BN254 native modulus.
type M127 struct{}

func (M127) NbLimbs() uint     { return 2 }
func (M127) BitsPerLimb() uint { return 64 }
func (M127) IsPrime() bool     { return true }
func (M127) Modulus() *big.Int {
	m := new(big.Int).Lsh(big.NewInt(1), 127)
	return m.Sub(m, big.NewInt(1))
}

type rlcSoundnessCircuit[T FieldParams] struct {
	A, B Element[T]
	R    Element[T]
}

func (c *rlcSoundnessCircuit[T]) Define(api frontend.API) error {
	f, err := NewField[T](api)
	if err != nil {
		return err
	}
	f.AssertIsEqual(f.Mul(&c.A, &c.B), &c.R)
	return nil
}

type recordedCheck struct {
	a, b, r []*big.Int
}

var (
	forgeMu      sync.Mutex
	forgeRecords []recordedCheck
)

func copyLimbs(in []*big.Int) []*big.Int {
	out := make([]*big.Int, len(in))
	for i := range in {
		out[i] = new(big.Int).Set(in[i])
	}
	return out
}

// rlcForgeMulHint runs the honest hint, then overwrites the remainder with a
// wrong value. It leaves k and c untouched, so the *individual* identity is
// broken; only the aggregate can rescue it. It records (a,b,r) as seen by the
// circuit so that the RLC hint override can build a matching K and C.
func rlcForgeMulHint(field *big.Int, inputs, outputs []*big.Int) error {
	if err := mulHint(field, inputs, outputs); err != nil {
		return err
	}
	nbBits := int(inputs[0].Int64())
	nbLimbs := int(inputs[1].Int64())
	nbALen := int(inputs[2].Int64())
	nbQuoLen := int(inputs[3].Int64())
	nbBLen := len(inputs) - 4 - nbLimbs - nbALen
	ptr := 4 + nbLimbs
	alimbs := inputs[ptr : ptr+nbALen]
	blimbs := inputs[ptr+nbALen : ptr+nbALen+nbBLen]
	remLimbs := outputs[nbQuoLen : nbQuoLen+nbLimbs]

	isCheckZero := nbBLen == 1 && blimbs[0].Cmp(big.NewInt(1)) == 0
	rec := recordedCheck{a: copyLimbs(alimbs), b: copyLimbs(blimbs)}
	if isCheckZero {
		// the circuit hardwires r = 0 (element on zero limbs) for checkZero
		rec.r = nil
	} else {
		// corrupt the remainder: r' = (a*b mod p) + 1
		v := new(big.Int)
		if err := limbs.Recompose(remLimbs, uint(nbBits), v); err != nil {
			return err
		}
		v.Add(v, big.NewInt(1))
		if err := limbs.Decompose(v, uint(nbBits), remLimbs); err != nil {
			return err
		}
		rec.r = copyLimbs(remLimbs)
	}
	forgeMu.Lock()
	forgeRecords = append(forgeRecords, rec)
	forgeMu.Unlock()
	return nil
}

// rlcForgeRLCHint replaces the honest accumulator with K, C chosen to satisfy
//
//	Σ_i z^i (a_i(X)b_i(X) - r_i(X)) = p(X)·K(X) + (2^w - X)·C(X)
//
// for whatever remainders the prover claimed. K is taken to be the constant
// F(2^w)/p mod q; C is the exact quotient of the residual by (2^w - X).
func makeRLCForgeHint(p *big.Int, nbBits uint) solver.Hint {
	return func(field *big.Int, inputs, outputs []*big.Int) error {
		nbChecks := int(inputs[0].Int64())
		maxKLen := int(inputs[1].Int64())
		maxCLen := int(inputs[2].Int64())
		z := new(big.Int).Mod(new(big.Int).Set(inputs[3]), field)

		forgeMu.Lock()
		records := forgeRecords
		forgeMu.Unlock()
		if len(records) != nbChecks {
			return errNbChecksMismatch
		}

		// F(X) = Σ z^i (a_i(X) b_i(X) - r_i(X))  over F_q
		F := make([]*big.Int, 64)
		for i := range F {
			F[i] = new(big.Int)
		}
		zPow := big.NewInt(1)
		for _, rec := range records {
			for i, ai := range rec.a {
				for j, bj := range rec.b {
					F[i+j].Add(F[i+j], new(big.Int).Mul(new(big.Int).Mul(ai, bj), zPow))
				}
			}
			for i, ri := range rec.r {
				F[i].Sub(F[i], new(big.Int).Mul(ri, zPow))
			}
			zPow = new(big.Int).Mod(new(big.Int).Mul(zPow, z), field)
		}
		for i := range F {
			F[i].Mod(F[i], field)
		}

		// K = F(2^w) / p  (a constant polynomial)
		shift := new(big.Int).Lsh(big.NewInt(1), nbBits)
		fAt := new(big.Int)
		pow := big.NewInt(1)
		for i := range F {
			fAt.Add(fAt, new(big.Int).Mul(F[i], pow))
			pow = new(big.Int).Mod(new(big.Int).Mul(pow, shift), field)
		}
		fAt.Mod(fAt, field)
		K := new(big.Int).Mul(fAt, new(big.Int).ModInverse(p, field))
		K.Mod(K, field)

		// residual = F(X) - p(X)*K, then divide by (2^w - X)
		plimbs := make([]*big.Int, (p.BitLen()+int(nbBits)-1)/int(nbBits))
		for i := range plimbs {
			plimbs[i] = new(big.Int)
		}
		if err := limbs.Decompose(p, nbBits, plimbs); err != nil {
			return err
		}
		for i, pi := range plimbs {
			F[i].Sub(F[i], new(big.Int).Mul(pi, K))
			F[i].Mod(F[i], field)
		}
		shiftInv := new(big.Int).ModInverse(shift, field)
		C := make([]*big.Int, len(F))
		carry := new(big.Int)
		for i := range C {
			acc := new(big.Int).Add(F[i], carry)
			acc.Mul(acc, shiftInv)
			acc.Mod(acc, field)
			C[i] = acc
			carry = acc
		}
		for i := maxCLen; i < len(C); i++ {
			if C[i].Sign() != 0 {
				return errCarryOverflow
			}
		}
		for i := range outputs {
			outputs[i].SetInt64(0)
		}
		outputs[0].Set(K)
		for i := 0; i < maxCLen && i < len(C); i++ {
			outputs[maxKLen+i].Set(C[i])
		}
		return nil
	}
}

type forgeErr string

func (e forgeErr) Error() string { return string(e) }

const (
	errNbChecksMismatch = forgeErr("recorded checks do not match nbChecks (solver reordered hints)")
	errCarryOverflow    = forgeErr("forged carry does not fit in the available limbs")
)

func TestForgeRLCAggregation(t *testing.T) {
	q := ecc.BN254.ScalarField()
	var params M127
	p := params.Modulus()

	a := new(big.Int).Rsh(p, 3)
	a.Add(a, big.NewInt(12345))
	b := new(big.Int).Rsh(p, 5)
	b.Add(b, big.NewInt(6789))
	honest := new(big.Int).Mod(new(big.Int).Mul(a, b), p)
	wrong := new(big.Int).Mod(new(big.Int).Add(honest, big.NewInt(1)), p)

	ccs, err := frontend.Compile(q, r1cs.NewBuilder, &rlcSoundnessCircuit[M127]{})
	if err != nil {
		t.Fatalf("compile: %v", err)
	}
	solve := func(r *big.Int, opts ...solver.Option) error {
		forgeMu.Lock()
		forgeRecords = nil
		forgeMu.Unlock()
		w, err := frontend.NewWitness(&rlcSoundnessCircuit[M127]{
			A: ValueOf[M127](a), B: ValueOf[M127](b), R: ValueOf[M127](r)}, q)
		if err != nil {
			return err
		}
		_, err = ccs.Solve(w, append(opts, solver.WithNbTasks(1))...)
		return err
	}

	if err := solve(honest); err != nil {
		t.Fatalf("honest must solve: %v", err)
	}
	if err := solve(wrong); err == nil {
		t.Fatal("wrong result must not solve under honest hints")
	}

	err = solve(wrong,
		solver.OverrideHint(solver.GetHintID(mulHint), rlcForgeMulHint),
		solver.OverrideHint(solver.GetHintID(deferredChecksRLCHint), makeRLCForgeHint(p, params.BitsPerLimb())))
	if err == nil {
		t.Fatal("FORGERY ACCEPTED via RLC aggregation on M127 (baseline rejects the same class of forgery)")
	}
	t.Logf("RLC forgery rejected: %v", err)
}
