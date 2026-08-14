package emulated

import (
	"math/big"
	"testing"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/constraint/solver"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/test"
)

// This file demonstrates that the RLC aggregation of the deferred
// multiplication checks is unsound: the aggregated quotient K and carry C are
// prover-supplied values that are never range checked, and the pair
// (p(X), 2^t-X) generates the unit ideal of F_q[X]. Hence for *any* left-hand
// side the prover can solve
//
//	LHS(X) = p(X) K(X) + (2^t - X) C(X)
//
// and the check accepts. The per-check quotients k_i remain range checked but
// are dangling: they only feed a hint, and hints are not constraints.

// forgedMulCircuit multiplies A*B and asserts the result equals Expected. The
// witness sets Expected to A*B+1, so a sound system must reject it.
type forgedMulCircuit struct {
	A, B     Element[BN254Fp]
	Expected Element[BN254Fp]
}

func (c *forgedMulCircuit) Define(api frontend.API) error {
	f, err := NewField[BN254Fp](api)
	if err != nil {
		return err
	}
	f.AssertIsEqual(f.Mul(&c.A, &c.B), &c.Expected)
	return nil
}

// mulHintCallCount lets the forging hint corrupt only the first mulHint
// invocation (the A*B product) and leave the AssertIsEqual one honest.
var mulHintCallCount int

// forgeMulHint returns the honest witness except that the first call has its
// remainder incremented by one, i.e. it claims A*B+1 as the product.
func forgeMulHint(mod *big.Int, inputs, outputs []*big.Int) error {
	if err := mulHint(mod, inputs, outputs); err != nil {
		return err
	}
	mulHintCallCount++
	if mulHintCallCount != 1 {
		return nil
	}
	nbQuoLimbs := int(inputs[3].Int64())
	// remainder limbs follow the quotient limbs; bump the least significant one
	outputs[nbQuoLimbs].Add(outputs[nbQuoLimbs], one)
	outputs[nbQuoLimbs].Mod(outputs[nbQuoLimbs], mod)
	return nil
}

// forgeDeferredChecksRLCHint patches the honest accumulators so that the
// aggregated identity still holds after the remainder of check 0 was increased
// by one. Corrupting r_0 by +1 changes the aggregated left-hand side by -1
// (check 0 carries weight z^0 = 1), so we need a correction satisfying
//
//	p(X) dK(X) + (2^t - X) dC(X) = -1.
//
// Taking dK to be the constant -p(2^t)^-1 makes the numerator vanish at X=2^t,
// so dC is obtained by exact division. Note this needs no knowledge of A, B or
// r whatsoever - only the public modulus - which is precisely the problem.
func forgeDeferredChecksRLCHint(mod *big.Int, inputs, outputs []*big.Int) error {
	if err := deferredChecksRLCHint(mod, inputs, outputs); err != nil {
		return err
	}
	maxKLen := int(inputs[1].Int64())

	var fp BN254Fp
	nbBits := fp.BitsPerLimb()
	nbLimbs := int(fp.NbLimbs())
	pInt := fp.Modulus()

	// p(X) coefficients are the modulus limbs
	pPoly := make([]*big.Int, nbLimbs)
	tmp := new(big.Int).Set(pInt)
	mask := new(big.Int).Lsh(one, nbBits)
	mask.Sub(mask, one)
	for i := range pPoly {
		pPoly[i] = new(big.Int).And(tmp, mask)
		tmp.Rsh(tmp, nbBits)
	}

	// dK = -p(2^t)^-1 = -p^-1 mod q, a constant polynomial
	dK := new(big.Int).ModInverse(new(big.Int).Mod(pInt, mod), mod)
	if dK == nil {
		return nil
	}
	dK.Neg(dK).Mod(dK, mod)

	// N(X) = -1 - dK*p(X), which vanishes at X = 2^t by construction
	nPoly := make([]*big.Int, nbLimbs)
	for i := range nPoly {
		nPoly[i] = new(big.Int).Mul(dK, pPoly[i])
		nPoly[i].Neg(nPoly[i])
		if i == 0 {
			nPoly[i].Sub(nPoly[i], one)
		}
		nPoly[i].Mod(nPoly[i], mod)
	}

	// divide N(X) by (2^t - X): dC_{n-2} = -N_{n-1}, dC_{j-1} = 2^t*dC_j - N_j
	twoT := new(big.Int).Lsh(one, nbBits)
	dC := make([]*big.Int, nbLimbs-1)
	dC[nbLimbs-2] = new(big.Int).Neg(nPoly[nbLimbs-1])
	dC[nbLimbs-2].Mod(dC[nbLimbs-2], mod)
	for j := nbLimbs - 2; j >= 1; j-- {
		dC[j-1] = new(big.Int).Mul(twoT, dC[j])
		dC[j-1].Sub(dC[j-1], nPoly[j])
		dC[j-1].Mod(dC[j-1], mod)
	}

	outputs[0].Add(outputs[0], dK)
	outputs[0].Mod(outputs[0], mod)
	for j := range dC {
		outputs[maxKLen+j].Add(outputs[maxKLen+j], dC[j])
		outputs[maxKLen+j].Mod(outputs[maxKLen+j], mod)
	}
	return nil
}

func forgedMulWitness() *forgedMulCircuit {
	a, b := big.NewInt(3), big.NewInt(5)
	wrong := new(big.Int).Mul(a, b)
	wrong.Add(wrong, one) // claim 3*5 == 16
	return &forgedMulCircuit{
		A:        ValueOf[BN254Fp](a),
		B:        ValueOf[BN254Fp](b),
		Expected: ValueOf[BN254Fp](wrong),
	}
}

// TestRLCWrongProductRejected is the control: corrupting only the product and
// leaving the accumulators honest must be caught. It confirms the deferred
// check is actually wired up and that TestRLCForgedProduct below succeeds
// because of the accumulator forgery rather than a missing constraint.
func TestRLCWrongProductRejected(t *testing.T) {
	mulHintCallCount = 0
	err := test.IsSolved(&forgedMulCircuit{}, forgedMulWitness(), ecc.BN254.ScalarField(),
		test.WithReplacementHint(solver.GetHintID(mulHint), forgeMulHint),
	)
	if err == nil {
		t.Fatal("wrong product accepted with honest accumulators")
	}
}

// TestRLCForgedProduct proves the RLC deferred check accepts a false
// multiplication. It fails while the aggregation is unsound and passes once
// the aggregated quotient is properly bound.
func TestRLCForgedProduct(t *testing.T) {
	mulHintCallCount = 0
	err := test.IsSolved(&forgedMulCircuit{}, forgedMulWitness(), ecc.BN254.ScalarField(),
		test.WithReplacementHint(solver.GetHintID(mulHint), forgeMulHint),
		test.WithReplacementHint(solver.GetHintID(deferredChecksRLCHint), forgeDeferredChecksRLCHint),
	)
	if err == nil {
		t.Fatal("SOUNDNESS BREAK: circuit accepted 3*5 == 16")
	}
	t.Logf("forgery rejected: %v", err)
}
