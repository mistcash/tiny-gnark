package emulated

import (
	"math/big"
	"testing"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/constraint/solver"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/test"
)

type deferredChecksRLCCircuit struct {
	A, B, C, D Element[BN254Fp]
	AB, CD     Element[BN254Fp]
	Difference Element[BN254Fp]
}

func (c *deferredChecksRLCCircuit) Define(api frontend.API) error {
	f, err := NewField[BN254Fp](api)
	if err != nil {
		return err
	}
	ab := f.Mul(&c.A, &c.B)
	cd := f.Mul(&c.C, &c.D)
	difference := f.Eval(
		[][]*Element[BN254Fp]{{&c.A, &c.B}, {&c.C, &c.D}},
		[]int{1, -1},
	)
	f.AssertIsEqual(ab, &c.AB)
	f.AssertIsEqual(cd, &c.CD)
	f.AssertIsEqual(difference, &c.Difference)
	return nil
}

func corruptDeferredChecksRLCHint(mod *big.Int, inputs, outputs []*big.Int) error {
	if err := deferredChecksRLCHint(mod, inputs, outputs); err != nil {
		return err
	}
	if len(outputs) > 0 {
		outputs[0].Add(outputs[0], big.NewInt(1))
		outputs[0].Mod(outputs[0], mod)
	}
	return nil
}

func TestDeferredChecksRLC(t *testing.T) {
	p := BN254Fp{}.Modulus()
	difference := new(big.Int).Sub(big.NewInt(15), big.NewInt(77))
	difference.Mod(difference, p)
	witness := &deferredChecksRLCCircuit{
		A:          ValueOf[BN254Fp](3),
		B:          ValueOf[BN254Fp](5),
		C:          ValueOf[BN254Fp](7),
		D:          ValueOf[BN254Fp](11),
		AB:         ValueOf[BN254Fp](15),
		CD:         ValueOf[BN254Fp](77),
		Difference: ValueOf[BN254Fp](difference),
	}

	if err := test.IsSolved(&deferredChecksRLCCircuit{}, witness, ecc.BN254.ScalarField()); err != nil {
		t.Fatalf("solve valid RLC circuit: %v", err)
	}
	if err := test.IsSolved(
		&deferredChecksRLCCircuit{},
		witness,
		ecc.BN254.ScalarField(),
		test.WithReplacementHint(solver.GetHintID(deferredChecksRLCHint), corruptDeferredChecksRLCHint),
	); err == nil {
		t.Fatal("expected corrupted RLC accumulator to fail")
	}
}
