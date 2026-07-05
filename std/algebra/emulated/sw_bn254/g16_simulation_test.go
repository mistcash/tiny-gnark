package sw_bn254

import (
	"bytes"
	"fmt"
	"testing"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark-crypto/ecc/bn254"
	"github.com/consensys/gnark/constraint"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/r1cs"
	"github.com/consensys/gnark/frontend/cs/scs"
	"github.com/consensys/gnark/test"
)

// Groth16Simulation combines:
//   - a 2-pair PairingCheck using fixed (precomputed) G2 points, and
//   - an AssertMillerLoopAndFinalExpIsOne check where one Miller loop result
//     is supplied as a witness (computed outside the circuit).
type Groth16Simulation struct {
	// Set 1: e(In1G1, In1G2) * e(In2G1, In2G2) == 1, fixed G2 points
	In1G1 G1Affine
	In1G2 G2Affine // fixed – precomputed line evaluations
	In2G1 G1Affine
	In2G2 G2Affine // fixed – precomputed line evaluations
	In3G1 G1Affine
	In3G2 G2Affine
}

func (c *Groth16Simulation) Define(api frontend.API) error {
	pairing, err := NewPairing(api)
	if err != nil {
		return fmt.Errorf("new pairing: %w", err)
	}

	err = pairing.PairingCheck(
		[]*G1Affine{&c.In1G1, &c.In2G1, &c.In3G1},
		[]*G2Affine{&c.In1G2, &c.In2G2, &c.In3G2},
	)
	return nil
}

func TestGroth16SimulationTestSolve(t *testing.T) {
	assert := test.NewAssert(t)

	p, q := randomG1G2Affines()
	var p1, p2, p3 bn254.G1Affine
	var q1, q2, q3 bn254.G2Affine
	p1.Double(&p)
	q1.Double(&q)
	p2.Neg(&p1)
	q2.Set(&q)
	p3.Set(&p)
	q3.Neg(&q1)

	witness := Groth16Simulation{
		In1G1: NewG1Affine(p1),
		In2G1: NewG1Affine(p2),
		In1G2: NewG2AffineFixed(q1),
		In2G2: NewG2AffineFixed(q2),
		In3G1: NewG1Affine(p3),
		In3G2: NewG2Affine(q3),
	}
	circuit := Groth16Simulation{
		In1G2: NewG2AffineFixedPlaceholder(),
		In2G2: NewG2AffineFixedPlaceholder(),
	}

	ccs, err := frontend.Compile(ecc.BN254.ScalarField(), scs.NewBuilder, &circuit)
	assert.NoError(err)

	t.Logf("nb commitments: %d, nbConstraints %d, nbInstructions: %d", scs.NbCommitments, ccs.GetNbConstraints(), ccs.GetNbInstructions())

	circuit = Groth16Simulation{
		In1G2: NewG2AffineFixedPlaceholder(),
		In2G2: NewG2AffineFixedPlaceholder(),
	}

	ccs, err = frontend.Compile(ecc.BN254.ScalarField(), r1cs.NewBuilder, &circuit)
	assert.NoError(err)

	t.Logf("nb commitments: %d, nbConstraints %d, nbInstructions: %d", scs.NbCommitments, ccs.GetNbConstraints(), ccs.GetNbInstructions())

	circuit = Groth16Simulation{
		In1G2: NewG2AffineFixedPlaceholder(),
		In2G2: NewG2AffineFixedPlaceholder(),
	}

	err = test.IsSolved(&circuit, &witness, ecc.BN254.ScalarField())
	assert.NoError(err)
}

func BenchmarkGroth16Simulation(b *testing.B) {
	p, q := randomG1G2Affines()
	var p1, p2, p3 bn254.G1Affine
	var q1, q2, q3 bn254.G2Affine
	p1.Double(&p)
	q1.Double(&q)
	p2.Neg(&p1)
	q2.Set(&q)
	p3.Set(&p)
	q3.Neg(&q1)

	witness := Groth16Simulation{
		In1G1: NewG1Affine(p1),
		In2G1: NewG1Affine(p2),
		In1G2: NewG2AffineFixed(q1),
		In2G2: NewG2AffineFixed(q2),
		In3G1: NewG1Affine(p3),
		In3G2: NewG2Affine(q3),
	}

	circuit := Groth16Simulation{
		In1G2: NewG2AffineFixedPlaceholder(),
		In2G2: NewG2AffineFixedPlaceholder(),
	}

	w, err := frontend.NewWitness(&witness, ecc.BN254.ScalarField())
	if err != nil {
		b.Fatal(err)
	}
	var ccs constraint.ConstraintSystem
	b.Run("compile scs", func(b *testing.B) {
		b.ResetTimer()
		for i := 0; i < b.N; i++ {
			circuit = Groth16Simulation{
				In1G2: NewG2AffineFixedPlaceholder(),
				In2G2: NewG2AffineFixedPlaceholder(),
			}
			if ccs, err = frontend.Compile(ecc.BN254.ScalarField(), scs.NewBuilder, &circuit); err != nil {
				b.Fatal(err)
			}
		}
	})
	var buf bytes.Buffer
	_, err = ccs.WriteTo(&buf)
	if err != nil {
		b.Fatal(err)
	}
	b.Logf("nb commitments: %d, scs size: %d (bytes), nb constraints %d, nbInstructions: %d", scs.NbCommitments, buf.Len(), ccs.GetNbConstraints(), ccs.GetNbInstructions())
	b.Run("solve scs", func(b *testing.B) {
		b.ResetTimer()
		for i := 0; i < b.N; i++ {
			if _, err := ccs.Solve(w); err != nil {
				b.Fatal(err)
			}
		}
	})
	b.Run("compile r1cs", func(b *testing.B) {
		b.ResetTimer()
		for i := 0; i < b.N; i++ {
			circuit = Groth16Simulation{
				In1G2: NewG2AffineFixedPlaceholder(),
				In2G2: NewG2AffineFixedPlaceholder(),
			}
			if ccs, err = frontend.Compile(ecc.BN254.ScalarField(), r1cs.NewBuilder, &circuit); err != nil {
				b.Fatal(err)
			}
		}
	})
	buf.Reset()
	_, err = ccs.WriteTo(&buf)
	if err != nil {
		b.Fatal(err)
	}
	b.Logf("nb commitments: %d, r1cs size: %d (bytes), nb constraints %d, nbInstructions: %d", scs.NbCommitments, buf.Len(), ccs.GetNbConstraints(), ccs.GetNbInstructions())
	b.Run("solve r1cs", func(b *testing.B) {
		b.ResetTimer()
		for i := 0; i < b.N; i++ {
			if _, err := ccs.Solve(w); err != nil {
				b.Fatal(err)
			}
		}
	})
}

// Benchmark results BEFORE

// ➜ go test -v -test.fullpath=true -benchmem -run=^$ -bench ^BenchmarkGroth16Simulation$ github.com/consensys/gnark/std/algebra/emulated/sw_bn254
// goos: darwin
// goarch: arm64
// pkg: github.com/consensys/gnark/std/algebra/emulated/sw_bn254
// cpu: Apple M3 Pro
// BenchmarkGroth16Simulation
// BenchmarkGroth16Simulation/compile_scs
// BenchmarkGroth16Simulation/compile_scs-12                      2         615039500 ns/op        1433215804 B/op  8212603 allocs/op
//     ./std/algebra/emulated/sw_bn254/g16_simulation_test.go:141: nb commitments: 571125, scs size: 41180931 (bytes), nb constraints 1592440, nbInstructions: 1650469
// BenchmarkGroth16Simulation/solve_scs
// BenchmarkGroth16Simulation/solve_scs-12                        6         167566014 ns/op        365668922 B/op   1275358 allocs/op
// BenchmarkGroth16Simulation/compile_r1cs
// BenchmarkGroth16Simulation/compile_r1cs-12                     2         617626084 ns/op        1722892844 B/op 15630073 allocs/op
//     ./std/algebra/emulated/sw_bn254/g16_simulation_test.go:167: nb commitments: 571125, r1cs size: 32248852 (bytes), nb constraints 491447, nbInstructions: 549478
// BenchmarkGroth16Simulation/solve_r1cs
// BenchmarkGroth16Simulation/solve_r1cs-12                       6         175422285 ns/op        181680978 B/op   1275541 allocs/op
// PASS
// ok      github.com/consensys/gnark/std/algebra/emulated/sw_bn254        6.751s

// Benchmark results AFTER

// ➜ go test -v -test.fullpath=true -benchmem -run=^$ -bench ^BenchmarkGroth16Simulation$ github.com/consensys/gnark/std/algebra/emulated/sw_bn254
// goos: darwin
// goarch: arm64
// pkg: github.com/consensys/gnark/std/algebra/emulated/sw_bn254
// cpu: Apple M3 Pro
// BenchmarkGroth16Simulation
// BenchmarkGroth16Simulation/compile_scs
// BenchmarkGroth16Simulation/compile_scs-12                      3         366773583 ns/op        877550837 B/op   5443292 allocs/op
//     ./std/algebra/emulated/sw_bn254/g16_simulation_test.go:141: nb commitments: 269520, scs size: 25537582 (bytes), nb constraints 1035242, nbInstructions: 1069315
// BenchmarkGroth16Simulation/solve_scs
// BenchmarkGroth16Simulation/solve_scs-12                        9         112571819 ns/op        189990416 B/op    289586 allocs/op
// BenchmarkGroth16Simulation/compile_r1cs
// BenchmarkGroth16Simulation/compile_r1cs-12                     3         380631264 ns/op        1054561938 B/op  9711792 allocs/op
//     ./std/algebra/emulated/sw_bn254/g16_simulation_test.go:167: nb commitments: 269520, r1cs size: 19238371 (bytes), nb constraints 315955, nbInstructions: 350030
// BenchmarkGroth16Simulation/solve_r1cs
// BenchmarkGroth16Simulation/solve_r1cs-12                       9         123303704 ns/op        118157063 B/op    289962 allocs/op
// PASS
// ok      github.com/consensys/gnark/std/algebra/emulated/sw_bn254        7.577s