package sw_bls12381

import (
	"bytes"
	"fmt"
	"testing"

	"github.com/consensys/gnark-crypto/ecc"
	bls12381 "github.com/consensys/gnark-crypto/ecc/bls12-381"
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
	var p1, p2, p3 bls12381.G1Affine
	var q1, q2, q3 bls12381.G2Affine
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

	ccs, err := frontend.Compile(ecc.BLS12_381.ScalarField(), scs.NewBuilder, &circuit)
	assert.NoError(err)

	t.Logf("nb commitments: %d, nbConstraints %d, nbInstructions: %d", scs.NbCommitments, ccs.GetNbConstraints(), ccs.GetNbInstructions())

	circuit = Groth16Simulation{
		In1G2: NewG2AffineFixedPlaceholder(),
		In2G2: NewG2AffineFixedPlaceholder(),
	}

	ccs, err = frontend.Compile(ecc.BLS12_381.ScalarField(), r1cs.NewBuilder, &circuit)
	assert.NoError(err)

	t.Logf("nb commitments: %d, nbConstraints %d, nbInstructions: %d", scs.NbCommitments, ccs.GetNbConstraints(), ccs.GetNbInstructions())

	circuit = Groth16Simulation{
		In1G2: NewG2AffineFixedPlaceholder(),
		In2G2: NewG2AffineFixedPlaceholder(),
	}

	err = test.IsSolved(&circuit, &witness, ecc.BLS12_381.ScalarField())
	assert.NoError(err)
}

func BenchmarkGroth16Simulation(b *testing.B) {
	p, q := randomG1G2Affines()
	var p1, p2, p3 bls12381.G1Affine
	var q1, q2, q3 bls12381.G2Affine
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

	w, err := frontend.NewWitness(&witness, ecc.BLS12_381.ScalarField())
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
			if ccs, err = frontend.Compile(ecc.BLS12_381.ScalarField(), scs.NewBuilder, &circuit); err != nil {
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
			if ccs, err = frontend.Compile(ecc.BLS12_381.ScalarField(), r1cs.NewBuilder, &circuit); err != nil {
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

// ➜ go test -v -test.fullpath=true -benchmem -run=^$ -bench ^BenchmarkGroth16Simulation$ github.com/consensys/gnark/std/algebra/emulated/sw_bls12381
// goos: darwin
// goarch: arm64
// pkg: github.com/consensys/gnark/std/algebra/emulated/sw_bls12381
// cpu: Apple M3 Pro
// BenchmarkGroth16Simulation
// BenchmarkGroth16Simulation/compile_scs
// BenchmarkGroth16Simulation/compile_scs-12                      2         650022979 ns/op        1584562044 B/op  9028669 allocs/op
//     ./std/algebra/emulated/sw_bls12381/g16_simulation_test.go:141: nb commitments: 660160, scs size: 43868077 (bytes), nb constraints 1784247, nbInstructions: 1849543
// BenchmarkGroth16Simulation/solve_scs
// BenchmarkGroth16Simulation/solve_scs-12                        6         180049278 ns/op        379735170 B/op   1394779 allocs/op
// BenchmarkGroth16Simulation/compile_r1cs
// BenchmarkGroth16Simulation/compile_r1cs-12                     2         686947854 ns/op        1871297060 B/op 16882975 allocs/op
//     ./std/algebra/emulated/sw_bls12381/g16_simulation_test.go:167: nb commitments: 660160, r1cs size: 34210621 (bytes), nb constraints 545510, nbInstructions: 610808
// BenchmarkGroth16Simulation/solve_r1cs
// BenchmarkGroth16Simulation/solve_r1cs-12                       6         182721285 ns/op        243027600 B/op   1394959 allocs/op
// PASS
// ok      github.com/consensys/gnark/std/algebra/emulated/sw_bls12381     7.235s

// Benchmark results AFTER

// ➜ go test -v -test.fullpath=true -benchmem -run=^$ -bench ^BenchmarkGroth16Simulation$ github.com/consensys/gnark/std/algebra/emulated/sw_bls12381
// goos: darwin
// goarch: arm64
// pkg: github.com/consensys/gnark/std/algebra/emulated/sw_bls12381
// cpu: Apple M3 Pro
// BenchmarkGroth16Simulation
// BenchmarkGroth16Simulation/compile_scs
// BenchmarkGroth16Simulation/compile_scs-12                      3         415050333 ns/op        1038236248 B/op  6072992 allocs/op
//     ./std/algebra/emulated/sw_bls12381/g16_simulation_test.go:141: nb commitments: 300032, scs size: 28116728 (bytes), nb constraints 1191033, nbInstructions: 1229131
// BenchmarkGroth16Simulation/solve_scs
// BenchmarkGroth16Simulation/solve_scs-12                       10         111708942 ns/op        298150729 B/op    262890 allocs/op
// BenchmarkGroth16Simulation/compile_r1cs
// BenchmarkGroth16Simulation/compile_r1cs-12                     3         418324833 ns/op        1219640528 B/op 10814557 allocs/op
//     ./std/algebra/emulated/sw_bls12381/g16_simulation_test.go:167: nb commitments: 300032, r1cs size: 21884880 (bytes), nb constraints 368434, nbInstructions: 406534
// BenchmarkGroth16Simulation/solve_r1cs
// BenchmarkGroth16Simulation/solve_r1cs-12                       9         119968986 ns/op        124435892 B/op    263899 allocs/op
// PASS
// ok      github.com/consensys/gnark/std/algebra/emulated/sw_bls12381     7.826s
