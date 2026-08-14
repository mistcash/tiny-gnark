# Random-Linear-Combination Amortisation of Deferred Non-Native Checks

## Abstract

Non-native (emulated) arithmetic in a SNARK circuit is verified by deferring
multiplication checks and discharging them in a batch against a Schwartz–Zippel
challenge. This note formalises two amortisation schemes built on that idea. The
first, implemented in `field_polyring.go`, batches the *quotients* of
multiplications in a polynomial ring `F_p[Y]/(P(Y))` using a random linear
combination (RLC), so that the prover supplies a single aggregated quotient
instead of one per operation. We prove this scheme sound and give explicit
Schwartz–Zippel bounds. The second, implemented in `field_mul.go`, transplants
the same RLC to the *integer* limb-decomposition checks used for base-field
multiplication. We show this transplant is **unsound**, exhibit a forgery, and
identify the structural reason: the ring scheme derives its binding power from
divisibility by a degree-`d ≥ 1` modulus, whereas the integer scheme derives its
binding power from range checks that RLC necessarily destroys.

---

## 1. Notation

| Symbol | Meaning |
| --- | --- |
| `q` | prime of the native circuit field `F_q` |
| `p` | emulated modulus (`p ≠ 0 mod q`) |
| `t` | bits per limb (`BitsPerLimb`) |
| `n` | limbs per emulated element (`NbLimbs`) |
| `N` | number of deferred checks in a batch |

An emulated element `a` with limbs `(a_0, …, a_{n-1})` is identified with its
*limb polynomial*

```
a(X) = Σ_j a_j · X^j        so that   a = a(2^t).
```

Range checks assert `0 ≤ a_j < 2^t`; they are what ties the polynomial `a(X)`
back to the integer `a`.

---

## 2. Scheme A — RLC over a polynomial ring (`field_polyring.go`)

### 2.1 Statement

Work in `R = F_p[Y]/(P(Y))` with `P` public and `deg P = d ≥ 1`. Check `i`
(`i = 0..N-1`) asserts a product of `m_i` ring elements

```
∏_j A_ij  =  R_i        in R,
```

witnessed by a quotient `Q_i ∈ F_p[Y]` with

```
∏_j A_ij(Y) − R_i(Y)  =  Q_i(Y) · P(Y)        in F_p[Y].            (A1)
```

Coefficients here are *emulated field elements*, each handled by the ordinary
(sound) emulated arithmetic; `Y` is the ring indeterminate.

### 2.2 Protocol

1. **Round 1.** Prover commits to all inputs `A_ij` and all remainders `R_i`.
   Challenge `z` is derived from that commitment.
2. **Round 2.** Prover computes and sends the single aggregated quotient
   `Q_acc(Y) = Σ_i z^i · Q_i(Y)`, computed *outside* the circuit by a hint.
   Challenge `x` is derived from a commitment to `(z, Q_acc)`.
3. **Round 3.** Verifier checks the single identity

```
Σ_i z^i · ( ∏_j A_ij(x) − R_i(x) )  =  Q_acc(x) · P(x).             (A2)
```

The saving is that neither `Q_i` nor its evaluation is ever formed in-circuit:
`N` quotient evaluations collapse to one.

### 2.3 Soundness

Let `E_i(Y) := ∏_j A_ij(Y) − R_i(Y) ∈ F_p[Y]`, fixed by the round-1 commitment
before `z` is known. Let `Ē_i := E_i mod P`. Check `i` is *true* iff `Ē_i = 0`.
Write `D := max_i deg E_i` and `D_Q` for the degree bound imposed on `Q_acc` by
its fixed coefficient count in the circuit.

> **Theorem 1.** Suppose `Ē_{i₀} ≠ 0` for some `i₀` (some check is false). Then
> the verifier accepts (A2) with probability at most
>
> ```
> (N − 1)/|Z|  +  max(D, D_Q + d)/|X|,
> ```
>
> where `Z`, `X` are the challenge sets for `z` and `x`.

*Proof.* Two bad events.

**(i) Bad `z`.** Consider `F(Z) := Σ_i Z^i · Ē_i` over the ring
`(F_p[Y]/(P))[Z]`. Expanding in the basis `1, Y, …, Y^{d-1}`, some coordinate of
`Ē_{i₀}` is a nonzero element of `F_p`; that coordinate of `F` is therefore a
nonzero univariate polynomial in `Z` of degree `≤ N − 1`. By Schwartz–Zippel it
vanishes at a uniform `z` with probability `≤ (N−1)/|Z|`. Off this event,
`Σ_i z^i Ē_i ≠ 0`, i.e. `P ∤ Σ_i z^i E_i`.

**(ii) Bad `x`.** Fix such a `z`, and let `Q_acc` be whatever the prover sent —
crucially it is committed *before* `x` is drawn, so it is a fixed polynomial.
Put

```
D(Y) := Σ_i z^i E_i(Y) − Q_acc(Y) · P(Y).
```

If `D ≡ 0` then `P | Σ_i z^i E_i`, contradicting (i). So `D ≠ 0`, and
`deg D ≤ max(D, D_Q + d)`. By Schwartz–Zippel, `D(x) = 0` with probability
`≤ max(D, D_Q + d)/|X|`. Acceptance of (A2) is exactly `D(x) = 0`. ∎

Two hypotheses are load-bearing and both are met by the implementation:

- **`Q_acc` is committed before `x`.** `performDeferredRingChecks` commits
  remainders → `z`, then commits `(z, Q_acc)` → `x`. Reversing this order would
  let the prover solve for `Q_acc` after seeing `x` and Theorem 1 would fail.
- **`Q_acc` has a bounded degree and well-formed coefficients.** Its coefficient
  count is fixed by the circuit, and each coefficient is produced by
  `packLimbs(·, false)`, i.e. **range checked**. Without that, a coefficient
  could carry out-of-range limbs and violate the overflow preconditions of the
  subsequent emulated multiplication.

Note what is *not* needed: the individual `Q_i` need no range checks at all
(`newInternalElement(·, 0)`), because they appear only as hint inputs and
soundness never refers to them. This is exactly the source of the large saving.

### 2.4 Concrete bounds

The implementation truncates both challenges to `nbChallengeLimbs = 2` limbs, so
`|Z| = |X| = 2^{2t}` (`= 2^128` for `t = 64`). With `N` checks and degrees as
above the soundness error is

```
(N − 1)/2^128 + max(D, D_Q + d)/2^128 ≈ 2^{-128} · (N + D_Q + d),
```

comfortably negligible for any realistic circuit (`N + D_Q + d ≪ 2^40`).

**Scheme A is sound.**

---

## 3. Scheme B — the same RLC over integer limb checks (`field_mul.go`)

### 3.1 Statement

Base-field multiplication does not live in a polynomial ring. Check `i` asserts
`a_i · b_i = r_i + k_i · p` over **ℤ**, encoded as the limb-polynomial identity

```
a_i(X)·b_i(X) − r_i(X) − k_i(X)·p(X) − (2^t − X)·c_i(X) = 0     in F_q[X].  (B1)
```

`mvCheck` is the same shape with `a_i(X)b_i(X)` replaced by a multivariate
expression in several emulated inputs. Here `k_i` is the integer quotient and
`c_i` is a *carry* witness whose only job is to certify divisibility by
`(2^t − X)`.

The legacy verifier checks (B1) per check at a single shared challenge, with
`a_i, b_i, r_i, k_i` all range checked (`field_mul.go:778` range checks `k`;
`c` is deliberately unchecked).

### 3.2 The transplanted protocol

`scheduleRLCDeferredChecks` aggregates *both* the quotient and the carry:

```
K(X) = Σ_i z^i k_i(X),      C(X) = Σ_i z^i c_i(X),
```

both produced by `deferredChecksRLCHint`, and checks the single identity

```
Σ_i z^i ( a_i(x)b_i(x) − r_i(x) )  =  p(x)·K(x) + (2^t − x)·C(x).    (B2)
```

### 3.3 Scheme B is unsound

> **Theorem 2.** For *any* values `a_i, b_i, r_i` whatsoever — in particular for
> a false product — there exist `K` and `C` within the coefficient budgets
> allotted by the circuit satisfying (B2) identically in `x`. The check
> therefore constrains nothing.

*Proof.* Let `L(X) := Σ_i z^i (a_i(X)b_i(X) − r_i(X))`, `deg L ≤ 2n − 2`. The
question is whether `L` lies in the ideal `I = (p(X), 2^t − X) ⊆ F_q[X]`. The
polynomial `2^t − X` is degree 1, hence irreducible, with unique root `X = 2^t`.
Since `p(2^t) = p ≢ 0 (mod q)`, it is *not* a root of `p(X)`, so

```
gcd( p(X), 2^t − X ) = 1        and therefore   I = F_q[X].
```

The ideal is the **unit ideal**: every `L` is representable. Concretely, choose
the constant `K := L(2^t) · p^{-1} mod q`. Then `L(2^t) − p(2^t)·K = 0`, so
`(2^t − X)` divides `L(X) − p(X)K` exactly, and

```
C(X) := ( L(X) − p(X)·K ) / (2^t − X)
```

is a polynomial of degree `≤ 2n − 3`, within the `maxCLen` budget. Both fit. ∎

The contrast with Theorem 1 is stark. There, `P` had degree `d ≥ 1` and
"`P` divides the aggregate" was a nontrivial condition that a bounded-degree
`Q_acc` could not fake. Here the modulus side generates the whole ring, so there
is no divisibility obstruction whatsoever. In the legacy per-check verifier the
missing constraint is supplied by **range checks on `k_i`** — but the honest
aggregate `K = Σ z^i k_i mod q` is a full-width pseudorandom field element, so it
*cannot* be range checked without destroying completeness. The scheme has no
sound parameterisation; it is not a matter of a missing assertion.

Corollary of the proof: `ΔK(X) = X − 2^t`, `ΔC(X) = p(X)` is a nonzero element of
the kernel, so `(K, C)` is not even uniquely determined by the honest witness.

### 3.4 Experimental confirmation

`field_mul_rlc_soundness_test.go` implements the attack of Theorem 2 for
`BN254Fp`. A circuit computes `A·B` and asserts it equals `Expected`; the witness
sets `Expected = A·B + 1`.

- `TestRLCWrongProductRejected` — **passes**. Corrupting the product while
  leaving the accumulators honest is caught, confirming the deferred check is
  wired up and does its job normally.
- `TestRLCForgedProduct` — **fails**, i.e. the forgery succeeds. Patching the
  accumulators by the correction of Theorem 2 makes the circuit accept
  `3 · 5 = 16`.

The correction is computed from the *public* modulus alone; it uses no knowledge
of `A`, `B` or `r`, and not even of the challenge `z`.
`TestRLCForgedProduct` is written to pass once the aggregation is repaired, so it
doubles as a regression test.

Note that the existing `TestDeferredChecksRLC` does not catch this: it perturbs
`outputs[0]` by `+1` without re-solving for `C`, which lands outside the kernel
and is correctly rejected. It tests robustness against a *careless* prover, not
against an adversarial one.

---

## 4. Why the measured saving was small

The commit reports 3.6 % (`emulated/secp256k1_64`) to 9.7 % (`scalar_mul_*`)
fewer R1CS constraints, rising to ~28 % for pairings. Two observations:

1. **The reported saving is not a real saving.** Part of the reduction comes
   from deleting constraints that were load-bearing for soundness (Theorem 2).
   It is not a baseline any correct implementation can match.

2. **The expensive constraints were nevertheless kept.** `callMulHint` still
   calls `packLimbs(ret[:nbQuoLimbs], false)`, so every per-check quotient `k_i`
   is *still range checked*. In the RLC path `k_i` then appears only as an input
   to `deferredChecksRLCHint` — and hint inputs are not constraints. The limbs
   are therefore **dangling**: the circuit pays the full range-check cost and
   gets no binding in return. The implementation removed the cheap part (a
   handful of `MulAcc` per check) and retained the expensive part.

This is the direct answer to why Scheme B saved ~10 % where Scheme A saved ~35 %.
Scheme A's saving comes precisely from *not* range checking the per-check
quotients — which it can afford because its soundness argument never mentions
them. Scheme B cannot make that trade: range checks on `k_i` are the entire
source of its binding power. The 35 % is not a target Scheme B can reach.

---

## 5. What can be amortised soundly

The carry `c_i` is aggregatable; the quotient `k_i` is not.

Keep `k_i` inside the checked identity and aggregate only the carry:

```
Σ_i z^i ( a_i(x)b_i(x) − r_i(x) − k_i(x)·p(x) )  =  (2^t − x)·C(x),
C(X) = Σ_i z^i c_i(X).
```

Soundness follows the legacy argument: acceptance certifies that
`(2^t − X)` divides the aggregate, i.e. `Σ_i z^i e_i ≡ 0 (mod q)` where
`e_i := a_i b_i − r_i − k_i p` is the residual of check `i`. Each `e_i` remains
individually range-constrained exactly as in the legacy scheme, and a
Schwartz–Zippel argument over `z` (degree `≤ N − 1`) forces every `e_i` to
vanish, with error `≤ (N−1)/|Z|`.

The saving is real but bounded: `c_i` is the *widest* witness of a check
(`≈ 2n − 1` limbs versus `n` for `k_i`), so this removes the single largest
per-check evaluation — roughly `2n − 2` `MulAcc` per check, replaced by one
accumulation — while leaving every range check and the `k_i` evaluation intact.
Expect a saving well below the measured 10 %, and nothing near 35 %.

A more aggressive sound variant would replace the powers `z^i` by *independent
small* challenges `ζ_i < 2^λ`, which keeps `K = Σ ζ_i k_i` small enough to range
check (`t + λ + log N` bits). That restores a bound on `K` and would permit
dropping the per-check `k_i` range checks. It requires care: the coefficient
bounds that lift the `F_q[X]` identity to ℤ must be re-derived for the widened
`K`, and generating `N` independent small challenges has its own cost. This is a
design change, not a patch, and should be specified and reviewed before being
attempted.

---

## 6. Recommendations

1. **Do not ship `scheduleRLCDeferredChecks` in its current form.** It removes
   soundness from every consumer of emulated arithmetic — pairings, ECDSA, RSA,
   all non-native EC operations. Revert to the legacy path, or gate it off,
   until a sound design replaces it.
2. **Regenerate `internal/stats/latest_stats.csv`.** The committed constraint
   counts were produced by the unsound circuit and understate the true cost.
3. **Keep `field_mul_rlc_soundness_test.go`.** It fails today by design and will
   pass when the aggregation is fixed.
4. **Scheme A (`field_polyring.go`) is unaffected** and remains sound as
   analysed in §2. The two schemes are not interchangeable, and the reason is
   structural, not incidental: `deg P ≥ 1` versus the unit ideal.
