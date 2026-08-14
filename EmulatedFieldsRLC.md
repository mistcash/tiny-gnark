# Random-Linear-Combination Aggregation of Deferred Emulated-Field Checks

**Status: the proposal, as stated, is _not_ sound. A restricted form of it is sound and is
proved below.**

---

## Abstract

`std/math/emulated` defers every non-native multiplication and multivariate evaluation to a
single batched verifier, which tests one polynomial identity per operation at a common random
point. `field_polyring.go` shows that an analogous family of checks over a polynomial ring can
be collapsed into a *single* identity by taking a random linear combination (RLC) of the
per-operation statements, with the prover supplying the combined quotient directly. This note
transplants that construction to the per-element checks of `field_mul.go`, and analyses it.

We show that the transplant fails. The obstruction is structural, not an implementation defect:
in the polynomial-ring setting the quotient is constrained by its **degree**, and degree
constraints are preserved by linear combination; in the emulated-integer setting the quotient is
constrained by its **magnitude**, and magnitude constraints are destroyed by reduction modulo the
native field. Aggregating the quotient therefore removes the only binding property the check has.
We give the forgery explicitly (Theorem 1) and confirm it against the implementation.

We then isolate the part of the construction that does survive: the **carry** polynomial may be
aggregated, because it certifies a divisibility — a degree-type property. We prove soundness for
that variant (Theorem 2) with Schwartz–Zippel error `(m-1)/q + D/q`, and give the cost model that
bounds the achievable saving, which explains the observed gap against the polynomial-ring result.

---

## 1. Notation

| symbol | meaning |
|---|---|
| `q` | native (SNARK scalar) field modulus; all circuit arithmetic is in `F_q` |
| `p` | emulated modulus, `m_p = ceil(log2 p)` bits |
| `w` | limb width (`BitsPerLimb`), `n = ceil(m_p / w)` limbs |
| `a_j` | the `j`-th limb of an element `a` |
| `a(X)` | limb polynomial `sum_j a_j X^j`; the integer value is `a = a(2^w)` |
| `t` | shorthand for `2^w` (the code's `coef`) |

An element is *range-checked to `L` limbs* when each limb is constrained to `w` bits, so its
integer value is `< 2^{wL}`. Range checks are the only source of magnitude information about a
hinted value; a value produced by a hint and not range-checked is an arbitrary element of `F_q`.

---

## 2. The baseline deferred check

### 2.1 `mulCheck`

For `a * b = r + k*p`, the hint returns `r` (range-checked, `n` limbs), `k` (range-checked,
`n_k` limbs) and a carry `c` (`n_c` limbs, **not** range-checked). The verifier is given the
identity

```
a(X)·b(X)  =  r(X) + k(X)·p(X) + (t - X)·c(X)                                   (1)
```

which holds over `Z[X]` for an honest prover, and is tested at one random `x` in `F_q`.

### 2.2 `mvCheck`

`Field.Eval` generalises the left side to a multivariate form with signed coefficients, the sign
of the quotient being carried by a boolean `kNeg`:

```
F(v_1(X), ..., v_s(X))  =  r(X) + s_k·k(X)·p(X) + (t - X)·c(X),   s_k = 1 - 2·kNeg     (2)
```

### 2.3 What identity (1) actually proves

> **Lemma 1.** For `G` in `F_q[X]`, there exists `C` in `F_q[X]` with `G(X) = (t - X)·C(X)` if
> and only if `G(t) = 0` in `F_q`. When it exists, `C` is unique and `deg C = deg G - 1`.

*Proof.* `F_q[X]/(t - X)` is isomorphic to `F_q` by evaluation at `t`; `(t - X)` is monic up to
the unit `-1`, so division is exact and the quotient unique. ∎

Since `c` carries no range checks, it is a free witness, and by Lemma 1 the *only* information
(1) conveys is the scalar statement

```
a·b - r - k·p  ==  0   (mod q)                                                  (3)
```

Everything else must come from the range checks. Writing `E = a·b - r - k·p` over `Z`, the check
is binding exactly when the range checks force `|E| < q/2`, whereupon (3) gives `E = 0` over `Z`
and hence `a·b ≡ r (mod p)`. **The soundness of the baseline is a magnitude argument about `k`.**
This is the property that the aggregation below must preserve — and does not.

*(An observation about how tightly the shipped parameters actually enforce `|E| < q/2` is
recorded separately in Appendix B; it is independent of the RLC work and is not relied on
anywhere in §5.)*

---

## 3. Why the polynomial-ring construction aggregates

In `field_polyring.go` the objects are polynomials over the *emulated field* and the statement is

```
prod_j A_j(Y)  =  R(Y) + Q(Y)·M(Y)          in  F_p[Y]
```

`Q` is constrained only by its **length** (`qDegree + 1` coefficients); its coefficients need no
range checks, and the code says so explicitly. Cheating requires `M(Y)` to divide the residual —
a genuine algebraic obstruction that a length-bounded `Q` cannot fake. Divisibility is
`F_p`-linear in the dividend:

```
rem( sum_i z^i·D_i , M )  =  sum_i z^i·rem( D_i , M )
```

so a random combination is divisible by `M` iff every summand is, up to a Schwartz–Zippel term.
Aggregation is therefore free *and* lets the prover drop every per-operation quotient, which is
where the reported ~35 % came from.

---

## 4. The proposed aggregation

Let checks `i = 1..m` have left sides `A_i(X)` (i.e. `a_i(X)b_i(X)`, or the multivariate form),
remainders `r_i`, quotients `k_i` and carries `c_i`.

* **Round 1.** Commit to `{a_i, b_i, r_i}`; derive `z`.
* **Prover message.** `K(X) = sum_i z^i·k_i(X)` and `C(X) = sum_i z^i·c_i(X)`, coefficient-wise
  in `F_q`, each on a fixed number of limbs.
* **Round 2.** Commit to `(z, K, C)`; derive `x`.
* **Check.**

```
sum_i z^i·( A_i(x) - r_i(x) )  =  p(x)·K(x) + (t - x)·C(x)                       (4)
```

The intended saving: `k_i(x)` and `c_i(x)` are never evaluated in-circuit, and the two products
`k_i(x)p(x)`, `c_i(x)(t-x)` collapse from `m` pairs to one.

---

## 5. Soundness

### 5.1 The aggregation is unsound

> **Theorem 1.** Fix any left sides `A_i` and any claimed remainders `r_i` satisfying their own
> range checks — in particular, arbitrary wrong ones. For every challenge `z` there exist `K`
> and `C` within the limb budgets of (4) that satisfy (4) identically in `X`. Check (4) therefore
> has no binding power whatsoever, for every choice of `p`, `q`, `w` and `n`.

*Proof.* Put `Phi(X) = sum_i z^i (A_i(X) - r_i(X))`. Take `K` to be the **constant**

```
K  =  Phi(t) · p^{-1}   in  F_q
```

which exists because `gcd(p, q) = 1` (`p` and `q` are distinct primes). Then
`(Phi - p·K)(t) = Phi(t) - p·K = 0`, so by Lemma 1 the polynomial

```
C(X)  =  ( Phi(X) - p(X)·K ) / (t - X)
```

is a polynomial of degree `max(deg Phi, n-1) - 1`. For the budgets produced by `callMulHint` and
`callPolyMvHint` this is `<= n_c - 1`, so `C` fits the allotted carry limbs, and `K` occupies a
single limb. Identity (4) holds for all `X`, hence at `x`. ∎

Three things are worth drawing out.

1. **The failure is not a parameter question.** No choice of limb budget helps: the forgery uses
   a one-limb `K`. Tightening the accumulator's length makes no difference.
2. **The per-check range checks on `k_i` become decorative.** `k_i` enters the circuit only as an
   input to the aggregation *hint*. No constraint relates `K` to any `k_i`, so the range checks
   on `k_i` — the dominant cost of a `mulCheck` — are paid for and bind nothing.
3. **The direction of the loss.** By §2.3 the check needed the *integer* statement
   `|E_i| < q/2` together with `E_i ≡ 0 (mod q)`. After aggregation the verifier learns only
   `sum_i z^i·E_i ≡ 0 (mod q)` with `sum_i z^i·k_i` supplied as an unconstrained field element,
   and that congruence is solvable for any `E_i` whatsoever.

### 5.2 Confirmation against the implementation

`M127` (`p = 2^127 - 1`, two 64-bit limbs over BN254) is a parameterisation in which the
per-check quotient range check *is* binding: the same class of forgery is rejected on the
pre-RLC code, because the forged quotient does not fit its 192-bit budget. It is therefore a
clean separator.

| configuration | pre-RLC path | RLC path |
|---|---|---|
| `M127`, forged remainder | **rejected** (quotient exceeds its 192-bit budget) | **accepted** |

`TestForgeRLCAggregation` implements exactly the construction of Theorem 1 — corrupt one
remainder, then rebuild `K` and `C` from the round-1 values and `z` — and obtains a satisfied
constraint system for `a*b = a*b + 1 mod p`. The regression test is committed alongside this
note.

### 5.3 A sound restriction: aggregate the carries only

Aggregating `C` alone is sound. Keep `k_i(x)·p(x)` per check and batch only the carry:

```
sum_i z^i·( A_i(x) - r_i(x) - k_i(x)·p(x) )  =  (t - x)·C(x),     C = sum_i z^i·c_i    (5)
```

> **Theorem 2.** Let `G_i(X) = A_i(X) - r_i(X) - k_i(X)·p(X)`, fixed by the round-1 commitment.
> Let `D` bound the degree in `X` of the aggregated identity and let `z, x` be uniform in `F_q`.
> If the verifier accepts (5) with probability greater than `(m-1)/q + D/q`, then
> `G_i(t) = 0` in `F_q` for every `i` — which is precisely the conclusion of the per-check
> baseline (3).

*Proof.* Suppose some `G_i(t) != 0`. Fix `z` and set
`H_z(X) = sum_i z^i·G_i(X) - (t - X)·C(X)`, of degree at most `D`; the verifier tests
`H_z(x) = 0`.

*Case `H_z` not identically zero.* By Schwartz–Zippel, `Pr_x[H_z(x) = 0] <= D/q`.

*Case `H_z` identically zero.* Then `(t - X)` divides `sum_i z^i·G_i(X)`, so by Lemma 1
`psi(z) := sum_i z^i·G_i(t) = 0`. As a polynomial in `z`, `psi` has degree at most `m-1` and is
not the zero polynomial, since some coefficient `G_i(t)` is non-zero. Hence
`Pr_z[psi(z) = 0] <= (m-1)/q`.

A union bound over the two cases gives the claim. ∎

Two remarks on the hypotheses. First, `C` is chosen *after* `z`; this is harmless, because the
argument only uses the *existence* of a witness to divisibility, not its value. Second, `x` must
be drawn after `C` is committed, or the prover can fit `C` to a known evaluation point — the
two-round commitment structure of §4 is required, not optional.

### 5.4 Concrete soundness

For a `mulCheck` with `n`-limb inputs, an `n_k`-limb quotient and an `n_c`-limb carry,

```
D  =  max( 2n - 2,  n + n_k - 2,  n_c )
```

and the aggregate error is `(m - 1 + D)/q`. For BN254 (`q ~ 2^254`), `n = 4`, `n_k = 5`,
`n_c = 7`, `D = 7`, and up to `m = 2^20` aggregated checks:

```
error  <=  (2^20 + 7) / 2^254  ~  2^-234
```

The aggregation term `(m-1)/q` is negligible against the term the baseline already pays, so the
sound variant costs essentially nothing in security. As always, `z` and `x` come from in-circuit
commitments, so the bound is conditional on the commitment scheme's binding property and on the
Fiat–Shamir heuristic applied to it.

### 5.5 The structural principle

> Random linear combination preserves **`F_q`-linear** properties of the aggregated statements
> and destroys **integer-magnitude** properties.

Divisibility by `(t - X)` is `F_q`-linear in the dividend, so carries aggregate (Theorem 2).
Degree bounds are `F_q`-linear, so the polynomial-ring quotient aggregates (§3). The bound
`|k| < 2^{w·n_k}` is not a property of `k mod q` at all, so `sum_i z^i k_i` retains nothing of
it (Theorem 1). Any future attempt to batch the quotient must first re-express the baseline's
magnitude argument as a degree or divisibility argument — for instance by range-checking the
carries, which lifts (1) to an identity over `Z[X]` — and only then aggregate.

---

## 6. Cost model: the ceiling on the saving

Per `mulCheck`, BN254Fp (`n = 4`, `n_k = 5`, `n_c = 7`), counting R1CS constraints:

| item | baseline | full RLC (unsound) | carry-only RLC (sound) |
|---|---|---|---|
| range checks on `r`, `k` | ~`n + n_k` limbs of lookups | unchanged (and now useless for `k`) | unchanged |
| evaluate `a`, `b` | `2(n-1)`, often cached | same | same |
| evaluate `r` | `n-1` | `n-1` | `n-1` |
| evaluate `k` | `n_k - 1` = 4 | — | `n_k - 1` |
| evaluate `c` | `n_c - 1` = 6 | — | — |
| products in the check | 3 | 1 | 2 |
| RLC fold | — | +1 | +1 |
| **saved per check** | — | **~11** | **~6** |

Amortised globals (one accumulator evaluation, one extra commitment) are `O(1)`.

Measured effect of the branch as implemented (`internal/stats/latest_stats.csv`, 44 of 170
circuits changed, mean −8.3 %):

| circuit | before | after | delta |
|---|---|---|---|
| `pairing_bn254` (groth16) | 505 959 | 365 100 | **−27.8 %** |
| `pairing_bls12381` (groth16) | 756 708 | 587 836 | −22.3 % |
| `pairing_bw6761` (groth16) | 1 589 471 | 1 282 176 | −19.3 % |
| `scalar_mul_P256` (groth16) | 96 434 | 86 136 | −10.7 % |
| `scalar_mul_secp256k1_incomplete` | 50 932 | 45 557 | −10.6 % |

So the branch already saves more than the ~10 % recalled — but the table above shows why it can
never reach the polynomial-ring figure honestly, and roughly half of what it does save is the
`k`-side term that Theorem 1 shows is not purchasable:

* the polynomial-ring RLC removes the **whole** per-operation quotient, *including its range
  checks*, because that quotient was only ever degree-bounded;
* the emulated RLC can at best remove per-check **evaluations**. The range checks on `k_i`
  — the dominant per-check cost — must stay, because they are the soundness argument.

Extrapolating the per-check table, the sound variant should retain on the order of half of the
measured reduction (~10-15 % on pairing circuits, ~5 % on scalar multiplication). That estimate
is arithmetic on the constraint counts above, not a measurement; it should be confirmed by
building the variant.

---

## 7. Assessment of the implementation on this branch

The scaffolding is well built; the flaw is in the statement being proved, not in the coding.

**Correct and worth keeping**

* Two-round structure: statement values in round 1, accumulators in round 2 with `z` folded into
  the second commitment. This is exactly the ordering Theorem 2 requires, and it is the part most
  implementations get wrong.
* Clean separation of `rlcDeferredChecker` from the legacy path; custom-modulus and
  extension-field checks correctly excluded.
* Horner fold `lhsAcc = lhs[i] + z·lhsAcc` and the `xPowers[i] = x^{i+1}` convention agree with
  `evalWithChallenge`.
* Sign handling for `mvCheck` folds `s_k` into the accumulator consistently on both sides.

**Findings**

1. **(Critical) `kAcc` is unconstrained.** `callDeferredChecksRLCHint` returns
   `f.newInternalElement(ret[:maxKLen], 0)`; nothing ties it to any `k_i`. This is Theorem 1.
   Aggregating the quotient must be abandoned; only the carry aggregation is recoverable.
2. **(Critical) The retained `k_i` range checks are dead weight.** `callMulHint` still emits them,
   so the branch pays the full cost of a check it has disabled. Whichever way the design goes,
   this must be resolved deliberately.
3. **(Correctness, latent) Cached evaluation of `f.Modulus()` is shared across paths.**
   `f.Modulus()` returns a `sync.Once`-cached element. The RLC path evaluates it at `x` and
   resets `pval.evaluation`/`isEvaluated` afterwards; the legacy path evaluates it at the
   multicommit challenge and never resets. `multicommit` gives each callback a *distinct* power
   of one root commitment, so the two paths evaluate at different points. Today the ordering
   saves it — `scheduleRLCDeferredChecks` is registered first and cleans up after itself — but
   the invariant is unwritten and one reordering away from a stale-evaluation bug in any circuit
   that mixes custom-modulus and regular operations. Reset symmetrically in both paths.
4. **(Hygiene) `kAcc`/`cAcc` declare `overflow = 0`** while holding full-width `F_q` values. Only
   safe because they are exclusively evaluated; mislabelled for any future reuse.
5. **(Hygiene) `mvCheck.kNeg` is omitted from `rlcToCommit`.** Moot while `K` is free, but under
   any repair `kNeg` is a prover-chosen bit that must be bound in round 1.
6. **(Test) `TestDeferredChecksRLC` cannot detect this class of bug.** It perturbs the
   accumulator and expects failure, which tests completeness of the identity, not binding. A
   soundness test must construct a *self-consistent* witness for a false statement, as
   `TestForgeRLCAggregation` does. Any future aggregation work should be gated on that test.
7. **(Cost) The second `committer.Commit` is an extra commitment per circuit**, with a Groth16
   commitment key and per-variable PLONK cost. Already included in the measured numbers, but it
   eats into the smaller saving that the sound variant will deliver.

---

## 8. Recommendations

1. Drop the quotient accumulator. Restrict the aggregation to carries (§5.3), which is provable
   and keeps roughly half the measured saving.
2. Gate the feature on a soundness test of the `TestForgeRLCAggregation` form, on a
   parameterisation such as `M127` where the per-check quotient bound is binding.
3. Fix finding 3 regardless of the outcome, as it is independent of the aggregation.
4. If the quotient saving is worth pursuing, the prerequisite is to convert the baseline's
   magnitude argument into a divisibility argument (range-checked carries lift (1) to `Z[X]`).
   That is a change to the *baseline* check and should be designed and costed on its own.

---

## Appendix A: reproduction

```
go test ./std/math/emulated/ -run TestForgeRLCAggregation -v
```

Constructs the Theorem 1 forgery against the branch's aggregation on `M127` and reports whether
the constraint system accepts `a*b = a*b + 1 mod p`.

## Appendix B: a separate observation on the baseline quotient budget

Independently of the RLC work, §2.3 shows the baseline's binding rests on the range checks
forcing `|a·b - r - k·p| < q/2`. Whether the budget `callMulHint` grants the quotient
(`n_k·w` bits) is tight enough for that inequality is a property of the *baseline* and of the
emulation parameters, and deserves its own analysis. Nothing in §5 depends on the answer:
Theorem 1 holds for every parameterisation, and Theorem 2 reduces the aggregate exactly to the
per-check statement, whatever that statement is worth. This is deliberately not developed here —
see the accompanying note to the maintainer.
