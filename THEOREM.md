# Exact division by an invariant floating-point divisor: statements and proofs

Revision 4 (2026-11-10): revision 2 applied the first referee pass (changes in §5); revision 3 added the Lean
model of IEEE arithmetic and machine-checked Theorem B items 1–3 in it; revision 4 defines round-to-nearest-even
in Lean, verifies the per-divisor check (closing the numerically cleared candidates), and states the whole
algorithm of `exact_fdiv.h` in Lean with one end-to-end theorem, `efd_correct` (§4).

Status of each statement is given in its heading: **Lean** (kernel-checked, see `lean/`), **paper** (proved
below by hand), **exhaustive** (checked on every input of a finite domain), **native** (run on hardware).
Counts and file names for the tests are in `FINDINGS.md`.

The algorithm is not ours: it is "Algorithm 2" of Brisebarre, Muller and Raina, *Accelerating correctly rounded
floating-point division when the divisor is known in advance*, IEEE Trans. Computers 53(8), 2004 (BMR), and the
per-divisor decision procedure of §1 (corollaries A1, A2) is their Theorem 2 / Algorithm 3 in another form. BMR
work in a model with unbounded exponent range and no special values. Theorem A re-proves the unbounded statement
in a form suited to machine checking; Theorem B carries it to IEEE-754 formats with subnormals, signed zeros,
infinities, NaN and overflow, which is the part we could not find in the literature.

## 0. Setting

Radix 2, precision `p ≥ 2`. `F_p` is the set of rationals `m·2^e` with integers `m, e`, `|m| < 2^p` (unbounded
exponent). `f` is *a nearest float of* a real `t` if `f ∈ F_p` and `|t − f| ≤ |t − g|` for every `g ∈ F_p`.
No tie-breaking rule is assumed anywhere in Theorem A.

Algorithm 2 for a divisor `y ≠ 0`:

    setup:      zh = a nearest float of 1/y            zl = a nearest float of 1/y − zh
    per x:      t1 = a nearest float of x·zl           q2 = a nearest float of x·zh + t1

(`q2 = fma(x, zh, x*zl)` in C.) The claim to decide is `q2 = RN(x/y)`.

## 1. Theorem A (unbounded exponent) — **Lean**: `ExactFDiv.alg2_core`

Let `X, Y` be integers with `2^(p−1) ≤ X, Y < 2^p`, and let `zh, zl, t1, q2` be as above for `x = X`, `y = Y`.
Let `q` be any nearest float of `X/Y`. If

* `Y ≤ X`, **or**
* there is no integer `B` with `X·2^(p+1) − B·Y = +1` or `= −1`,

then `q2 = q`. (In Lean the disjunction is `Admissible p X Y`.)

*Proof.* Write `P = 2^p`, `a = 1/P`, `b = 1/Y`; so `a < b ≤ 2a` and `1/2 ≤ Xa < 1`.

*Error bound* (`ExactFDiv.err_bound`). `b ≤ 2a = P·2a²`, so `|b − zh| ≤ a²` (half a unit of the binade of `b`).
Hence `|b − zh| ≤ P·a³` and `|b − zh − zl| ≤ a³/2`; also `|zl| ≤ a²` because `a²` is a float and a nearest float
never jumps over a float. Then `|X·zl| ≤ P·a²`, so `|X·zl − t1| ≤ a²/2`. With `s = X·zh + t1`,

    |s − X/Y| ≤ X·|b − zh − zl| + |X·zl − t1| ≤ X·a³/2 + a²/2 < a².                         (1)

*Case `Y ≤ X`* (`finish_ge`). `1 ≤ X/Y < 2`, so `1 ≤ q ≤ 2` and `q = k·2a` for an integer `k`,
`P/2 ≤ k ≤ P`, with `|X/Y − k·2a| ≤ a`. The two neighbouring rounding breakpoints are `(2k ± 1)·a`, and

    X/Y − (2k ± 1)a = (X·P − (2k ± 1)·Y) / (Y·P).

The integer numerator is not zero (it would give `2^p | Y`, impossible for `0 < Y < 2^p`, because `2k ± 1` is
odd). So it is `≤ −1` for the upper breakpoint and `≥ 1` for the lower one, i.e. `X/Y` stays at distance
`≥ 1/(YP) = ab > a²` from both. By (1), `|s − k·2a| < a`, strictly inside the rounding interval of `k·2a`, and
when `k = P/2` (the binade boundary `1`), `s − 1 > −a² ≥ −a/2`, a quarter of the grid step. Lemma U below gives
`q2 = k·2a = q`.

*Case `X < Y`* (`finish_lt`). `1/2 < X/Y < 1`, `q = k·a` with `P/2 ≤ k ≤ P`, breakpoints `(2k ± 1)·a/2`, and

    X/Y − (2k ± 1)a/2 = (X·2P − (2k ± 1)·Y) / (2·Y·P).

The numerator is not `0` (same parity argument with `2^(p+1)`) and by hypothesis not `±1`, so it is `≤ −2`,
resp. `≥ 2`: distance `≥ 2/(2YP) = ab > a²` again, and at `k = P/2`, `s − 1/2 > −a² ≥ −a/4` (this is where
`p ≥ 2` is used). Lemma U gives `q2 = k·a = q`. ∎

**Lemma U (unique nearest)** — **Lean**: `ExactFDiv.nearest_unique`. Let `u = 2^e`, `k` an integer with
`2^(p−1) ≤ k ≤ 2^p`, `|t − k·u| < u/2`, and `t − k·u > −u/4` if `k = 2^(p−1)`. Then every nearest float of `t`
is `k·u`. (Floats that are `≥ 2^(p−1)·u` are integer multiples of `u`; just below the binade boundary the grid is
`u/2`, which is why the extra condition is needed there.)

### Corollaries of Theorem A

**A3 (general floats)** — **Lean**: `ExactFDiv.alg2_float`. Theorem A holds for all `x = ±X·2^i`,
`y = ±Y·2^j` (any signs, any integer exponents), by the invariance of "nearest" under negation and scaling by
powers of two (`IsNearest.neg`, `IsNearest.scale`).

**A1 (even significand; BMR Theorem 2, condition 1)** — **Lean**: `ExactFDiv.alg2_even`. If `Y` is even,
Algorithm 2 is correct for every nonzero `x`. (`X·2^(p+1) − B·Y` is even.) Covers every divisor with at most
`p − 1` significant bits: all integers below `2^52` and all binary32 values used as binary64 divisors; `255.0`,
`3.0`, `1000.0`, `1e9`, `60.0`, `0.75`, …

**A2 (the per-divisor check; BMR Algorithm 3)**. For odd `Y`:

* for each sign `s ∈ {+1, −1}` at most one `X ∈ [0, Y)` satisfies `X·2^(p+1) = B·Y + s` for some `B`
  (**Lean**: `candidate_unique`); it is `X_s = s·(2^(p+1))^(−1) mod Y`;
* `X₊ + X₋ = Y` (**Lean**: `candidates_sum`), so at most **one** of the two lies in `[2^(p−1), Y)`
  (two numbers `≥ 2^(p−1)` cannot sum to `Y < 2^p`). Call it the candidate `X₀` of `Y`, if it exists.
  That a rejected divisor fails on at most one dividend significand is already stated by BMR (after their
  Algorithm 2 and in the discussion of Algorithm 3); the Lean lemmas are a machine-checked proof of it, not a
  new observation.

Consequently, for an odd `Y`: every `X ≠ X₀` is admissible, and Theorem A applies to it. The decision for the
divisor is completed by **one evaluation** of the kernel at a float with significand `X₀`, compared with the
correctly rounded quotient. If it agrees, Algorithm 2 is correct for every `x` (unbounded model); if not, `X₀` is
the only significand on which it fails. Soundness of an accepted odd divisor therefore rests on: Lean (all
`X ≠ X₀`), plus one numerical evaluation at `X₀` (hardware arithmetic in `efd64_bad_significand`, exact rational
arithmetic in `src/checker.py`), plus the invariance of *round-to-nearest-even* under sign change and scaling
(**paper**; it carries the evaluation from the tested exponent to all exponents). **Exhaustive**: the check
equals a brute-force scan over all `X` for every `Y`, `p = 3..12`.

**A4 (integer dividends — the compiler corollary)** — **paper**; **exhaustive** for the instances listed in
`FINDINGS.md`. Let `C` be a floating-point constant accepted by the setup of Theorem B (conditions S1, S2 and the
significand check S3), in the default rounding mode and without strict floating-point exception semantics. Let
`x` be the conversion of an integer of a type whose every value is exactly representable, with at most `r`
significant bits. Then `x / C` and `fma(x, zh, x·zl)` are the same floating-point value for every `x`, provided

1. `max |x| < thi` (Theorem B). This holds automatically for `i8/i16/i32/u32 → binary64` and
   `i8/i16/u16 → binary32` (the smallest possible `thi` is `2^54`, resp. `2^25`); for wider integers it is a
   condition on `C` (it fails only for extremely small `|C|`, e.g. `C = 0x1.4p-1022`, `x = 2^62`: the kernel
   gives `−∞`, the quotient is `+∞`);
2. no lower guard: S2 forces `tlo ≤ 1/2`, and a nonzero integer has `|x| ≥ 1`;
3. `x = 0` (always `+0` after an integer conversion): both forms give `+0` when `C > 0`; when `C < 0` the
   quotient is `−0` and the kernel returns it only if `zl` and `zh` have the same sign (else the fold needs `nsz`).

Moreover S3 can be weakened: the significand of such an `x` has at least `p − r` trailing zero bits, so a
constant *rejected* by the check is still safe when its candidate `X₀` has fewer than `p − r` trailing zeros
(for `i32 → binary64`, fewer than 21) — which is the case for all but a fraction of about `2^(−21)` of the
rejected constants. Integer types wider than the significand (`i64 → binary64`) are not covered by this
weakening: their conversion rounds, and the converted value can have any significand.

## 2. Theorem B (IEEE-754 formats) — **Lean** for items 1–3 in a model of IEEE arithmetic (`kernel_eq_div`, `kernel_special`, `kernel_inf_opposite`, `kernel_zero_opposite`, `mul_inv_eq_div`; see §4 for what the model covers); flags **paper**; **exhaustive** on toy formats; **native**

Format: precision `p`, floats `±m·2^e` with `emin ≤ e ≤ emax`, `m < 2^p`; subnormals at `e = emin`; `±0`, `±∞`,
NaN; round-to-nearest-even; operations `⊗`, `⊘`, `fma` correctly rounded with the IEEE special-value rules.
`λ = 2^(emin+p−1)` is the smallest positive normal number. **Assume `emin ≤ 1 − 2p`** (true for binary16, 32, 64
and 128; without it the statement is false — the referee exhibits a `p = 4`, `emin = −6` format where `ρ` below
is not representable).

Let `y` be finite, normal, and let (computed in the format)

    zh = 1 ⊘ y,     ρ = fma(−y, zh, 1),     zl = ρ ⊘ y.

Assume (S1) `zh` is normal, (S2) `ρ = 0` or `|zl| ≥ 2λ`, (S3) the significand of `y` passes the check of A2.
If `ρ ≠ 0`, let `tlo`, `thi` be floats with `tlo·|zl| ≥ λ` and `thi·|zl| ≤ 2^(emax+p−1)` (`thi = +∞` allowed
when `|zl| ≤ 1`). Then:

1. **(fast range)** for every finite `x` with `tlo ≤ |x| < thi`:  `fma(x, zh, x ⊗ zl)` and `x ⊘ y` are the same
   floating-point datum, including the case where both overflow to the same infinity. Neither computation
   raises *underflow*, and they raise *overflow* together. The *inexact* flag is **not** preserved (the kernel
   raises it for `3/3`); *invalid* and *division-by-zero* are raised by neither.
2. **(power of two)** if `ρ = 0` then `y` is a power of two and `x ⊗ zh = x ⊘ y` for *every* `x` of the format.
3. **(specials)** for `x ∈ {±0, ±∞}`, `x ⊘ y` is `x` with its sign multiplied by `sign(y)`. If `zl` and `zh`
   have the same sign the kernel returns that value for all four. If they have opposite signs the kernel is
   wrong exactly for the zero whose quotient is `−0` (it returns `+0`) and for both infinities (it returns NaN).
   For NaN `x` both sides are NaN (sign and payload are not compared anywhere in this repository).
4. **(guards are necessary in general)** witnesses in §3.

*Proof of 1.* (i) `ρ = 1 − y·zh` exactly. With `2^E ≤ |y| < 2^(E+1)`: `ulp(y) = 2^(E−p+1)`,
`ulp(zh) ≥ 2^(−E−p)`, so `1 − y·zh` is an integer multiple of `2^(1−2p) ≥ 2^emin`, and
`|1 − y·zh| = |y|·|1/y − zh| ≤ 2^(E+1)·2^(−E−p−1) = 2^(−p)`: at most `p` significant bits above `2^(1−2p)`, hence
representable, and `fma` returns it. So `zl = RN((1 − y·zh)/y) = RN(1/y − zh)` in the format.
(ii) *Bridge* (**Lean**: `IsNearestB.toNearest`): for a real `t` with `|t| ≥ λ` (or `t = 0`), a nearest float of
the format (ignoring `emax`) is a nearest float in `F_p`. (iii) `|1/y| ≥ λ`: otherwise `|y| > 1/λ`, hence
`|y| ≥ (1 + 2^(1−p))/λ` (next float), `1/|y| < λ − 2^(emin−1)`, and `zh` would be subnormal, contradicting S1.
(iv) `|zl| ≥ 2λ` gives `|1/y − zh| ≥ λ` by monotonicity of rounding (a real below `λ` cannot round to `≥ 2λ`).
(v) For `|x| ≥ tlo`: `|x·zl| ≥ λ`, so `t1 = x ⊗ zl` is a nearest float in `F_p` of `x·zl`; for `|x| < thi` it
does not overflow. (vi) Because `|zl| ≤ 2^(−p)·|zh|·(1 + 2^(1−p))` (it is the rounding of a quantity of magnitude
at most half an ulp of `zh`), `|x·zh| ≥ (2^p − 1)·|x·zl|`, so `|s| = |x·zh + t1| ≥ λ` and `|x/y| ≥ λ` with a
wide margin. (vii) By (ii)–(vi) the five roundings are nearest roundings in `F_p` (this is exactly
**Lean** `alg2_bounded`, whose five range hypotheses are (iii)–(vi)); Theorem A with A2/A3 gives that `s` and
`x/y` have the same round-to-nearest-even value `q` in `F_p`. (viii) IEEE defines the result of an operation
whose exact value has magnitude `≥ λ` as that unbounded-exponent rounding if it does not exceed the largest
finite float, and the infinity of the same sign otherwise; since the unbounded roundings of `s` and `x/y`
coincide, so do the IEEE results. (ix) Flags: no result or intermediate is tiny, so underflow is not raised by
either side; overflow is raised by the final `fma` iff `|q|` exceeds the largest float iff the division raises
it; `x ⊗ zl` does not overflow by (v). ∎

*Proof of 2.* `ρ = 0` means `y·zh = 1` with both factors floats, which forces both significands to be powers of
two; then `x·zh = x/y` as reals, both sides round the same real, and special values propagate identically
through a multiplication by a power of two of the same sign as `y`.

*Proof of 3.* IEEE sign rules: `x ⊗ zl` is a zero (resp. infinity) of sign `sx·s(zl)`; `fma` adds it to the
exact zero (resp. infinite) product of sign `sx·s(zh)`. Equal signs give that sign; opposite signs give `+0` in
round-to-nearest (correct only when the quotient is `+0`) and `∞ − ∞ = NaN`.

**Looser threshold** — **paper**, **exhaustive** on toy formats (`loose` runs, with the bound rounded up to a
power of two). Value equality (not underflow-flag equality) holds already for `|x/y| ≥ 2^(emin+2p)`: writing
`x/y = (X/Y)·2^m`, the budget for the error of `t1` in (1) is `2^(m−2p−1)`; a subnormal product errs by at most
`2^(emin−1)`; and `|x/y| ≥ 2^(emin+2p)` forces `m ≥ emin + 2p`.

## 3. Where it fails — **native** (binary64, hardware fma; `results/native_witnesses_binary64.txt`)

| violated hypothesis | y | x | kernel | x / y |
|---|---|---|---|---|
| `|x| ≥ tlo` (tlo = 2^−964) | 10 | `0x0.0000000003f39p-1022` | `…653p-1022` | `…652p-1022` |
| `|x| ≥ tlo` (tlo = 2^−966) | 3 | `0x1.abe96e4b06ce6p-1021` | `0x1.1d46498759deep-1022` | `…defp-1022` |
| `|x| ≥ tlo` (tlo = 2^−958) | 255 | `0x1.1a207cc667e97p-1017` | `0x0.2367770fdcda0p-1022` | `…da1p-1022` |
| `|x| ≥ tlo` (tlo = 2^−971) | 0.1 | `0x0.a8ea3291e952ap-1022` | `0x1.a6497e6cc74e8p-1020` | `…4e9p-1020` |
| equal signs, `x = −0` | 10 | `−0` | `+0` | `−0` |
| equal signs, `x = +∞` | 10 | `+∞` | NaN | `+∞` |
| `|x| < thi` (thi = 2^80) | `0x1.4p-997` | `2^1000` | `−∞` | `+∞` |
| S3 (significand check) | `0x1.ee635506bf2efp+52` | `0x1.4540e56da1dacp+52` | `0x1.50d71be07be08p-1` | `…e07p-1` |
| S2 (`zl` underflowed) | `0x1.8p+1020` | `0x1.15ba2177219d3p+23` | `0x1.724d81f42cd1ap-998` | `…d19p-998` |
| S1 (`zh` subnormal) | `0x1.8p+1023` | `0x1.e4f40a499abe6p+1013` | `0x1.434d5c3111d43p-10` | `…d44p-10` |

(The last two rows were found by the referee.) The guards are necessary *in general*, not for every divisor:
for extremely small divisors such as `y = 0x1.8p-1022` the setup gives `tlo = 2^−1074`, so every finite nonzero
`x` is in range and the bare kernel is right on all of them. For ordinary divisors `tlo` is about
`2^(emin+2p)·|y|` (`4·10^−292·|y|` in binary64, `10^−30·|y|` in binary32) and inputs below it are where the
bare kernel can fail, as in the first four rows. S1 and S2 are sufficient conditions; we do not claim the kernel
fails for every divisor that violates them.

## 4. What is and is not machine-checked

**Lean 4 + Mathlib (no `sorry`, no `native_decide`, no added axioms; 39 audited theorems in
`results/lean_axioms_audit.txt`, all depending only on `propext`, `Classical.choice`, `Quot.sound`).**

*Unbounded exponent* (`Basic`, `Main`, `General`): `IsFloat`, `IsNearest`, invariance under negation and scaling,
the grid lemma, the half-ulp bound, Lemma U (`nearest_unique`), Theorem A (`alg2_core`), A3 (`alg2_float`),
A1 (`alg2_even`), candidate uniqueness and the single-candidate lemma (`candidate_unique`, `candidates_sum`,
`candidates_not_both`).

*Formats with gradual underflow* (`Bounded`): the bridge `IsNearestB.toNearest` and `alg2_bounded`.

*IEEE model* (`IEEE`, `Setup`, `Final`, `Exists`, revision 3): an inductive type of IEEE data (NaN, signed
infinities, signed zeros, finite numbers) with `mul`, `div` and `fma` following the IEEE-754 special-operand rules
and the round-to-nearest sign rule for exact-zero sums; finite nonzero results go through a rounding function `R`
about which only `RoundSpec` is assumed (some nearest float of the format with gradual underflow; total underflow
gives a zero with the sign of the exact value; overflow is decided on the unbounded-exponent rounding and gives
the infinity of its sign). Proved in that model:

* `kernel_eq_div` (Theorem B item 1): if `emin ≤ 1 − 2p`, `emax ≥ 0`, `zh = 1 ⊘ y` is normal,
  `zl = fma(−y, zh, 1) ⊘ y` is a number with `|zl| ≥ 2λ`, the significands are admissible, and
  `λ ≤ |x·zl| ≤ maxFloat`, then `fma(x, zh, x ⊗ zl)` and `x ⊘ y` are the same IEEE datum — finite and
  equal, or the same infinity. The exactness of `ρ` (`setup_abs`) and the normal-range lemma for `1/y`
  (`inv_ge_minNormal`) are proved, not assumed; so are the five range conditions that `alg2_bounded` needed.
  `kernel_eq_div_even` drops the admissibility hypothesis for even significands.
* `kernel_special` (item 3): for `x` a zero, an infinity or NaN, and `zh`, `zl`, `y` of equal sign, the kernel
  equals `x ⊘ y`; `kernel_inf_opposite`, `kernel_zero_opposite`: with opposite signs it returns NaN for both
  infinities and `+0` for both zeros.
* `mul_inv_eq_div` (item 2): if `y·zh = 1` exactly, `x ⊗ zh = x ⊘ y` for every `x`, whatever `R`; and
  `rho_computed`: with `zh` the computed normal reciprocal, the computed `fma(−y, zh, 1)` is a zero iff
  `y·zh = 1`, and otherwise the exact residual — so the C test `rho == 0.0` is exactly the hypothesis.
* `guards_imply`, `guards_imply_noupper`: the C guards (`tlo·|zl| ≥ λ`, and `thi·|zl| ≤ maxFloat` or no upper
  guard with `|zl| ≤ 1` and `x` finite) imply the range hypothesis of `kernel_eq_div`.
* `exists_nearestB`, `exists_round`: nearest floats and a rounding function satisfying `RoundSpec` exist, so the
  hypotheses are not vacuous. Round-to-nearest-even is one such rounding (any tie rule is allowed).

*Revision 4* (`RNE`, `Checker`, `Algorithm`):

* `rhe` (round to nearest integer, ties to even), `rne` (round-to-nearest-even into the format with gradual
  underflow) and `rneR` (the IEEE result with overflow to infinity and a signed zero on total underflow);
  `rne_nearest`, `rhe_tie`, **`rneR_spec`: round-to-nearest-even satisfies `RoundSpec`**.
* `accept p Y`, a computable per-divisor check that evaluates the kernel *exactly* at the single candidate
  significand, and **`accept_sound`**: if it returns true, the round-to-nearest-even kernel equals the
  round-to-nearest-even quotient for every `x` and every sign and exponent of `y` — the candidate included.
* `efdSetup` and `efdDiv`, the *scalar reference* of `native/exact_fdiv.h` (`efd64_setup`/`efd64_div` and the
  binary32 twins) written in the model with the same branch structure (normal `y`; normal `zh`; `ρ == 0` → multiply; `|zl| ≥ 2λ`; the check; `tlo`, `thi` from the binary
  exponent of `zl` as the C's `frexp` code computes them; specials and out-of-range `x` divide), and
  **`efd_correct`: `efdDiv (efdSetup y) y x = div x y` for every datum `x`, `y` of the format** — NaN, infinities,
  zeros, subnormals and overflow included; instances `efd_correct_binary64`, `efd_correct_binary32`.

**Limits of the Lean part** (do not overstate):

* exception flags and NaN payloads are not modelled;
* the model is written for this proof; it was checked against IEEE 754-2019 by hand and by two independent
  (agent) readings, and its rounding was compared with hardware division on 4 000 binary64 pairs including
  subnormal, underflowing and overflowing quotients (0 disagreements, `results/lean_correspondence.txt`); nothing
  connects it formally to hardware or to bit patterns;
* `efdSetup`/`efdDiv` mirror the C, but the C source is not verified: the correspondence of its arithmetic (the
  modular inverse, the candidate, the `frexp` thresholds) with the Lean definitions rests on reading and on a
  differential test of the check (6 000 divisors, 0 disagreements);
* everything assumes hardware `mul`, `div`, `fma` are IEEE operations with round-to-nearest-even, no excess
  precision and no flush-to-zero/denormals-are-zero modes (`native/exact_fdiv_env.h` checks these at run time);
* the AVX2 array kernels of `native/efd_kernels.h` (bit-level guards, special-lane blend, zero fix) are not
  modelled; they are covered by exhaustive and sampled tests against scalar division only;
* third referee pass (fresh agent, on `RNE`, `Checker`, `Algorithm`): no fatal finding; it checked `rneR`
  against IEEE ties-to-even on hand-picked ties, binade tops, the overflow threshold and subnormal ties; gave a
  paper argument that `accept` and the C check compute the same candidates for every `Y` (and tested it on all
  4 194 304 odd binary32 significands and 100 002 binary64 ones); and compared Lean `efdSetup` with C `efd64_setup`
  on 1 550 divisors (mode, `zh`, `zl`, `tlo`, `thi` identical). Its suggestion for closing the C link further — an
  `acceptIEEE` that runs the check with the model's own operations and a word-level model of the Newton inverse,
  proved equal to `accept` — is not done.

**Paper + tests only:** the flag statements, the looser threshold, corollary A4, and "y·zh = 1 implies y is a
power of two" (not needed: the theorem uses `y·zh = 1` directly).

**Second referee pass on the Lean model** (fresh agent, compiled its own test instances): no fatal finding;
the model's `mul`, `div`, `fma` match IEEE 754-2019 case by case on special operands, `RoundSpec` is a correct
over-approximation of roundTiesToEven, and the hypotheses of `kernel_eq_div` are jointly satisfiable (a toy
instance was discharged in Lean). Applied: the upper range hypothesis was `|x·zl| ≤ 2^(p−1)·2^emax`, which
left fast-path inputs of the C code uncovered when `1/2 ≤ |zl| < 1` (e.g. `y = 0x1.8p-54`, `x = DBL_MAX`; the
answer is right there, but was not proved) — now `≤ maxFloat`, which covers every input the C sends down the
fast path; the special-value theorems could be instantiated with the junk value `num 0` and now assume
nonzero operands; `0·b + w` in `fma` now rounds `w`; the exponent convention is documented; the glue lemmas
`guards_imply*` and `rho_computed` were added.

## 5. Changes in revision 2 (referee findings applied)

A4 gained its upper-range condition and the precise list of integer types, lost a wrong parenthesis about `tlo`,
and its `2^(−21)` sentence was inverted; Theorem B now states `emin ≤ 1 − 2p`, defines `tlo`/`thi` only for
`ρ ≠ 0`, no longer says "iff" for the special values, and states which flags are and are not preserved; proof
steps (iii), (iv), (vi), (viii) were missing; the claim that the bare kernel fails for *every* non-power-of-two
divisor was false and is withdrawn; the "at most two candidates" of A2 is sharpened to one; witness rows for S1
and S2 added; §4 rewritten with the limits of the Lean part; evidence counts moved to `FINDINGS.md`.
