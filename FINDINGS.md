# Exact division by an invariant floating-point divisor — findings

Mathematics in [THEOREM.md](THEOREM.md), commands in [REPLAY.md](REPLAY.md), raw outputs in [results/](results/).
Work of November 2026; see the README for provenance and review status.

## 1. The problem in one paragraph

`array / scalar` and `x / constant` are everywhere, and a floating-point divide costs 8–30 times a multiply.
Multiplying by the reciprocal changes results (`49.0 / 49.0` becomes `0.9999999999999999`), so software that
promises IEEE results pays for the divide (NumPy, Eigen, arrow-rs, DuckDB, every compiler without fast-math),
and software that wants the speed ships the inexact reciprocal and takes the bug reports (Polars today, XLA,
PyTorch on CUDA). A 2004 paper (Brisebarre, Muller, Raina) shows that one multiply plus one fused multiply-add,
`fma(x, zh, x*zl)`, gives the *correctly rounded* quotient for about 98.7 % of divisors, decidably per divisor —
but only in an idealised model with no underflow, overflow, zeros or infinities, and nobody ships it: CompCert's
authors name the rewrite and decline it because it fails "when x is small"; LLVM, GCC, Go and HotSpot fold only
power-of-two divisors. What was missing is the fact a consumer needs: **exactly when the fast form is the same
IEEE value as the division, for real formats, with a proof.** This repository supplies that and measures what it buys.

## 2. What was established

| # | statement | status |
|---|---|---|
| 1 | Unbounded-exponent correctness of the mul+fma kernel with the exact failure characterisation (Theorem A), for every nearest rounding, all signs and exponents; even significands always work; at most one candidate significand per divisor | **Lean 4 + Mathlib**, no `sorry`/`native_decide`/added axioms (`lean/`) |
| 2 | Bridge to formats with subnormals: outside the subnormal range, rounding in the format is rounding in the unbounded model; Theorem A in such a format under five explicit range hypotheses | **Lean** (`IsNearestB.toNearest`, `alg2_bounded`) |
| 3 | Full IEEE statement (Theorem B): for a divisor accepted by a 3-condition setup, the kernel equals `x / y` for every finite `x` with `tlo ≤ |x| < thi` (overflow included, underflow/overflow flags equal, inexact not preserved); exact behaviour on `±0`, `±∞`, NaN; power-of-two divisors exact for every `x` | **Lean** in a model of IEEE arithmetic for the values (`kernel_eq_div`, `kernel_special`, `mul_inv_eq_div`; setup exactness proved, rounding spec shown satisfiable); flags paper; exhaustive on toy formats; native tests |
| 4 | Each guard is necessary in general: ten binary64 witnesses where the unguarded kernel is wrong | native |
| 5 | Compiler corollary (A4): `fdiv (sitofp i32 x), C` equals the kernel with no guard for every accepted constant, and for rejected constants whose candidate cannot be a 32-bit integer's significand | paper; exhaustive over all 2^32 `int32` for the tested constants |
| 6 | Reference implementation (`native/exact_fdiv.h`, binary64 and binary32), AVX2 kernels (`native/efd_kernels.h`), measured speed | native tests and benchmarks below |
| 7 | **The algorithm itself**: `efdSetup`/`efdDiv` (the scalar setup and guarded division of `exact_fdiv.h`, same branches, with a verified per-divisor check and round-to-nearest-even defined in Lean) return `x / y` for every datum `x`, `y` of the format — `efd_correct`, with binary64 and binary32 instances | **Lean**; Lean check = C check on 6 000 divisors; Lean rounding = hardware on 4 000 divisions |

Not ours: the algorithm, the double-word reciprocal, the unbounded-model decision procedure, the fact that a
rejected divisor fails on at most one dividend significand, the 98.7 % figure (BMR 2004); a binary32 checker (Reynolds 2019); the observation that tiny `x`, zeros and infinities break it
(Stack Overflow 35527683, CompCert JAR 2015). New here, as far as two literature/code scans could tell: the
machine-checked proof, the full-IEEE statement with explicit thresholds and its exhaustive/native validation, a
binary64 runtime check, guarded SIMD kernels with measurements, and the integer-dividend corollary.

## 3. Evidence

Every count below is in a file under `results/`; "kind" is, in decreasing strength: proof, machine-checked,
exhaustive (every input of a finite domain), native witness (a specific input run on hardware), sampled. Expected and observed mismatch count: 0 in
every row.

| claim | kind | evidence | file |
|---|---|---|---|
| Theorem A, A1, A3, candidate uniqueness, single candidate, bridge, bounded-format form; Theorem B items 1–3 in a Lean model of IEEE data and operations, setup exactness, existence of a rounding function | machine-checked | 39 theorems, axioms `[propext, Classical.choice, Quot.sound]` only; no `sorry`/`native_decide`; a deliberately false statement about the model is rejected | `lean_axioms_audit.txt` |
| per-divisor check = brute force (unbounded model) | exhaustive | every significand `Y` and every `X`, `p = 3..12`: 4 092 divisors, 44 rejected, 0 disagreements | `checker_vs_bruteforce.json` |
| the same, binary32, hardware | exhaustive in `X`, sampled in `Y` | 30 000 significands (28 125 odd) × all 2^23 `X`: 693 rejected, each with exactly the predicted single failing `X`; 0 disagreements | `native_f32_sigcheck_seed3.txt` |
| Theorem B, all of it (fast range, specials, fallbacks, overflow) | exhaustive on toy formats, exact rational model | every pair (x, y) of every value incl. ±0, ±∞, NaN for the supported y: p=5 (emin −24, emax 16): 1.42 M pairs, strict and loose thresholds; p=6 (−30, 20): 8.83 M, strict and loose; p=7 (−34, 22): 43.8 M, strict; p=8 (−24, 6): 41.4 M, strict (42 divisors rejected by the check) | `ieee_model_p*.json`, `.log` |
| the same, independent harness | exhaustive on 12 smaller formats (referee) | 0 mismatches whenever `emin ≤ 1 − 2p`; mismatches without it | referee report (transcript) |
| C reference `efd32_div` = `x / y` | exhaustive in x, sampled in y | all 2^32 dividends × 120 divisors (98 in FMA mode, 8 exact, 14 fallback): 5.15·10^11 comparisons; plus an earlier stopped run of 80 divisors | `native_f32_x_exhaustive_seed11.txt`, `…_partial80.txt` |
| C reference `efd64_div` = `x / y` | sampled, adversarial | 40 126 divisors, 2.23·10^9 comparisons in six families (random bits, thresholds, near-breakpoint, candidate significands, quotient edges, specials); all 538 significand rejections confirmed necessary | `native_f64_adversarial.txt` |
| AVX2 kernels = scalar division | exhaustive (binary32) and sampled | 5.23·10^11 elements: all 2^32 float patterns × 3 policies × 40 divisors, plus mixed arrays, all lengths 0..70, in place and out of place | `native_kernels.txt` (+ `native_kernels_p4.txt` for the final default policy) |
| overflow/underflow/invalid/div-by-zero flags equal in the fast range | sampled | binary64 14.4 M cases (321 509 overflowing), binary32 13.5 M (714 657 overflowing): 0 differences; inexact differs in 1 775 + 1 402 cases, as stated | `native_flags.txt` |
| guards necessary in general | native witness | 10 binary64 inputs, unguarded kernel wrong, guarded reference right | `native_witnesses_binary64.txt` |
| corollary A4 | exhaustive in x | all 2^32 `int32` values × 147 double constants (146 accepted by setup, 1 rejected-but-safe); all 2^16 `uint16` values × 199 974 float constants (5 005 rejected-but-safe) | `int_dividend_test.txt` |
| Lean algorithm ↔ C and hardware | differential | verified check `accept` vs `efd64/32_bad_significand`: 3 000 + 3 000 odd significands, 0 disagreements; model rounding vs hardware division: 4 000 binary64 pairs (551 subnormal results, 646 underflows to zero, 954 overflows), 0 disagreements | `lean_correspondence.txt` |
| same bits as a shipped consumer | sampled | NumPy 2.4.4 `np.true_divide(a, s)` vs the kernel through ctypes, 2 dtypes × 5 sizes × 5 data kinds × up to 6 divisors: identical bits in every configuration | `numpy_compare.json` |

Acceptance statistics (binary64, `native_f64_adversarial.txt`): of 20 000 random bit patterns 95.7 % get the
fast kernel, 1.27 % are rejected by the significand check, the rest are out of range (huge, subnormal, special);
of 20 000 divisors with ordinary exponents 98.6 % get the fast kernel and 1.42 % are rejected. Half of the
accepted divisors have `zl` and `zh` of equal sign (specials need no handling).

Known gaps in the evidence: the binary64 C reference is sampled, not exhaustive (it cannot be); the model's
`thi` is one binade looser than the C header's (the model therefore tests a slightly larger fast range than the
code uses); NaN sign and payload are never compared; nothing ran on a second machine or a non-x86 CPU.

## 4. What it buys (measured, one machine)

One laptop, Intel Core Ultra 7 155U (performance and efficiency cores, AVX2 + FMA), quiet machine, medians of
15 round-robin repetitions; full tables, method and loop disassembly in `native/BENCH.md`,
`results/bench_tables.md`. "div" is a `vdivpd`/`vdivps` loop with the same unrolling. The kernel is the final
default policy (P4): one add and one compare per vector as the guard, real division only for blocks containing a
finite nonzero element outside `[tlo, thi)`.

**Array kernel against a divide loop** (`y = 3`, ordinary data, out of place; speed-up = div time / kernel time):

| core, type | 256 | 4 096 | 65 536 | 1 Mi | 16 Mi elements |
|---|---|---|---|---|---|
| performance core, binary64 | 3.6× | 3.0× | 3.0× | 0.9× | 1.0× |
| performance core, binary32 | 1.05× | 0.7–1.45× | 1.45× | 1.0× | 1.0× |
| efficiency core, binary64 | 5.6× | 5.9× | 6.1× | 2.1× | 2.5× |
| efficiency core, binary32 | 2.2× | 2.5× | 2.5× | 2.5× | 1.1× |

In cache the binary64 divide is the bottleneck and the kernel removes it; out of cache on the performance core
memory is the bottleneck and nothing is gained. binary32 on the performance core is the weak case: `vdivps`
costs only 0.13 ns per element there, and `3.0f` is an opposite-sign divisor that needs the zero fix; a
same-sign binary32 divisor (`1e-3f`) measures 2.6× (0.051 ns against 0.134 ns).

**Data independence** (n = 4096, binary64, performance core, ns per element; normal / 10 % zeros / 1 % NaN /
0.1 % below `tlo` / integers 0..255):

| divisor | div | first design (P2) | final default (P4) |
|---|---|---|---|
| 3 (equal signs) | .43 .43 .42 .42 .42 | .14 **.82** .21 .15 .16 | .14 .14 .14 .15 .14 |
| 0.1 (opposite signs) | .42 .43 .43 .43 .42 | .14 **.82** .21 .15 .17 | .18 .19 .19 .19 .18 |

The first design was *slower than division* on data with 10 % zeros (its guard branch mispredicts). The final
one is flat: for equal-sign divisors zeros, infinities and NaN need no handling at all (Theorem B item 3), and
for opposite-sign divisors a two-instruction sign fix handles zeros; the price there is about 30 % over the
equal-sign case.

**Compiler fold (corollary A4)**, loops auto-vectorised by gcc with identical flags, outputs bit-identical
(`results/int_dividend_bench.txt`):

| loop | 1 024 | 16 384 | 262 144 | 4 Mi elements |
|---|---|---|---|---|
| `out[i] = (double)in_i32[i] / 1000.0` | 5.1× | 3.5× | 2.0× | 1.04× |
| `out[i] = (float)in_u8[i] / 255.0f` | 2.2× | 2.2× | 2.3× | 0.96× |

**Against a shipped consumer** (`results/numpy_compare.*`: NumPy 2.4.4 `np.true_divide(a, s, out=o)` and the
kernel called through ctypes in the same process, unpinned, best of several): the outputs have identical bits
in all 200-odd configurations. Speed-up over NumPy: binary64 1.4–1.7× at 1 024 elements, 1.7–2.1× at 4 096,
3.9–6.1× at 65 536 (NumPy measured 2.1 ns per element there, the efficiency-core divide speed, so the scheduler
had probably moved the process), 0.7–2.5× at 1 Mi, 0.6–1.1× at 16 Mi; binary32 1.4–1.8× up to 4 096, 2.3–2.6× at
65 536 and 1 Mi, about 1.1× at 16 Mi. This is a harness, not a NumPy patch, and the run-to-run spread on a hybrid
CPU is large.

**Cost of the checks.** Setup (two divisions, one fma, one modular inverse, at most one test evaluation) is
17–30 ns per divisor; setup plus kernel beats the divide loop from about 50–60 elements (binary64, performance
core). The guard roughly doubles the cost of the bare mul+fma in L1 (0.08 → 0.16 ns per element) and adds 6–10 %
at 65 536 elements. The kernel runs at 1.2–2.6 times the time of the *inexact* `x * (1/y)`, which is the
relevant comparison for the consumers that ship the reciprocal today.

**What the proof buys.** Nothing here is faster than what an engineer could write from the 2004 paper plus
tests; the point is that nobody ships it, and the stated reason (CompCert's authors, the Stack Overflow thread)
is the missing full-range statement. The baseline is therefore what consumers actually ship: the divide, or the
inexact reciprocal.

## 5. Independent review (AI agents, adversarial, read-only)

No error in Theorem A, the Lean files, or the binary64/binary32 behaviour of the C reference. Ten findings on
the write-up, all applied in THEOREM.md revision 2: the integer corollary lacked its upper-range condition (a
real counterexample for `i64` and tiny constants) and had one inverted sentence; Theorem B needed
`emin ≤ 1 − 2p` in its statement (false without it on a toy format); "the bare kernel fails for every
non-power-of-two divisor" was false (it is right for all finite nonzero `x` when the divisor is extremely
small); an "iff" on special values was wrong for the `+0`-quotient zero; the inexact flag was not mentioned;
four proof steps were missing; two evidence counts cited runs that had not finished; the list of what is
machine-checked was stale. The referee also contributed two witnesses (conditions S1, S2), the observation that
at most one candidate is ever in range (now a Lean lemma; BMR already state that a rejected divisor fails on at
most one dividend significand), and a 12-format exhaustive cross-check of Theorem B
with its own harness (0 mismatches whenever `emin ≤ 1 − 2p`).

Two further passes reviewed the Lean IEEE model and the end-to-end algorithm (THEOREM.md §4). The second found one
real coverage gap: the upper range hypothesis left some inputs the C sends down the fast path unproved, now
fixed. It also found that the special-value theorems could be instantiated with a junk value, now excluded. The
third found nothing fatal. It checked the rounding against IEEE ties-to-even on hand-picked edge cases, gave an
argument that the Lean and C checks compute the same candidates for every divisor (tested on all 4 194 304 odd
binary32 significands), and compared the Lean and C setups on 1 550 binary64 divisors. All reviewers were AI
agents (Claude), not people; **no human has audited the proofs.**

## 6. Limits (read before quoting anything)

* The Lean part states and proves the whole algorithm (setup, check, thresholds, guarded division) in a model of
  IEEE arithmetic written for this proof, with round-to-nearest-even defined in Lean. It does not cover exception
  flags, NaN payloads, or the C source itself: that the C computes what `efdSetup`/`efdDiv` compute rests on
  reading and on differential tests. See THEOREM.md §4.
* Round-to-nearest-even only; a correctly rounded `fma`; no excess precision. The inexact flag is not preserved,
  so the fold is not valid under strict floating-point exception semantics. NaN in gives NaN out; NaN sign and
  payload are not compared anywhere.
* About 1.3–1.4 % of random binary64 divisors are rejected by the significand check and about 3 % of random bit
  patterns for range reasons (huge `|y|`, subnormals); those fall back to real division. Each rejection in the
  sample was confirmed necessary.
* Speed: the gain is an in-cache gain. Once the array no longer fits in cache the kernel and the divide loop
  converge on the performance core. Newer cores have faster dividers (the scan lists 3.5–4 cycles per 256-bit
  divide on Arrow Lake and Zen 5 against 8 on this machine's generation), so the ratio will be smaller there.
  All timings are from one laptop (Core Ultra 7 155U); nothing was measured on AMD, Arm or AVX-512.
* No consumer has been asked. The integration measurements are a ctypes harness next to NumPy, not a NumPy
  patch, and the compiler corollary is demonstrated by hand-written loops, not an LLVM patch.
* Same-host replay only.
