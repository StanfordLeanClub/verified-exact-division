# Verified exact division by an invariant floating-point divisor

For a fixed divisor `y`, the quotient `x / y` can be computed without a divide instruction as

```c
q = fma(x, zh, x * zl);      // zh = RN(1/y), zl = RN(1/y - zh), computed once per divisor
```

which is the *correctly rounded* IEEE quotient for almost every divisor (Brisebarre, Muller and Raina, IEEE
Trans. Computers 2004). Nobody ships it: compilers only fold power-of-two divisors, and array libraries either pay
for the divide or ship the inexact `x * (1/y)`. The stated reason is that the 2004 theorem assumes an unbounded
exponent range with no zeros, infinities, subnormals or overflow.

This repository supplies the missing statement and a machine-checked proof of it:

* **a per-divisor check and input guards** under which the fast form is bit-identical to IEEE division,
  including signed zeros, infinities, NaN, subnormals and overflow;
* **a Lean 4 + Mathlib proof** that the whole scalar algorithm divides correctly in a model of IEEE-754 binary
  arithmetic with round-to-nearest-even (`efd_correct`, with binary64 and binary32 instances);
* **a C reference** (`native/exact_fdiv.h`), AVX2 array kernels (`native/efd_kernels.h`), exhaustive and
  adversarial tests against hardware division, and benchmarks.

## The headline theorem

[`lean/ExactFDiv/Algorithm.lean`](lean/ExactFDiv/Algorithm.lean) defines `efdSetup` and `efdDiv`. They have the
same branch structure as `efd64_setup` / `efd64_div` in [`native/exact_fdiv.h`](native/exact_fdiv.h): a normal
divisor, a normal high reciprocal, the power-of-two case, the per-divisor check `accept`, and the thresholds `tlo`
and `thi`. The theorem is:

```lean
theorem efd_correct {p : ℕ} (hp : 2 ≤ p) {emin emax : ℤ} (hemin : emin + 2 * (p:ℤ) ≤ 1)
    (hemax : 0 ≤ emax) (y x : IEEE) (hy : Valid p emin emax y) (hx : Valid p emin emax x) :
    efdDiv p emin emax (efdSetup p emin emax y) y x = div (rneR p emin emax) x y
```

For every datum `y` and `x` of the format, the guarded division returns exactly the IEEE quotient under
round-to-nearest-even. `efd_correct_binary64` and `efd_correct_binary32` instantiate it.

All 39 audited theorems depend only on `propext`, `Classical.choice` and `Quot.sound`. There is no `sorry`, no
`native_decide`, and no added axiom ([`results/lean_axioms_audit.txt`](results/lean_axioms_audit.txt)).

## What is and is not established

| claim | evidence |
|---|---|
| unbounded-exponent correctness and the exact failure characterisation (Theorem A) | Lean |
| full IEEE statement: fast range with overflow, special values, power-of-two divisors, exact setup residual | Lean, in a model of IEEE arithmetic written for this proof |
| round-to-nearest-even satisfies the model's rounding assumption | Lean (`rneR_spec`) |
| the per-divisor check is sound, including the one input significand that Theorem A cannot cover | Lean (`accept_sound`) |
| the Lean check agrees with the C check | 6 000 divisors, 0 disagreements |
| the Lean rounding agrees with hardware division | 4 000 binary64 divisions incl. subnormal, underflowing and overflowing results, 0 disagreements |
| the C reference equals `x / y` | all 2^32 binary32 dividends for 120 divisors; 2.2·10^9 adversarial binary64 cases |
| the AVX2 kernels equal scalar division | 8.8·10^11 elements, including all 2^32 binary32 patterns for 40 divisors |
| exception flags | overflow, underflow, invalid and division-by-zero agree on 27.9 M cases; **inexact is not preserved** |

**Not covered by Lean:**

* the C source itself (it mirrors the Lean definitions; the link rests on reading and on differential tests);
* the AVX2 layer;
* exception flags and NaN payloads;
* bit-pattern encodings.

The review so far was done by AI agents, not people: three adversarial passes, all findings applied.
**No human has audited the proofs yet.** See [THEOREM.md](THEOREM.md) §4 for the precise boundary.

## Speed (one laptop: Intel Core Ultra 7 155U, AVX2)

The array kernel is 3.0–3.6× faster than a `vdivpd` loop in cache on a performance core, and 5.6–6.1× on an
efficiency core, for binary64. Once the array is memory-bound on the performance core there is no gain. binary32
gains less, because `vdivps` is already fast. Compiler-style loops of the form `(double)int32 / 1000.0` are 2–5×
faster in cache. Full tables are in [FINDINGS.md](FINDINGS.md) §4 and [native/BENCH.md](native/BENCH.md).
Nothing was measured on AMD, Arm or AVX-512.

## Prior art

The algorithm is not new.

* **Brisebarre, Muller and Raina (2004):** the double-word reciprocal, the decision procedure in the unbounded
  model, the fact that a rejected divisor fails on at most one dividend significand, and the 98.7% figure.
* **Reynolds (2019):** a binary32 checker.
* **Stack Overflow 35527683 (2016)** and **Boldo, Jourdan, Leroy and Melquiond (JAR 2015, §6.2):** the
  failure modes for tiny inputs, zeros and infinities.

What is new here, as far as our literature and code searches found, is the full-IEEE statement with explicit
guards, its machine-checked proof, the verified per-divisor check, the guarded SIMD kernels, and the
measurements. See [FINDINGS.md](FINDINGS.md) §2.

## Layout

```
lean/         Lean 4.32.1 + Mathlib v4.32.1 development (ExactFDiv/*.lean; Audit.lean prints the axioms)
native/       C reference, environment check, AVX2 kernels, tests, benchmarks
src/          exact rational models (Python), witness search, Lean-vs-C/hardware differential tests
results/      outputs of every run cited in FINDINGS.md
THEOREM.md    statements, paper proofs, and what exactly is machine-checked
FINDINGS.md   results, evidence table, speed, review, limits
REPLAY.md     every command, with expected output
```

## Building

```bash
cd lean && ./check.sh      # lake exe cache get && lake build && lake env lean ExactFDiv/Audit.lean
```

The C tests need gcc or clang with `-mfma -ffp-contract=off`, and never `-ffast-math`; see [REPLAY.md](REPLAY.md).

## Provenance

Built in November 2026 by Stanford Lean Club members working with AI coding agents (Claude Code), as part of a
search for places where a proof makes a faster implementation admissible. The mathematics, Lean proofs, C code,
tests and write-ups were produced with substantial AI assistance and checked as described above. Corrections,
independent replays on other hardware, and human review of the proofs are very welcome; please open an issue.
