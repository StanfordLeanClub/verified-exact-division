# Certified coefficient selection and guarded binary32 division

This isolated extension adds a sound arbitrary-pair coefficient checker, a same-sign `/3.0f` specialization, and a Lean proof from every binary32 input encoding through exact guards and SIMD/list control flow. It also provides a tighter threshold and direct fallback, plus an arithmetic proof that coefficient selection alone cannot preserve the inexact flag at input 3.

Read [RESULTS.md](RESULTS.md), [CONTRACT.md](CONTRACT.md), and [REPLAY.md](REPLAY.md). The implementation is [div3_tight.h](native/div3_tight.h); the full aggregate timing table is [BENCH_RESULTS.md](BENCH_RESULTS.md).

This directory owns its build, frozen dependencies, proofs, and implementation. It changes no preexisting repository files. The native headers match upstream commit `482d8cdad10f23ef778e3c938b1b43ceac06809c`. Frozen ExactFDiv arithmetic definitions match that commit; its IEEE source additionally derives typeclass instances, and its audit lists more theorems.

The guarantee is IEEE **value** agreement under nearest-even rounding and gradual underflow, including signed zeros and NaN class. Exception flags are explicitly not preserved. C compilation, pointers, and AVX2 instruction semantics are outside the Lean theorem. No human audit is claimed.

This publication contains portable sources and aggregate validation. Detailed raw measurements, source replay logs, failure records, and local provenance remain in the separate local evidence package. The commands below regenerate evidence without requiring those local files. No local-machine paths or raw benchmark records are exported here.

The underlying BMR algorithm is established. Priority for this particular combination is unestablished; see [NOVELTY.md](NOVELTY.md).
