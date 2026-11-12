# Certified coefficient selection and guarded binary32 division

This isolated extension adds a sound arbitrary-pair coefficient checker, a same-sign `/3.0f` specialization, and a Lean proof from every binary32 input encoding through exact guards and SIMD/list control flow. It also provides a tighter threshold and direct fallback, plus an arithmetic proof that coefficient selection alone cannot preserve the inexact flag at input 3.

Read [RESULTS.md](RESULTS.md), [CONTRACT.md](CONTRACT.md), and [REPLAY.md](REPLAY.md). The implementation is [div3_tight.h](native/div3_tight.h); the full aggregate timing table is [BENCH_RESULTS.md](BENCH_RESULTS.md).

The [machine proof](MACHINE_PROOF.md) now connects one exact compiled image to that value model, including termination, byte-level memory bounds, in-place safety, framing, and return/register behavior. Use the separately linked `certified_div3` API and the exact-image acceptance gate for this guarantee. The 32/8/scalar algorithm and the original inline header remain unchanged.

The [expert assessment](ASSESSMENT.md) traces the assurance boundaries and explains the independent acceptance checks added after the initial PR. Run `python acceptance.py` for the short SoftFloat comparison and deliberate fault tests, or add `--exhaustive` to check all binary32 encodings through both scalar and SIMD execution. `python replay.py` now enforces the axiom policy and tests that admitted proofs are rejected.

This directory owns its build, frozen dependencies, proofs, and implementation. It changes no preexisting repository files. The native headers match upstream commit `482d8cdad10f23ef778e3c938b1b43ceac06809c`. Frozen ExactFDiv arithmetic definitions match that commit; its IEEE source additionally derives typeclass instances, and its audit lists more theorems.

The guarantee is IEEE **value** agreement under nearest-even rounding and gradual underflow, including signed zeros and NaN class. Exception flags are explicitly not preserved. For the checked image, memory and control flow are proved relative to the stated x86/primitive-instruction model and caller preconditions. Arbitrary C compilation and hardware/model conformance remain outside that theorem. No human audit is claimed.

This publication contains portable sources and aggregate validation. Detailed raw measurements, source replay logs, failure records, and local provenance remain in the separate local evidence package. The commands below regenerate evidence without requiring those local files. No local-machine paths or raw benchmark records are exported here.

The underlying BMR algorithm is established. Priority for this particular combination is unestablished; see [NOVELTY.md](NOVELTY.md).
