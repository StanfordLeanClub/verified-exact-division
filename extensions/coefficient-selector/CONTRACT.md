# Binary32 division by 3: value contract

The selected and tightened kernels implement binary32 division by positive `3.0f` under round-to-nearest, ties-to-even, with gradual underflow and a fused multiply-add. FTZ and DAZ must be disabled. Floating-point exceptions must be masked. Compile without fast-math, reciprocal approximation, reassociation, or contraction that changes the specified operation sequence.

For every input encoding, the result agrees with division as follows:

| Result | Required agreement |
|---|---|
| Finite nonzero, including subnormal | Exact binary32 value, hence identical encoding |
| Positive or negative zero | Value and sign bit |
| Positive or negative infinity | Value and sign bit |
| NaN | NaN class only |

**Exception flags are not preserved. This is not full floating-point environment equivalence.** Starting with clear flags, input `3.0f` produces exactly `1.0f` in every tested variant. Hardware division leaves flags clear; the selected multiply/FMA sequence raises inexact (`MXCSR & 0x3f == 0x20`). Its rounded low product is inexact even though the quotient is exact. The arithmetic inequality is kernel-checked in Lean and the flag mismatch is observed in the native replay. No preservation guarantee is made for any exception flag, trapping behavior, `errno`, NaN payload/sign, or signaling-NaN status. Code that observes these must keep division or use a separately verified environment-preserving implementation.

The mismatch cannot be fixed solely by selecting another pair: `any_pair_inexact_at_three` proves that any finite binary32 pair returning 1 at input 3 must round at least one of its two operations inexactly. This does not rule out algorithms with additional branches, operations, or explicit environment handling.

The input range includes every binary32 encoding: subnormal inputs, values whose quotient is subnormal or signed zero, both signed zeros, infinities, and all quiet/signaling NaN encodings. Finite division by 3 cannot overflow. Tiny finite lanes use actual division. In a vector block, one tiny lane sends the whole block through division; flags may therefore depend on neighboring values and array length, even though output values do not.

The original selected pair is:

```c
h = 0x1.555554p-2f;  // bits 0x3eaaaaaa
l = 0x1.555556p-26f; // bits 0x32aaaaab
q = fmaf(x, h, x*l);
```

The proved old threshold is `2^-100` (bits `0x0d800000`). The tightened candidate uses `3*2^-102` (bits `0x0d400000`). The low-product normality condition, guard predicates, and full array result are separate proof obligations; their proof status is recorded in RESULTS.md and the axiom audit. A smaller threshold is not justified merely by passing native tests.

For the native array API, `src` and `dst` each designate at least `n` accessible floats; the ranges are disjoint or exactly equal, and the byte extent is representable. Partial overlap is unsupported. The tightened loop uses `n-i` bounds to avoid index-addition overflow. The Lean list theorem proves result order and length for every finite list. The additional [machine theorem](MACHINE_PROOF.md) proves termination, byte-level memory bounds and framing, in-place safety, and return/register behavior for the separately linked, byte-checked `certified_div3` image. Its destination must also be disjoint from the code/constants and return-address slot. Its precise preconditions are `Div3Machine.Precondition` and `Valid`; actual mappings and permissions are caller obligations. This does not cover arbitrary recompilation of the inline API.

The proof uses the project's explicit rational IEEE value model. Binary32 decoding, wrapping bit arithmetic, lane-mask reduction, branch selection, and list loop structure are proved inside Lean. The checked-image extension additionally proves execution in its explicit x86 instruction model, with a kernel-checked byte decoder. Primitive FP behavior, hardware/model conformance, loader correctness, and the caller's ABI remain stated trust boundaries. The division primitive is specified only for positive 3.0f. No test result is used as a theorem premise.

The independent acceptance check compares the actual header, compiled in a separate translation unit, with pinned Berkeley SoftFloat 3e integer arithmetic. Its exhaustive mode checks every encoding through both a scalar call and a SIMD array, and compares hardware division with the same oracle. Additional finite checks cover mixed lanes, all tail lengths through 70, in-place/disjoint buffers, eight float alignments, canaries, and inaccessible end pages. Deliberately broken variants must be rejected. The checked-image runner repeats these tests after verifying the loaded bytes. Testing does not establish the universal memory theorem or conformance to an external formal IEEE specification. SoftFloat is independently authored software, not an infallible or formally linked oracle. NaNs remain compared by class, and exception flags remain excluded.
