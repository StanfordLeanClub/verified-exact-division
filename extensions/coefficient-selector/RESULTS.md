# Guarded binary32 /3 extension

This work extends the certified coefficient selector to binary32 decoding, IEEE value rounding, exact wrapping guard bits, SIMD mask reduction, and the 32/8/scalar array loop. It is isolated from Claude's active work. The repository contribution belongs under `extensions/coefficient-selector/`, on a separate branch.

The earlier [expert assessment](ASSESSMENT.md) added independent acceptance checks without changing the algorithm. This follow-up adds a [machine-code proof](MACHINE_PROOF.md) for one fixed compiled image, including termination, byte-level memory safety and framing, in-place operation, and the return/ABI contract. The original inline header and earlier measurements are unchanged. The linked-image SoftFloat replay also checks every binary32 encoding: 12,886,335,424 comparisons, zero mismatches, and 4,544 guard-page calls. Results are in `results/machine_acceptance.json`; earlier acceptance evidence is retained.

## Proof statements

The complete replay covers 54 source modules and 244 audited declarations, including all 137 machine-proof theorems. Permitted dependencies are `propext`, `Classical.choice`, and `Quot.sound`, or none. No exported guarantee may rely on a proof hole, an added axiom, or native decision. The replay enforces this policy and rejects real admitted-proof/added-axiom controls. `results/proof_acceptance.json` records acceptance and every source hash; development failures and raw logs remain local.

`Div3Machine.machine_correct` quantifies over all permitted array lengths, initial register states, and byte memories. It gives a finite instruction execution with correct output values, a preserved memory frame, bounded memory accesses, preserved general registers, and a correct return. `program_decoded` checks all 107 instructions against the 532-byte image. `memory_permissions` derives per-byte permission safety from the range result and caller permissions. These are proofs relative to the explicit ISA and primitive FP models; their trust boundary and fixed-build scope are detailed in [MACHINE_PROOF.md](MACHINE_PROOF.md).

`nativeArray_correct` proves that the original selected P4 array model equals elementwise IEEE division for every list of 32-bit words. There is no caller-supplied validity or normal-input premise: `decode_valid` establishes representability for every encoding. `simd_testz_iff` connects ORs of corresponding 32-bit comparison lanes and the all-256-bits-zero test to whether any lane in any vector is flagged. `coldTiny_eq` proves that a flagged same-sign block always reaches the division arm of the cold helper. The proof includes both wraparound points in each signed integer comparison.

`tightArray_correct` gives the same result for the tightened threshold and direct division fallback. `tight_flags_subset` proves that it never flags an input the old selected guard accepted; `newly_fast` supplies a strict witness. The threshold changes from `2^-100` to `3*2^-102`, a 25% decrease in its real value. This admits another 8,388,608 signed input encodings. `tight_low_guard` checks the new product bound; `predecessor_low_fails` shows that the immediately preceding binary32 threshold fails that sufficient bound. This is not a proof that every smaller input makes the arithmetic fail.

The generic `CoefficientSelector.arbitrary_pair_ieee` theorem accepts an arbitrary coefficient pair, any precision, and exponent bounds. Its premises are unbounded correctness, `3*abs(l) <= abs(h)`, `abs(l) <= 1/abs(y)`, and a normal finite low product. It allows final overflow. `arbitrary_pair_guarded` derives the low-product range from a threshold and `abs(l) <= 1`. `check_sound_ieee` composes the existing checker and scaling theorem with that bridge. This removes the requirement that the high coefficient be the nearest reciprocal. It does not automatically generate IEEE-safe setup for every selected divisor.

## Subnormals, special values, and a fundamental limit

Subnormal inputs and other finite values below the guard use division. Outputs can be subnormal or signed zero. Both zero signs and infinity signs are preserved. NaNs agree as a class; sign, payload, and signaling status are collapsed by the model. The shared concrete fixtures include least/largest subnormals, the least normal, zero-rounding cases, both signs, guard boundaries, maximal finite inputs, infinities, and quiet/signaling NaNs.

The guard is necessary. At input bits `0x00800000`, the raw multiply/FMA sequence returns `0x002aaaaa`, while division returns `0x002aaaab`. The guarded path returns the latter. Both the numerical failure and the guarded answer are proved, and the native replay reproduces them.

Exception flags are explicitly outside the [contract](CONTRACT.md). Input `3.0f` returns exactly `1.0f`, but every tested reciprocal-pair variant raises inexact while division leaves flags clear. `any_pair_inexact_at_three` proves a stronger arithmetic obstruction: for **any** two finite binary32 coefficients that make this two-operation scheme return 1, at least one operation is inexact. Every coefficient is an integer multiple of `2^-149`; exactness of both operations would imply `3*(H+L) = 2^149` for integers H,L, which is impossible. Coefficient selection alone cannot remove this mismatch. The theorem does not model the exception register or exclude alternative algorithms with additional control flow or state handling.

## Native evidence and limits

The tightened implementation is `native/div3_tight.h`. Its block loads are retained across the decision, and the tiny branch goes directly to division; the redundant cold range/special scan and source reload are removed at source level. It uses subtraction-based loop bounds. These are source-level statements, not instruction-count or pointer-safety theorems.

The final exhaustive run checks all 4,294,967,296 encodings through five variants: Claude's original context, the previous selected context, the tightened context in Claude's unchanged engine, the direct tightened kernel, and hardware division. It records **21,475,308,630 comparisons including edge/tail/in-place cases, zero value mismatches**. Finite/zero outputs are compared bitwise and NaNs by class. The flag counterexample is checked independently. The prior run had a reporting-only comparison-counter error (counted two variants while executing five); its raw output is retained and superseded by the corrected run.

The original inline API remains a source-level implementation whose arbitrary compiler outputs are not certified. The dedicated `certified_div3` image additionally has the machine theorem and byte acceptance gate. Hardware conformance to the instruction model, actual mappings/permissions, loader/caller behavior, exception flags, and NaN payload preservation remain outside that theorem's guarantee. Only division by positive 3.0f is required of the machine proof's division primitive. See [CONTRACT.md](CONTRACT.md).

## Performance and priority

Fresh paired measurements compare all five variants on the same inputs, with pinned cores, randomized order, three warm-ups and 31 retained rounds. All 96 core/size/distribution groups and every trial are retained. For 4,096 inputs, the additional speedup of the direct tightened implementation over the previous selected P4 implementation is:

| Data | P-core paired speedup [95%] | E-core paired speedup [95%] |
|---|---:|---:|
| Ordinary normal inputs | 1.055 [0.955, 1.160] | 1.061 [1.056, 1.076] |
| Tiny inputs every 1,000 positions | 1.302 [1.266, 1.313] | 1.207 [1.201, 1.214] |
| Tiny inputs every 10 positions | 2.664 [2.583, 2.838] | 1.710 [1.707, 1.716] |
| Newly admitted threshold band | 7.067 [6.764, 8.898] | 7.666 [7.655, 7.711] |

The normal P-core improvement at 4,096 inputs is unresolved. On that workload, the complete direct specialization still beats Claude's original context by 1.612x [1.429, 1.870]; the E-core ratio is 1.778x [1.764, 1.788]. For 32 ordinary normal inputs, direct/selected improvement is 1.570x on the P-core and 1.533x on the E-core. For 16,777,216 ordinary inputs, neither core resolves an additional gain over the previous selection. No measured group's paired interval is wholly below 1 against the previous selected implementation, but several overlap 1; hardware division can still win on tiny-heavy small arrays.

The tighter threshold alone leaves ordinary normal workloads unchanged in algorithmic work. Its large gain is confined to the deliberately targeted threshold band. The direct specialization also fixes constants at compile time and simplifies its cold branch, so its measured improvement cannot be attributed solely to removing the second mask scan. It is offered as a `/3` specialization, not a universal dispatch policy.

The machine remained active, with aggregate busy fractions recorded in the metadata. No local Lean build overlapped timing. A preliminary Python summary of the P-core results overlapped the beginning of the E-core run; no trials were discarded. These within-run bootstrap intervals do not establish an application-wide gain, a quiet-machine result, or performance on another CPU. Medians, pairwise ratios, and the complete aggregate table are in `results/tight_summary.json` and [BENCH_RESULTS.md](BENCH_RESULTS.md). Raw trials remain local and can be regenerated with the supplied harness.

The base multiply/FMA algorithm, coefficient synthesis, bound tightening, and removal of redundant branches are established techniques. The incremental contribution is the formally checked coefficient freedom and its useful instances, fuller IEEE/bit/SIMD proof coverage, and measured integration. Priority for the combination remains unestablished; see [NOVELTY.md](NOVELTY.md).
