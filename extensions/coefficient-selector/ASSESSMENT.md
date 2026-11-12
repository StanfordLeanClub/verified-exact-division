# Assessment of the coefficient-selector PR

The original assessment below is historical: revision `2aa0bbd8941405369495f24bad913ca6037ed09c`, PR #1, against base `482d8cdad10f23ef778e3c938b1b43ceac06809c`. That assessment added acceptance checks without changing the numerical implementation or theorem sources.

The subsequent machine-proof work starts from PR head `509f271c17784f7ed7094ce21856afb14c46dd9a`. It addresses the most consequential remaining gap for one fixed compiled `/3` image: `machine_correct` proves termination, the 32/8/scalar execution, byte-level memory bounds/framing, in-place safety, and return/register behavior. A kernel-checked byte decoder and exact-image gate connect that theorem to a separately linked entry point. See [MACHINE_PROOF.md](MACHINE_PROOF.md) for the current evidence and trust boundary. The inline header, frozen dependencies, and earlier benchmarks remain unchanged. The statements below about an absent universal memory/compiled-code proof describe the earlier revision and are superseded only for this checked image.

## Decision

Keep the coefficient selector, same-sign `/3` specialization, tighter guard, and flag-obstruction theorem. Together they form a useful research contribution with unusually broad arithmetic and control-flow coverage. The appropriate next addition is an executable acceptance process that checks the compiled artifact against an independently authored reference and demonstrates that the process rejects defects. That addition is now implemented.

The strongest supported claim is a machine-checked model of value-preserving binary32 division by 3, backed by exhaustive native evidence under the stated environment. It is not full IEEE observable-behavior equivalence, a formally verified C library, a general runtime divisor selector, or an application-wide speedup result. Keep the PR a draft for human review. A consumer may evaluate the specialization when its environment satisfies [CONTRACT.md](CONTRACT.md), it does not observe exception flags or NaN details, and its own workload benefits.

## Professional method and rewritten brief

1. **Additional professional obligation:** audit whether the strongest advertised claim is the actual theorem, then trace that claim through encoding, SIMD control flow, compilation, memory use, and the runtime environment. Try to falsify the validation itself with known defects.
2. **Raw starting material:** the exact PR tree, Lean definitions and dependencies, native header and generated instructions, input enumeration and comparison code, and individual unfiltered timing trials. Summaries are claims to check.
3. **Methods and tools:** claim-to-evidence tracing; fresh Lean source replay and enforced axiom audit; pinned Berkeley SoftFloat differential testing; exhaustive binary32 enumeration; mixed-lane, tail, alignment and memory-boundary tests; executable mutations; Clang/llvm-objdump inspection; and direct recomputation from raw paired timings.
4. **External tests of correctness:** Lean's kernel, an independently authored arithmetic implementation, the actual compiler-produced binary, concrete rejection witnesses, and reproducible source/binary identities. These checks do not substitute for an independent human proof or compiler-correctness review.

The working brief was:

> Assess PR #1 at its exact current revision as a numerical-software verification specialist. Starting from source, proof definitions, generated code, and raw measurements, determine precisely what is proved, what is only tested, and what consumers can safely rely on. Try to falsify the strongest claims and identify the single most consequential assurance gap. Implement the smallest substantive improvement that closes or materially reduces that gap, validate it with independent evidence and deliberate negative controls, and update the PR's contract and claims accordingly. Keep Claude's work untouched. Do not expand the divisor set or make novelty or performance claims beyond the evidence.

## Claim-to-evidence assessment

| Claim | Evidence and practical boundary |
|---|---|
| Accepted arbitrary coefficient pairs work | `check_sound` and scaling/IEEE bridge theorems. The bridge has explicit range premises. The search program is untrusted until its emitted certificate is checked. |
| `/3` covers every input encoding | `decode_valid`, `tightTiny_bits`, `tight_raw_correct`, and `tightArray_correct`; no caller-supplied normal-input premise. The semantics are the project's rational IEEE value model. |
| SIMD branching agrees with the guard | Wrapping signed-bit comparisons and `simd_testz_iff` prove the specified lane reduction; array theorems prove result order. Matching those definitions to intrinsics is still a correspondence obligation. |
| Tighter guard is justified | Exact normal-low-product bound and a failing predecessor for that bound. This is a sufficient guard, not a theorem that every smaller input fails or that the guard is globally optimal. |
| Exception flags can be ignored only by contract | Input 3 returns 1 but raises extra inexact. `any_pair_inexact_at_three` rules out repairing this by coefficient selection alone within this two-operation scheme. It does not rule out other algorithms or explicit state handling. |
| The compiled header computes the promised values | Previously hardware differential testing; now also every encoding checked independently against SoftFloat in scalar and SIMD execution. No C/LLVM/ISA equivalence proof has been added. |
| Arrays are safe | Valid disjoint or identical ranges are preconditions. Added canaries and inaccessible-page tests cover specified finite layouts. There is still no universal pointer or memory-safety theorem. |
| Native execution is faster | Workload-dependent measurements on one CPU. Counts, paired medians, and all trial retention check out; within-run intervals do not establish general deployment gains. |
| The algorithm is novel | The existing novelty review does not establish priority. The new validation uses established methods and adds no novelty claim. |

The theorem inventory and native exhaustive sweep are complementary. Neither alone bridges every trust boundary. In particular, proving a hand-written arithmetic model does not prove its C translation, and enumeration on one executable does not prove all compilers or arbitrary arrays.

## What was added and what it found

The independent native reference uses the author's unmodified Berkeley SoftFloat 3e sources, with the archive pinned by SHA-256. SoftFloat implements IEEE binary arithmetic in software; its interface supports binary32 division and explicit rounding modes. [SoftFloat documentation](https://www.jhauser.us/arithmetic/SoftFloat-3/doc/SoftFloat.html)

`acceptance.py` compiles the production header in a separate translation unit without LTO. Expected bits come from SoftFloat integer arithmetic, not native division, the reciprocal algorithm, or the Lean model. The recorded Clang 19.1.5 build checked all **4,294,967,296 encodings** through scalar and SIMD execution, plus hardware division against the same oracle: **12,886,335,424 value comparisons including layout tests, zero mismatches**. The layout checks include **4,544 calls ending at inaccessible pages**, tails through length 70, eight float alignments, exact in-place operation, source preservation, and mixed blocks containing a single tiny lane. NaNs are compared by class. See [the aggregate native record](results/acceptance.json).

All five deliberately broken variants compiled, ran, and were rejected by explicit comparisons:

| Mutation | Rejection witness |
|---|---|
| Remove the tiny guard | `00800000`: got `002aaaaa`, expected `002aaaab` |
| Increase the high coefficient one ULP | `0d400000`: got `0c800001`, expected `0c800000` |
| Examine only lane zero of the mask | `00800000`: got `002aaaaa`, expected `002aaaab` |
| Replace FMA with separate multiply/add | `aedb5108`: got `ae123606`, expected `ae123605` |
| Store one element beyond the output | Output canary modified |

Instruction inspection confirms vector multiply, FMA, and division in the tested implementation, hardware division in the comparison function, and no floating-point arithmetic instructions in SoftFloat's division function. This is a sanity check on lowering, not a symbolic equivalence proof. The oracle and implementation still share a compiler; their arithmetic algorithms are independent. The TestFloat authors explicitly caution that differential testing cannot guarantee absence of all bugs. The TestFloat program itself was not run here. [TestFloat documentation](https://www.jhauser.us/arithmetic/TestFloat-3/doc/TestFloat-general.html)

The proof replay had a genuine acceptance-policy defect: it returned Lean's exit status without checking the printed axiom dependencies. Lean can return success for an admitted theorem. The revised `replay.py` requires all 107 reports and permits only `propext`, `Classical.choice`, and `Quot.sound`. All 27 unchanged proof modules replayed successfully. Real admitted-proof and added-axiom probes were rejected even though Lean compiled them successfully; nine parser/source-policy negative controls also passed. See [the proof record](results/proof_acceptance.json). This run used installed, pinned Mathlib dependencies, not a fresh dependency installation. The original exported proofs passed the audit; this finding concerns enforcement by the old replay script, not an identified hole in those proofs.

## Performance judgment and remaining work

The raw timing audit retained all **14,880 trials**: 96 core/size/distribution groups, five variants, 31 rounds. Every published median and paired median ratio matches the raw records. The machine's aggregate busy fractions were 36.36% and 32.77%; preliminary analysis overlapped the beginning of the E-core run. The original within-run intervals are retained, not upgraded to independent-run confidence estimates.

At 4,096 ordinary inputs the incremental P-core gain remains unresolved. Tiny inputs every 1,000 positions support the reported additional 1.30x P-core and 1.21x E-core gains on that workload. Large ordinary arrays do not resolve an additional gain. These facts justify keeping an opt-in specialization and measuring it in a real consumer; they do not justify a universal replacement policy. No new speed measurement or performance improvement is claimed by this assessment.

The next decision-changing evidence depends on the intended claim. A production throughput claim needs a named consumer workload, end-to-end measurements including dispatch/setup, and independent repeated runs. A formally verified executable claim needs a semantics-preserving connection to C/LLVM/ISA and a memory model. A full IEEE replacement needs a different exception-state strategy. Adding more coefficient instances would not resolve any of those questions. The present change intentionally strengthens acceptance of the existing `/3` result and leaves those larger obligations explicit.
