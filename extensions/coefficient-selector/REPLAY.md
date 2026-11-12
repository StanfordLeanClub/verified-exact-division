# Portable replay

Requires Lean 4.32.1 and the Mathlib revision pinned in `lean/lakefile.toml`:

```sh
cd lean
lake update
lake exe cache get
lake build
lake env lean Div3IEEE/Audit.lean
cd ..
python replay.py
```

The ordinary build checks module imports. The fresh-source replay concatenates all 54 sources in preserved namespace/section order, imports only Mathlib, and checks all declarations without importing a cached project theorem. Its source, output, and hashes are written to `results/`. Development used the installed Mathlib cache and direct Lean invocation; the Lake commands provide portable installation. No exported guarantee may depend on `sorryAx`, native evaluation, or an added axiom.

Replay now requires all 244 expected axiom reports and rejects missing/duplicate reports, unapproved dependencies, proof holes, and native-decision tokens. It runs real Lean negative controls: an admitted proof and a proof using a new axiom both compile successfully, but must fail the acceptance policy. Nine additional parser/source-policy controls check rejection behavior. This is a build acceptance policy, not a defense against a malicious Lean metaprogram or a substitute for reviewing theorem statements.

For offline replay against an explicitly installed Mathlib cache, use `python replay.py --lean /path/to/lean --lean-path-file /path/to/mathlib-paths.txt`. The file contains the platform-separated Mathlib/dependency import paths. The recorded assessment used this mode and Lean 4.32.1; a new dependency installation was not tested.

After building, synthesize another normalized divisor with:

```sh
python tools/select_coefficients.py --precision 24 --significand 12582912 --prove
```

Without `--prove`, the search result is untrusted. That CLI certifies unbounded RNE correctness. The generic IEEE bridge additionally requires the explicit range premises; it does not automatically generate a full IEEE implementation for every divisor. Search failure means fallback to division.

Native tests require x86 AVX2/FMA and Clang. The recorded benchmark harness uses Windows affinity and timing APIs. On the measured Core Ultra 7 155U, processor 10 is a P-core and processor 4 an E-core; select appropriate processors on another machine.

```sh
python run_native.py
python run_tight.py exhaustive 10
python run_tight.py bench 10
python run_tight.py bench 4
python analyze_tight.py
```

Run timing sequentially after compilation ends. The tests set nearest-even, disable FTZ/DAZ, and mask exceptions. Exhaustive validation covers every binary32 encoding through five variants; tail/edge/in-place checks and the flag counterexample are included. Tests compare finite/zero values bitwise and NaNs by class, not flags or NaN payloads.

Independent acceptance for the tightened `/3` header (x86-64 AVX2/FMA, Clang and `llvm-objdump`):

```sh
python acceptance.py
python acceptance.py --exhaustive
```

This downloads Berkeley SoftFloat 3e from its author and checks archive SHA-256 `21130ce885d35c1fe73fc1e1bf2244178167e05c6747cad5f450cc991714c746`. To supply the same archive offline, add `--softfloat-archive /path/to/SoftFloat-3e.zip`. Only the required, unmodified reference sources are compiled, using its `8086-SSE` specialization and nearest-even mode. The actual header is compiled separately without LTO. The runner checks for multiply/FMA/division instructions and absence of floating-point division in the oracle function. These instruction-presence checks are not compiler equivalence verification.

The short run includes 1,048,576 pseudorandom words plus boundary/layout checks. Exhaustive mode enumerates all 2^32 words and compares scalar, SIMD, and hardware outputs with the reference. SIMD sweep batches contain consecutive encodings; mixed-lane tests are finite, not an exhaustive enumeration of arrays. Both modes must reject five executable mutations: omitted guard, wrong high coefficient, incomplete lane reduction, unfused arithmetic, and an extra store. Compiler errors and crashes do not count as successful rejection. Commands, binaries, disassembly, output, and failure witnesses stay in `acceptance_work/`; the portable aggregate record is `results/acceptance.json`. These correctness-run durations are not kernel performance measurements. Runtime environment checks in the harness do not add environment/ISA dispatch to the production API.

This publication includes aggregate validation and the complete aggregate timing table. Raw trial records, local source identities, and development failure logs remain in the separate local evidence package. Fresh commands write new raw records here. The initial counter-reporting error was corrected and the exhaustive run repeated; failing Lean builds were rejected before final replay. The unguarded numerical failure remains a checked theorem and test case.

## Fixed compiled image

After both `lake build` and the fresh-source replay pass, run the separate
machine-image gate. The recorded build uses Windows x86-64, Clang 19.1.5,
AVX2/FMA, and COFF objects:

```sh
cd lean
lake env python ../machine_acceptance.py --softfloat-archive /path/to/SoftFloat-3e.zip --exhaustive
```

Omit `--exhaustive` for the short sweep. For an offline direct Lean invocation,
pass `--lean /path/to/lean --lean-path-file /path/to/project-and-mathlib-paths.txt`;
this file must include the freshly built Div3Machine and all dependency paths.
The recorded replay used this mode. The ordinary source replay needs only
Mathlib paths, as described above.

This gate compiles `native/certified_div3.c`, extracts its code/constants,
checks exact byte equality in Lean, audits the machine theorem dependencies,
rejects five mutated images, assembles/links the accepted image, and checks
all loaded bytes before native testing. Different compiler output fails
closed. It does not silently regenerate a proof for an altered program.
Native commands, binaries, and raw logs stay in `machine_work/`; the portable
record is `results/machine_acceptance.json`. The checked object in that run
is `checked.obj`, with the ABI declared in `native/certified_div3.h`.

The 532-byte image hash is fixed in [MACHINE_PROOF.md](MACHINE_PROOF.md).
Consumers must link that accepted object and preserve its image/ABI/environment
contract. Arbitrary inline compilation does not acquire this guarantee.
No timing result for the dedicated compiled entry point is claimed.

Verify shipped file hashes with `python verify_manifest.py`. The machine
proof establishes values, termination, memory bounds/framing, and return
behavior relative to the explicit ISA/primitive specifications and caller
preconditions. See [CONTRACT.md](CONTRACT.md) for the remaining boundaries.
