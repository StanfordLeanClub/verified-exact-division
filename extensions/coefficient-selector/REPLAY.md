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

The ordinary build checks module imports. The fresh-source replay concatenates all 27 sources in preserved namespace/section order, imports only Mathlib, and checks all declarations without importing a cached project theorem. Its source, output, and hashes are written to `results/`. The original development used the installed Mathlib cache and direct Lean invocation; the Lake commands provide portable installation. No exported guarantee may depend on `sorryAx`, native evaluation, or an added axiom.

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

This publication includes aggregate validation and the complete aggregate timing table. Raw trial records, local source identities, and development failure logs remain in the separate local evidence package. Fresh commands write new raw records here. The initial counter-reporting error was corrected and the exhaustive run repeated; failing Lean builds were rejected before final replay. The unguarded numerical failure remains a checked theorem and test case.

Verify shipped file hashes with `python verify_manifest.py`. The proof is of the specified value/bit/control-flow model, not C compilation or pointer safety. See [CONTRACT.md](CONTRACT.md).
