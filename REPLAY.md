# Replay — exact division by an invariant floating-point divisor

Everything below was run on 2026-11-10 on one machine: Intel Core Ultra 7 155U (AVX2 + FMA, no AVX-512),
Windows 11 + WSL2 Ubuntu, gcc 15.2.0, Python 3.14, Lean 4.32.1 with Mathlib v4.32.1 (commit 520045ab14).
Same-host replay only; nobody else has re-run this yet. Paths are relative to the repository root.

## 1. Lean (kernel-checked statements)

Files: `lean/ExactFDiv/Basic.lean` (rounding basics), `Main.lean` (Theorem A, `alg2_core`), `General.lean`
(arbitrary signs/exponents, even-significand corollary, candidate uniqueness), `Bounded.lean` (formats with a
minimal exponent, bridge lemma, `alg2_bounded`), `IEEE.lean` (model of IEEE data and operations, special
operands, power-of-two divisors), `Setup.lean` (exactness of the residual, normal range of `1/y`), `Final.lean`
(Theorem B item 1, `kernel_eq_div`), `Exists.lean` (a rounding function satisfying the spec exists),
`Audit.lean` (`#print axioms`).

Build with Lake (downloads Mathlib's prebuilt cache on first use; `lean-toolchain` pins Lean 4.32.1 and
`lakefile.toml` pins Mathlib `v4.32.1`):

    cd lean && ./check.sh        # = lake exe cache get && lake build && lake env lean ExactFDiv/Audit.lean

Expected: no errors; `Audit.lean` prints, for each of `nearest_unique`, `alg2_core`, `alg2_float`, `alg2_even`,
`candidate_unique`, `candidates_sum`, `candidates_not_both`, `IsNearestB.toNearest`, `alg2_bounded`,
`kernel_special`, `kernel_inf_opposite`, `kernel_zero_opposite`, `mul_inv_eq_div`, `setup_abs`,
`inv_ge_minNormal`, `kernel_eq_div`, `kernel_eq_div_even`, `exists_nearestB`, `exists_round`, `guards_imply`,
`guards_imply_noupper`, `rho_computed`, and the revision-4 theorems `rhe_nearest` … `efd_correct` and `efd_correct_binary64`, `efd_correct_binary32` (39 lines):
`depends on axioms: [propext, Classical.choice, Quot.sound]` (saved in `results/lean_axioms_audit.txt`).
`grep -n "sorry\|native_decide\|^axiom" lean/ExactFDiv/*.lean` prints nothing. About 1–3 minutes per file.

### 1b. Lean ↔ C and hardware (differential)

    cd src/difftest
    python gen.py 20261110 3000 3000          # divisor significands -> ys64.txt, ys32.txt
    gcc -O2 -mfma -ffp-contract=off -o cdiff cdiff.c -lm && ./cdiff > c_out.txt     # C check verdicts (WSL)
    cd ../../lean && lake env lean ../src/difftest/Diff.lean > ../src/difftest/lean_out.txt   # Lean `accept`
    cd ../src/difftest && python gen_round.py 7 4000                                 # pairs + hardware quotients
    cd ../../lean && lake env lean ../src/difftest/Round.lean                   # model quotients -> pairs_lean.txt

Expected: identical 0/1 strings for both formats, and `pairs_lean.txt` identical to `pairs_expected.txt`
(`results/lean_correspondence.txt`).

## 2. Exact models (Python, no dependencies)

    cd src
    python checker.py 12            # per-divisor check vs brute force, every significand, p = 3..12  (~25 min)
    python ieee_model.py 5 -24 16   # toy IEEE format, EVERY pair of values incl. specials, strict thresholds (~1 min)
    python ieee_model.py 5 -24 16 loose
    python ieee_model.py 6 -30 20   # (~10 min each)
    python ieee_model.py 6 -30 20 loose
    python ieee_model.py 7 -34 22   # (~45 min CPU)
    python ieee_model.py 8 -24 6    # (~1 h CPU; the first format with rejected significands)
    python witnesses.py             # binary64 witnesses for every guard (exact model)

Expected: `checker_mismatches: 0` on every line of `checker.py`; `MISMATCHES guarded vs division: 0` for every
`ieee_model.py` run; `witnesses.py` prints the first eight rows of THEOREM.md §3 (the last two are in
`native/witness_check.c` only). Outputs are in `results/`.

## 3. Native tests (hardware fma and division as the oracle)

    cd native
    CF="-O2 -mfma -mavx2 -ffp-contract=off"
    gcc $CF -o witness_check witness_check.c -lm && ./witness_check        # 10 witnesses: raw kernel wrong, guarded right
    gcc $CF -fopenmp -o test_f32 test_f32.c -lm
    ./test_f32 sig 30000 3      # checker verdict vs exhaustive scan of all 2^23 significands, 30 000 divisors
    ./test_f32 x 20 11          # guarded scalar reference vs x / y for ALL 2^32 x, 100 structured + 20 random divisors (~40 min, 14 threads)
    gcc $CF -fopenmp -o test_f64 test_f64.c -lm && ./test_f64              # binary64 adversarial, > 2e9 comparisons
    gcc $CF -fopenmp -o test_kernels test_kernels.c -lm && ./test_kernels 200 40 1   # AVX2 kernels vs scalar division
    gcc -O3 -mavx2 -mfma -ffp-contract=off -fopenmp -o int_dividend int_dividend.c -lm
    ./int_dividend test 100     # corollary A4: all 2^32 int32 dividends for 147 constants; uint16 for binary32
    ./int_dividend bench        # (double)int / C  vs  the fold (quiet machine)
    gcc -O1 -mfma -ffp-contract=off -frounding-math -o test_flags test_flags.c -lm && ./test_flags   # exception flags

Windows side (clang targeting MSVC, Python with NumPy), comparison with a shipped consumer:

    cd native && clang -O2 -mavx2 -mfma -ffp-contract=off -shared -Wno-unknown-pragmas -o efd.dll efd_dll.c
    cd .. && python src/numpy_compare.py > results/numpy_compare.json 2> results/numpy_compare.txt

Every test prints a `SUMMARY` line; the expected mismatch count is 0 everywhere. `-ffp-contract=off` matters: the
tests compare against `x / y` and must not be re-contracted. A CPU without FMA would run libm's software `fma`
(still correct, far slower).

## 4. Benchmarks

`native/bench.c`, `native/run_bench.sh`, `native/BENCH.md` (method, loop disassembly, tables),
`results/bench_tables.md` (all tables; raw per-trial logs are not included in this repository). Timings are only meaningful on a quiet machine; BENCH.md records the load at the
time of each run.

