# BENCH — array / scalar: exact mul+FMA kernels vs vdivpd/vdivps (Intel Core Ultra 7 155U)

These are measured wall-clock throughputs on one laptop. They are not operation counts and they are not proofs.
Correctness is covered separately (`results/native_kernels.txt`, `results/native_f64_adversarial.txt`).

## What is measured

All variants use the same 4-vector unrolling. Each is a `noinline` function called through a function-pointer
table, so the compiler cannot hoist anything across variants or calls.

| variant | per element | exact? |
|---|---|---|
| `div` | `vdivpd`/`vdivps` loop (`div64_array`, `div32_array`) | yes (reference) |
| `recip` | `x * (1/y)` | **no**; speed reference only |
| `raw` | unguarded `fma(x, zh, x*zl)` | only for tlo <= \|x\| < thi; used only to price the guard |
| `P1` | guarded kernel; a flagged block is redone with real division | yes |
| `P2` | guarded kernel; flagged blocks whose flagged lanes are all +-0/+-inf/NaN get `x ^ signbit(y)` (or the raw q when same_sign); otherwise the block is redone with division (**default policy**) | yes |
| `P3` | branchless specials: every block blends `x ^ signbit(y)` into special lanes and branches only on finite nonzero lanes outside [tlo, thi) | yes |

The guard is `a = bits(x) << 1; out = (a + K) >s C`: one shift, one add and one signed compare per vector, an OR
across the block, and one `vptest`/`jne` per block of 16 doubles or 32 floats. Since tests check the shipped code,
an earlier mask-based guard (`bits & 0x7FF..F`) was replaced by the shift. The shift needs no mask constant, which
removed register spills. The slow path is an out-of-line `cold` function that reloads the block from `src`.

**Data sets**
- (i) normal-range values, `|x| = m * 2^U`, U uniform in [-30, 30], random sign.
- (ii) (i) with 10 % zeros.
- (iii) (i) with 1 % NaN.
- (iv) (i) with 0.1 % finite nonzero values below tlo, which force the division fallback.
- (v) integers 0..255. About 0.4 % of these are 0, which is a special lane.

**Divisors** 255, 3, 0.1, 1.7320508075688772, 1e-3. Setup modes:

| divisor | f64 mode | f64 same_sign | f32 mode | f32 same_sign |
|---|---|---|---|---|
| 255 | FMA | 1 | FMA | 0 |
| 3 | FMA | 1 | FMA | 0 |
| 0.1 | FMA | 0 | FMA | 0 |
| 1.7320508075688772 | FMA | 0 | **DIV** (rejected by the significand check) | 0 |
| 0.001 | FMA | 0 | FMA | 1 |

For the float32 divisor `(float)1.7320508…` the efd variants are the plain division loop. They dispatch on mode
exactly like `efd32_div_array`.

**Sizes** 256, 4096, 65536, 1 Mi and 16 Mi elements. Footprints per array: f64 2 KiB / 32 KiB / 512 KiB / 8 MiB /
128 MiB, and f32 half of that. L1d is 48 KiB, L2 2 MiB and L3 12 MiB. **Caution:** f64 n=4096 out-of-place is
64 KiB (src+dst), which does not fit in L1. f64 n=4096 in-place and f32 n=4096 do fit.

**In-cache vs memory-bound**
- n <= 65536 is in-cache (L1/L2). This is where the arithmetic matters.
- n = 1 Mi is L3/DRAM.
- n = 16 Mi is DRAM-bound.

## Methodology

**Timing**
- `rdtscp`/`lfence` around each sample. The TSC runs at 2.688 GHz and was calibrated against CLOCK_MONOTONIC. ns
  are reported.
- Out-of-place: one sample is K calls on the same buffers, with K*n >= 65536.
- In-place: one sample is one call on each of K fresh copies (K*n*size >= 16 KiB), refreshed by an untimed
  `memcpy`.
- Variants are sampled **interleaved, round-robin within a group**, so clock drift hits all of them alike.
- There are 3 warm-up rounds, then at least 15 rounds (at least 31 for n <= 65536). The tables give the median with
  [min..max].

**Clock**
- Before and after each group, a dependent `imul` chain (3-cycle latency) estimates the core clock. A dependent
  add-immediate chain gave impossible 5–18 GHz readings: these cores apparently resolve add-immediate chains early.
- Core cycles per element = ns × that clock. They are stored as `est_core_cycles` in the JSON. They are approximate,
  because the U-series part changes frequency within a group.

**Pinning**
- WSL2 exposes 14 identical vCPUs: no P/E topology, no MAXMHZ, every vCPU reports P-core caches. `taskset` pins a
  vCPU, not a physical core. A per-vCPU probe (`cpuprobe.c`) showed no stable P/E mapping. All vCPUs measured
  ~2.7 GHz with vdivpd ymm ≈ 8 cycles.
- The WSL run (`wsl_vcpu2`, `taskset -c 2`) therefore ran on whatever physical core Windows chose. Its clock median
  was 3.19 GHz, so most likely a P-core.
- For a real P-core/E-core comparison, the same `bench.c` was also built **natively on Windows** (clang 19.1.5, same
  flags; `#ifdef _WIN32` shim). `SetThreadAffinityMask` pinned it to a logical processor. `EfficiencyClass` from
  `GetLogicalProcessorInformationEx` identified the cores: LP 0,1,10,11 = class 1 (P-cores), LP 2–9 = class 0
  (E-cores), LP 12–13 = class 0 at ~1 GHz (LP E-cores).
- Runs: `win_pcore_lp10` (median clock 3.64 GHz) and `win_ecore_lp4` (median 2.11 GHz). The Windows build is a
  different compiler. Its correctness was checked with `test_kernels_win.exe 5 0 3` (part A only: 1.77e9 elements,
  0 mismatches). Its loops were not hand-inspected; only instruction presence was checked.

**Load**
- The final WSL run was taken on a quiet machine: WSL load1 1.0 (the benchmark itself) and the Windows host at
  0.18 / 0.11 busy cores before and after (`results/host_load_log.txt`).
- The two Windows runs followed immediately (03:10–03:15 local). Host load was not logged during them. They show the
  same tight min/max spreads, but their quietness is inferred, not measured.
- An earlier full WSL run, made while the Windows host had ~3.8 busy cores (`lean` processes outside WSL, invisible
  to the WSL load average), is kept as `wsl_vcpu2_hostbusy`. Label it **CONTAMINATED**. Its numbers agree with the
  quiet run within the run-to-run variation.
- Runs made with superseded kernel/bench code were discarded.

**Replay**
- `native/run_bench.sh <vcpu> <label> full 15` (WSL).
- Windows: `clang -O2 -mavx2 -mfma -ffp-contract=off -D_CRT_SECURE_NO_WARNINGS bench.c -o bench_win.exe`, then
  `set EFD_AFFINITY=10` and `bench_win.exe full <label> 15` and `bench_win.exe setup <label>`.
- `python3 native/summarize.py results/bench_core_ultra_7_155u.json results/bench_raw_*.jsonl > results/bench_tables.md`.
- Raw JSONL is in `results/bench_raw_*.jsonl`; stderr logs are in `results/bench_log_*.txt`.

## Headline (y = 3, data (i))

Median ns/element. The speedup is div/P2; P2 is the default exact kernel.

| core | type | 256 | 4096 | 65536 | 1 Mi | 16 Mi |
|---|---|---|---|---|---|---|
| P-core (win LP10) out-of-place | f64 div / P2 | 0.608 / 0.164 (3.7x) | 0.542 / 0.183 (3.0x) | 0.436 / 0.146 (3.0x) | 0.684 / 0.570 (1.2x) | 0.969 / 0.961 (1.0x) |
| P-core (win LP10) in-place | f64 div / P2 | 0.798 / 0.450 (1.8x) | 0.640 / 0.190 (3.4x) | 0.437 / 0.115 (3.8x) | 0.663 / 0.541 (1.2x) | 0.844 / 0.642 (1.3x) |
| P-core (win LP10) out-of-place | f32 div / P2 | 0.166 / 0.073 (2.3x) | 0.190 / 0.073 (2.6x) | 0.165 / 0.086 (1.9x) | 0.157 / 0.148 (1.06x) | 0.505 / 0.503 (1.0x) |
| P-core (win LP10) in-place | f32 div / P2 | 0.202 / 0.093 (2.2x) | 0.210 / 0.083 (2.5x) | 0.166 / 0.082 (2.0x) | 0.219 / 0.236 (0.92x) | 0.304 / 0.318 (0.96x) |
| E-core (win LP4) out-of-place | f64 div / P2 | 2.110 / 0.371 (5.7x) | 2.110 / 0.357 (5.9x) | 2.110 / 0.348 (6.1x) | 2.251 / 1.087 (2.1x) | 2.623 / 1.320 (2.0x) |
| E-core (win LP4) out-of-place | f32 div / P2 | 0.783 / 0.212 (3.7x) | 0.737 / 0.178 (4.2x) | 0.696 / 0.163 (4.3x) | 0.809 / 0.310 (2.6x) | 0.903 / 0.692 (1.3x) |
| WSL vCPU2 out-of-place | f64 div / P2 | 0.590 / 0.163 (3.6x) | 0.457 / 0.237 (1.9x) | 0.478 / 0.176 (2.7x) | 0.923 / 0.908 (1.0x) | 1.120 / 1.092 (1.0x) |
| WSL vCPU2 out-of-place | f32 div / P2 | 0.286 / 0.133 (2.2x) | 0.262 / 0.119 (2.2x) | 0.161 / 0.110 (1.5x) | 0.178 / 0.178 (1.0x) | 0.497 / 0.484 (1.0x) |

The per-variant tables follow.

**In cache**
- On the P-core, exact division runs 3–3.8x faster than vdivpd (f64) and 2–2.6x faster than vdivps (f32).
- On the E-core it is 5.7–6.1x (f64) and 3.7–4.3x (f32). The E-core's ymm divider is slow (~4.4 cycles per double).
- The exact kernels run at 1.1–1.3x the time of the unguarded mul+FMA (`raw`) when not limited by the per-call
  overhead. At n=256 the guard roughly doubles the in-L1 time: P2 0.164 vs raw 0.077 ns on the P-core, f64
  out-of-place.
- They run at 1.2–2.6x the time of the inexact `x*(1/y)`.

**Memory-bound** (n >= 1 Mi)
- Out-of-place on the P-core, everything converges to the DRAM/L3 rate: 1.0–1.2x.
- In-place f64 on the P-core still gains 1.2–1.4x, because the divider is near the memory rate there.
- On the E-core, f64 division stays compute-bound even at 16 Mi, so the exact kernel gives 2x.
- f32 in-place at 1 Mi/16 Mi on the P-core is 0.92–0.96x, i.e. slightly slower than division (within noise of the
  memory rate).

## Cost of the guard and the slow-path policies

**Normal data (i)**
- P1 = P2 within noise everywhere, because no block is flagged.
- In L1 (n=256 out-of-place) the guard roughly doubles the time over `raw`:
  - P-core f64: 0.077 → 0.164 ns.
  - E-core f64: 0.182 → 0.371 ns.
  - P-core f32: 0.037 → 0.073 ns.
- At n=65536 the gap is 6–10 %, because loads and stores dominate there.
- P3 costs 30–50 % more than P2 on f64 and ~2x on f32. It adds a second `vpcmpgtq`/`vpcmpgtd`, a `vblendv` and an
  `xor` per vector. On the P-core, `vpcmpgtq` issues on one port, which plausibly explains part of this (not
  verified with counters). For f32 on the P-core, P3 is barely faster than vdivps (1.06–1.1x).

**Special values** (n=4096, y=255, out-of-place, ns/element)

| core / type | variant | i normal | ii 10 % zeros | iii 1 % NaN | iv 0.1 % below tlo | v ints 0..255 |
|---|---|---|---|---|---|---|
| P-core f64 | div | 0.514 | 0.514 | 0.542 | 0.528 | 0.542 |
| | raw | 0.163 | 0.162 | 0.171 | 0.225 | 0.171 |
| | P1 | 0.177 | 0.810 | 0.234 | 0.221 | 0.220 |
| | P2 | 0.174 | 0.868 | 0.238 | 0.218 | 0.221 |
| | P3 | 0.203 | 0.203 | 0.213 | 0.269 | 0.214 |
| P-core f32 | div | 0.174 | 0.174 | 0.179 | 0.185 | 0.185 |
| | raw | 0.036 | 0.036 | 0.058 | 0.168 | 0.039 |
| | P1 | 0.066 | 0.456 | 0.239 | 0.097 | 0.116 |
| | P2 | 0.066 | 0.473 | 0.258 | 0.093 | 0.124 |
| | P3 | 0.157 | 0.156 | 0.212 | 0.185 | 0.166 |
| E-core f64 | div | 2.110 | 2.110 | 2.110 | 2.110 | 2.110 |
| | P1 | 0.356 | 2.568 | 0.745 | 0.423 | 0.550 |
| | P2 | 0.358 | 1.483 | 0.533 | 0.423 | 0.445 |
| | P3 | 0.533 | 0.528 | 0.518 | 0.587 | 0.523 |
| E-core f32 | div | 0.677 | 0.660 | 0.660 | 0.660 | 0.660 |
| | P1 | 0.179 | 1.102 | 0.404 | 0.209 | 0.289 |
| | P2 | 0.180 | 0.926 | 0.360 | 0.209 | 0.266 |
| | P3 | 0.422 | 0.392 | 0.392 | 0.424 | 0.392 |

- **10 % zeros.** About 80 % (f64) or 97 % (f32) of blocks are flagged at random, so the per-block branch
  mispredicts. P1 and P2 become 4–7x slower than on normal data and **slower than plain division on the P-core**
  (0.81–0.87 vs 0.514 ns f64; 0.46 vs 0.17 ns f32). P2 helps a little over P1 on the E-core, where division is
  expensive. P3 is unaffected (0.203 ns).
- **1 % NaN.** P1/P2 pay +35 % (f64) to +260 % (f32 P-core). P3 is nearly unaffected.
- **0.1 % tiny values.** Division is needed for the block. For P1/P2 it costs 25–40 % over normal data. Even `raw`
  slows down here (P-core f32 0.036 → 0.168 ns), because `x*zl` produces subnormals, which appears to trigger a
  microcode assist; this was not confirmed with counters. That is why the guard is evaluated before the arithmetic
  and the slow path forms q only when it needs it.
- **Integers 0..255.** 1 in 256 is zero, so 6 % (f64) or 12 % (f32) of blocks are flagged. P2 still beats division
  by 2.3x (f64 P-core) and 1.5x (f32 P-core), and by 4.7x and 2.5x on the E-core.

**Which policy is best**
- P2 (= P1 on clean data; never worse than P1 by more than noise) is best when special values are rare, below
  roughly 0.1–1 % of elements. It is the default `EFD_POLICY_DEFAULT`.
- P3 is best when zeros, NaNs or infinities are frequent. Its cost does not depend on the data.
- An adaptive dispatcher (count flagged blocks over the first chunk, switch to P3) is the obvious next variant. It is
  not implemented.

## Setup cost and break-even

`efdNN_setup` costs, in ns per call (median over 15 × 4096 calls):

| core | f64 random moderate divisors | f64 for a fixed benchmark divisor | f32 random | f32 fixed |
|---|---|---|---|---|
| P-core (win) | 27 | 17–22 | 40 | 19–27 |
| E-core (win) | 43 | 29 | 54 | 28–51 |
| WSL vCPU2 | 24 | 15–23 | 30 | 14–28 |

The fixed-divisor loop is friendlier to the branch predictor than the random set.

Full rows are in `results/bench_tables.md`. Odd significands run the per-divisor check, which adds two scalar
divisions and an fma.

Break-even is the first n (out-of-place, in L1) at which `efdNN_div_array` (setup + P2) is faster than the plain
division loop:

| core | f64 (y = 255, 3, 0.1, √3, 1e-3) | f32 (y = 255, 3, 0.1, 1e-3) |
|---|---|---|
| P-core (win) | 48, 48, 48, 64, 48 | 192, 192, 512, 256 |
| E-core (win) | 16, 16, 16, 24, 16 | 64, 64, 128, 96 |
| WSL vCPU2 | 48, 48, 48, 64, 96 | 192, 192, 256, 192 |

For the f32 divisor √3 (mode DIV) there is no break-even: it is just division plus setup.

## Hot loops (gcc 15.2 -O2 -mavx2 -mfma -ffp-contract=off, WSL binary `bench`)

These are the main 4-vector loops for f64, from `objdump -d --no-show-raw-insn bench`. Each variant has the same
loads, the same stores and the same loop structure. Nothing is hoisted between variants, because each variant is a
separate noinline function. The tails (single-vector loop, then scalar efdNN_div) are not shown.

**`div64_array` (vdivpd)**
```
vmovupd 0x20(%rax),%ymm3
vmovupd (%rax),%ymm4
sub    $0xffffffffffffff80,%rax
sub    $0xffffffffffffff80,%rdx
vmovupd -0x40(%rax),%ymm2
vmovupd -0x20(%rax),%ymm1
vdivpd %ymm0,%ymm3,%ymm3
vdivpd %ymm0,%ymm2,%ymm2
vmovupd %ymm3,-0x60(%rdx)
vdivpd %ymm0,%ymm1,%ymm1
vmovupd %ymm2,-0x40(%rdx)
vdivpd %ymm0,%ymm4,%ymm4
vmovupd %ymm1,-0x20(%rdx)
vmovupd %ymm4,-0x80(%rdx)
cmp    %rax,%r9
jne    <div64_array+0x40>
```

**`mul64_array` (recip = x * (1/y); also the EFD_EXACT loop)**
```
vmulpd 0x20(%rax),%ymm0,%ymm3
sub    $0xffffffffffffff80,%rax
sub    $0xffffffffffffff80,%rdx
vmulpd -0x40(%rax),%ymm0,%ymm2
vmulpd -0x20(%rax),%ymm0,%ymm1
vmulpd -0x80(%rax),%ymm0,%ymm4
vmovupd %ymm3,-0x60(%rdx)
vmovupd %ymm2,-0x40(%rdx)
vmovupd %ymm1,-0x20(%rdx)
vmovupd %ymm4,-0x80(%rdx)
cmp    %rax,%r9
jne    <mul64_array+0x40>
```

**`v64_p1` = efd64 P1/P2 fast path (guard, one branch per 16 doubles, then mul+fma)**
```
vmovupd (%rsi),%ymm5
vmovupd 0x20(%rsi),%ymm4
vmovupd 0x40(%rsi),%ymm3
vmovupd 0x60(%rsi),%ymm2
vpsllq $0x1,%ymm5,%ymm0
vpsllq $0x1,%ymm4,%ymm11
vpsllq $0x1,%ymm3,%ymm1
vpsllq $0x1,%ymm2,%ymm10
vpaddq %ymm6,%ymm0,%ymm0
vpaddq %ymm6,%ymm11,%ymm11
vpaddq %ymm6,%ymm1,%ymm1
vpcmpgtq %ymm7,%ymm0,%ymm0
vpcmpgtq %ymm7,%ymm11,%ymm11
vpcmpgtq %ymm7,%ymm1,%ymm1
vpaddq %ymm6,%ymm10,%ymm10
vpcmpgtq %ymm7,%ymm10,%ymm10
vpor   %ymm11,%ymm0,%ymm0
vpor   %ymm10,%ymm1,%ymm1
vpor   %ymm1,%ymm0,%ymm0
vptest %ymm0,%ymm0
jne    <v64_p1.cold>
vmulpd %ymm5,%ymm9,%ymm0
vfmadd132pd %ymm8,%ymm0,%ymm5
vmulpd %ymm4,%ymm9,%ymm0
vmovupd %ymm5,(%rdi)
vfmadd132pd %ymm8,%ymm0,%ymm4
vmulpd %ymm3,%ymm9,%ymm0
vmovupd %ymm4,0x20(%rdi)
vfmadd132pd %ymm8,%ymm0,%ymm3
vmulpd %ymm2,%ymm9,%ymm0
vmovupd %ymm3,0x40(%rdi)
vfmadd132pd %ymm8,%ymm0,%ymm2
vmovupd %ymm2,0x60(%rdi)
lea    0x10(%rax),%rdx
sub    $0xffffffffffffff80,%rsi
sub    $0xffffffffffffff80,%rdi
cmp    %rdx,%r11
jae    <v64_p1+0xf0>
```

**`v64_p3`, same_sign == 0 path (branchless special lanes; two spill slots on rbp, which are L1-resident)**
```
vmovupd (%rsi),%ymm8
vmulpd %ymm5,%ymm8,%ymm7
vpsllq $0x1,%ymm8,%ymm0
vxorpd %ymm12,%ymm8,%ymm6
vpaddq %ymm15,%ymm0,%ymm3
vpaddq %ymm1,%ymm0,%ymm0
vpcmpgtq %ymm14,%ymm3,%ymm3
vpcmpgtq %ymm2,%ymm0,%ymm0
vfmadd132pd %ymm4,%ymm7,%ymm8
vmovupd 0x20(%rsi),%ymm7
vpandn %ymm0,%ymm3,%ymm0
vmulpd %ymm5,%ymm7,%ymm10
vpsllq $0x1,%ymm7,%ymm9
vblendvpd %ymm3,%ymm6,%ymm8,%ymm8
... (same pattern for vectors 2 and 3) ...
vpor   %ymm9,%ymm0,%ymm0
vptest %ymm0,%ymm0
vblendvpd %ymm10,-0x190(%rbp),%ymm3,%ymm3
jne    <v64_p3.cold+0x1e5>
vmovupd %ymm8,0x0(%r13)
vmovupd %ymm7,0x20(%r13)
vmovupd %ymm6,0x40(%r13)
vmovupd %ymm3,0x60(%r13)
lea    0x10(%rax),%rdx
sub    $0xffffffffffffff80,%rsi
sub    $0xffffffffffffff80,%r13
cmp    %rdx,%r12
jae    <v64_p3+0x330>
```

**`v64_raw` (unguarded mul+fma, inexact outside [tlo, thi))** has the same body as the fast half of `v64_p1`,
without the shift/add/compare/or/ptest lines.

## Per-variant tables (y = 3, data i): median ns/element [min..max]

### win_pcore_lp10 f64, y=3, data i_normal, out-of-place: median ns/element [min..max]

| variant | 256 | 4096 | 65536 | 1048576 | 16777216 |
|---|---|---|---|---|---|
| div | 0.608 [0.608..0.771] | 0.542 [0.542..0.649] | 0.436 [0.436..0.557] | 0.684 [0.668..0.731] | 0.969 [0.936..1.016] |
| recip | 0.064 [0.063..0.081] | 0.170 [0.168..0.202] | 0.137 [0.135..0.154] | 0.534 [0.521..0.625] | 0.977 [0.946..0.994] |
| raw | 0.077 [0.077..0.130] | 0.171 [0.169..0.205] | 0.138 [0.137..0.151] | 0.545 [0.524..0.642] | 0.989 [0.942..1.056] |
| P1 | 0.164 [0.164..0.249] | 0.183 [0.180..0.217] | 0.146 [0.143..0.161] | 0.572 [0.562..0.710] | 0.953 [0.926..1.065] |
| P2 | 0.164 [0.163..0.231] | 0.183 [0.180..0.240] | 0.146 [0.144..0.164] | 0.570 [0.561..0.746] | 0.961 [0.926..1.117] |
| P3 | 0.240 [0.239..0.304] | 0.214 [0.213..0.255] | 0.169 [0.169..0.185] | 0.618 [0.596..0.763] | 0.984 [0.941..1.104] |
| speedup div/P2 | 3.71x | 2.97x | 2.99x | 1.20x | 1.01x |

### win_pcore_lp10 f64, y=3, data i_normal, in-place: median ns/element [min..max]

| variant | 256 | 4096 | 65536 | 1048576 | 16777216 |
|---|---|---|---|---|---|
| div | 0.798 [0.756..0.837] | 0.640 [0.599..0.646] | 0.437 [0.436..0.481] | 0.663 [0.648..0.716] | 0.844 [0.811..0.884] |
| recip | 0.092 [0.092..0.230] | 0.095 [0.089..0.102] | 0.106 [0.105..0.129] | 0.513 [0.432..0.634] | 0.599 [0.590..0.624] |
| raw | 0.134 [0.113..0.440] | 0.111 [0.104..0.115] | 0.106 [0.105..0.120] | 0.562 [0.459..0.633] | 0.636 [0.620..0.705] |
| P1 | 0.411 [0.218..0.908] | 0.189 [0.176..0.531] | 0.115 [0.114..0.209] | 0.535 [0.460..0.570] | 0.622 [0.604..0.649] |
| P2 | 0.450 [0.226..0.615] | 0.190 [0.179..0.197] | 0.115 [0.115..0.703] | 0.541 [0.451..0.620] | 0.642 [0.605..0.670] |
| P3 | 0.585 [0.311..1.018] | 0.261 [0.245..0.266] | 0.170 [0.169..0.283] | 0.505 [0.483..0.589] | 0.615 [0.599..0.726] |
| speedup div/P2 | 1.77x | 3.38x | 3.80x | 1.23x | 1.31x |

### win_pcore_lp10 f32, y=3, data i_normal, out-of-place: median ns/element [min..max]

| variant | 256 | 4096 | 65536 | 1048576 | 16777216 |
|---|---|---|---|---|---|
| div | 0.166 [0.165..0.220] | 0.190 [0.184..0.209] | 0.165 [0.165..0.199] | 0.157 [0.157..0.164] | 0.505 [0.493..0.871] |
| recip | 0.031 [0.031..0.069] | 0.032 [0.031..0.046] | 0.083 [0.081..0.095] | 0.146 [0.146..0.151] | 0.503 [0.423..0.511] |
| raw | 0.037 [0.036..0.088] | 0.040 [0.038..0.046] | 0.084 [0.083..0.105] | 0.147 [0.145..0.155] | 0.511 [0.499..0.526] |
| P1 | 0.072 [0.071..0.182] | 0.072 [0.068..0.096] | 0.087 [0.085..0.143] | 0.148 [0.147..0.155] | 0.502 [0.492..0.565] |
| P2 | 0.073 [0.072..0.158] | 0.073 [0.070..0.098] | 0.086 [0.085..0.142] | 0.148 [0.147..0.170] | 0.503 [0.490..0.536] |
| P3 | 0.153 [0.153..0.327] | 0.175 [0.164..0.246] | 0.147 [0.147..0.240] | 0.151 [0.149..0.166] | 0.558 [0.547..0.598] |
| speedup div/P2 | 2.28x | 2.60x | 1.91x | 1.06x | 1.00x |

### win_pcore_lp10 f32, y=3, data i_normal, in-place: median ns/element [min..max]

| variant | 256 | 4096 | 65536 | 1048576 | 16777216 |
|---|---|---|---|---|---|
| div | 0.202 [0.190..0.203] | 0.209 [0.208..0.212] | 0.165 [0.162..0.186] | 0.219 [0.174..0.264] | 0.304 [0.299..0.311] |
| recip | 0.045 [0.043..0.047] | 0.038 [0.038..0.041] | 0.062 [0.060..0.070] | 0.227 [0.172..0.236] | 0.300 [0.294..0.312] |
| raw | 0.051 [0.048..1.420] | 0.048 [0.047..0.050] | 0.066 [0.061..0.076] | 0.246 [0.184..0.266] | 0.312 [0.305..0.323] |
| P1 | 0.093 [0.087..0.098] | 0.082 [0.082..0.095] | 0.081 [0.069..0.107] | 0.238 [0.179..0.259] | 0.317 [0.310..0.327] |
| P2 | 0.093 [0.087..0.098] | 0.083 [0.082..0.086] | 0.082 [0.068..0.099] | 0.236 [0.185..0.317] | 0.318 [0.314..0.344] |
| P3 | 0.190 [0.178..0.529] | 0.189 [0.187..0.192] | 0.151 [0.143..0.169] | 0.250 [0.184..0.373] | 0.372 [0.331..0.458] |
| speedup div/P2 | 2.17x | 2.53x | 2.03x | 0.92x | 0.96x |

### win_ecore_lp4 f64, y=3, data i_normal, out-of-place: median ns/element [min..max]

| variant | 256 | 4096 | 65536 | 1048576 | 16777216 |
|---|---|---|---|---|---|
| div | 2.110 [2.110..2.450] | 2.110 [2.110..2.323] | 2.110 [2.110..3.678] | 2.251 [2.244..2.380] | 2.623 [2.451..2.807] |
| recip | 0.107 [0.106..0.168] | 0.207 [0.199..0.299] | 0.198 [0.197..0.722] | 1.052 [0.846..1.491] | 1.212 [1.012..1.444] |
| raw | 0.182 [0.181..0.194] | 0.211 [0.204..0.329] | 0.203 [0.201..0.688] | 0.961 [0.863..1.524] | 1.203 [1.017..1.388] |
| P1 | 0.369 [0.361..0.379] | 0.356 [0.344..0.489] | 0.345 [0.331..0.383] | 1.109 [0.960..1.827] | 1.277 [1.228..1.467] |
| P2 | 0.371 [0.359..0.380] | 0.357 [0.348..0.507] | 0.348 [0.332..0.810] | 1.087 [1.017..1.934] | 1.320 [1.222..1.507] |
| P3 | 0.532 [0.528..0.550] | 0.521 [0.511..0.631] | 0.506 [0.484..0.562] | 1.098 [1.040..1.878] | 1.338 [1.270..1.424] |
| speedup div/P2 | 5.68x | 5.92x | 6.06x | 2.07x | 1.99x |

### win_ecore_lp4 f64, y=3, data i_normal, in-place: median ns/element [min..max]

| variant | 256 | 4096 | 65536 | 1048576 | 16777216 |
|---|---|---|---|---|---|
| div | 2.126 [2.123..2.131] | 2.118 [2.114..3.251] | 2.110 [2.110..2.271] | 2.242 [2.235..2.313] | 2.527 [2.442..2.925] |
| recip | 0.125 [0.124..0.126] | 0.132 [0.130..0.282] | 0.159 [0.158..0.204] | 0.714 [0.625..0.930] | 0.892 [0.728..0.958] |
| raw | 0.198 [0.194..0.199] | 0.191 [0.187..0.325] | 0.182 [0.181..0.373] | 0.685 [0.666..0.958] | 0.926 [0.757..1.029] |
| P1 | 0.385 [0.380..0.394] | 0.410 [0.342..0.570] | 0.350 [0.331..0.543] | 0.806 [0.730..1.026] | 0.898 [0.845..1.152] |
| P2 | 0.391 [0.386..0.396] | 0.358 [0.342..0.507] | 0.361 [0.332..0.459] | 0.785 [0.737..1.043] | 0.899 [0.846..1.030] |
| P3 | 0.541 [0.537..0.558] | 0.541 [0.507..0.676] | 0.523 [0.483..0.605] | 0.875 [0.843..1.115] | 0.995 [0.947..1.116] |
| speedup div/P2 | 5.43x | 5.91x | 5.84x | 2.86x | 2.81x |

### win_ecore_lp4 f32, y=3, data i_normal, out-of-place: median ns/element [min..max]

| variant | 256 | 4096 | 65536 | 1048576 | 16777216 |
|---|---|---|---|---|---|
| div | 0.783 [0.783..0.886] | 0.737 [0.737..0.861] | 0.696 [0.696..0.793] | 0.809 [0.796..0.857] | 0.903 [0.869..0.955] |
| recip | 0.066 [0.065..0.069] | 0.077 [0.074..0.091] | 0.107 [0.106..0.110] | 0.278 [0.255..0.298] | 0.557 [0.489..0.689] |
| raw | 0.108 [0.108..0.108] | 0.105 [0.103..0.122] | 0.110 [0.108..0.128] | 0.289 [0.259..0.391] | 0.648 [0.534..0.731] |
| P1 | 0.211 [0.211..0.214] | 0.177 [0.176..0.181] | 0.162 [0.162..0.183] | 0.312 [0.271..0.451] | 0.695 [0.613..0.749] |
| P2 | 0.212 [0.212..0.212] | 0.178 [0.177..0.183] | 0.163 [0.162..0.183] | 0.310 [0.270..0.379] | 0.692 [0.620..0.727] |
| P3 | 0.494 [0.492..0.498] | 0.440 [0.438..0.526] | 0.408 [0.406..0.501] | 0.514 [0.485..0.534] | 0.781 [0.707..0.844] |
| speedup div/P2 | 3.69x | 4.15x | 4.28x | 2.61x | 1.31x |

### win_ecore_lp4 f32, y=3, data i_normal, in-place: median ns/element [min..max]

| variant | 256 | 4096 | 65536 | 1048576 | 16777216 |
|---|---|---|---|---|---|
| div | 0.953 [0.828..1.176] | 0.792 [0.790..0.798] | 0.696 [0.696..0.697] | 0.783 [0.783..0.789] | 0.969 [0.907..1.001] |
| recip | 0.078 [0.076..0.281] | 0.072 [0.070..0.080] | 0.085 [0.084..0.087] | 0.310 [0.305..0.535] | 0.450 [0.389..0.543] |
| raw | 0.117 [0.114..0.328] | 0.117 [0.108..0.120] | 0.096 [0.095..0.097] | 0.333 [0.325..0.487] | 0.466 [0.401..0.510] |
| P1 | 0.357 [0.215..0.503] | 0.194 [0.192..0.199] | 0.162 [0.162..0.255] | 0.373 [0.359..0.544] | 0.506 [0.453..0.607] |
| P2 | 0.363 [0.215..0.482] | 0.193 [0.192..0.200] | 0.162 [0.162..0.172] | 0.362 [0.359..0.451] | 0.518 [0.451..0.603] |
| P3 | 0.700 [0.560..0.982] | 0.471 [0.467..0.475] | 0.409 [0.403..0.411] | 0.563 [0.557..0.617] | 0.711 [0.666..0.853] |
| speedup div/P2 | 2.63x | 4.10x | 4.30x | 2.16x | 1.87x |

### wsl_vcpu2 f64, y=3, data i_normal, out-of-place: median ns/element [min..max]

| variant | 256 | 4096 | 65536 | 1048576 | 16777216 |
|---|---|---|---|---|---|
| div | 0.590 [0.590..0.750] | 0.457 [0.456..0.570] | 0.478 [0.466..0.585] | 0.923 [0.857..1.041] | 1.120 [1.089..1.224] |
| recip | 0.060 [0.059..0.173] | 0.185 [0.160..0.220] | 0.209 [0.182..0.230] | 0.936 [0.872..1.029] | 1.135 [1.110..1.242] |
| raw | 0.074 [0.074..0.088] | 0.192 [0.144..0.252] | 0.163 [0.156..0.584] | 0.876 [0.810..0.925] | 1.104 [1.073..1.238] |
| P1 | 0.162 [0.162..0.191] | 0.245 [0.149..0.437] | 0.175 [0.164..0.339] | 0.899 [0.844..0.975] | 1.120 [1.074..1.253] |
| P2 | 0.163 [0.162..0.191] | 0.237 [0.149..0.469] | 0.176 [0.166..0.513] | 0.908 [0.831..0.995] | 1.092 [1.062..1.302] |
| P3 | 0.234 [0.233..0.360] | 0.311 [0.179..0.662] | 0.196 [0.185..0.382] | 0.935 [0.890..1.015] | 1.125 [1.079..1.360] |
| speedup div/P2 | 3.62x | 1.92x | 2.71x | 1.02x | 1.03x |

### wsl_vcpu2 f64, y=3, data i_normal, in-place: median ns/element [min..max]

| variant | 256 | 4096 | 65536 | 1048576 | 16777216 |
|---|---|---|---|---|---|
| div | 0.664 [0.638..0.683] | 0.512 [0.508..0.515] | 0.503 [0.502..0.625] | 0.862 [0.837..0.971] | 1.035 [0.936..1.044] |
| recip | 0.080 [0.074..0.378] | 0.079 [0.076..0.083] | 0.131 [0.123..0.147] | 0.601 [0.576..0.645] | 0.669 [0.639..0.692] |
| raw | 0.100 [0.093..0.110] | 0.091 [0.087..0.095] | 0.131 [0.122..0.390] | 0.580 [0.561..0.716] | 0.659 [0.636..0.691] |
| P1 | 0.192 [0.183..0.200] | 0.154 [0.151..0.158] | 0.146 [0.136..1.627] | 0.661 [0.581..0.770] | 0.712 [0.684..0.801] |
| P2 | 0.190 [0.183..0.198] | 0.153 [0.150..0.156] | 0.148 [0.136..0.186] | 0.672 [0.564..0.806] | 0.705 [0.647..0.865] |
| P3 | 0.271 [0.261..0.280] | 0.206 [0.204..0.208] | 0.210 [0.195..0.842] | 0.651 [0.536..0.776] | 0.767 [0.702..0.865] |
| speedup div/P2 | 3.49x | 3.34x | 3.40x | 1.28x | 1.47x |

### wsl_vcpu2 f32, y=3, data i_normal, out-of-place: median ns/element [min..max]

| variant | 256 | 4096 | 65536 | 1048576 | 16777216 |
|---|---|---|---|---|---|
| div | 0.286 [0.285..0.369] | 0.262 [0.261..0.353] | 0.161 [0.161..0.285] | 0.178 [0.176..0.288] | 0.497 [0.487..0.534] |
| recip | 0.052 [0.052..0.068] | 0.042 [0.042..0.053] | 0.106 [0.102..0.117] | 0.184 [0.181..0.227] | 0.499 [0.490..0.522] |
| raw | 0.067 [0.060..0.100] | 0.053 [0.053..0.256] | 0.091 [0.081..0.134] | 0.173 [0.169..0.205] | 0.484 [0.475..0.512] |
| P1 | 0.132 [0.131..0.229] | 0.119 [0.118..0.282] | 0.108 [0.085..0.182] | 0.180 [0.176..0.217] | 0.484 [0.471..0.543] |
| P2 | 0.133 [0.133..0.171] | 0.119 [0.118..0.150] | 0.110 [0.085..0.180] | 0.178 [0.176..0.346] | 0.484 [0.470..0.527] |
| P3 | 0.267 [0.266..0.498] | 0.240 [0.239..0.302] | 0.185 [0.146..0.313] | 0.189 [0.185..0.209] | 0.503 [0.495..0.546] |
| speedup div/P2 | 2.15x | 2.20x | 1.46x | 1.00x | 1.03x |

### wsl_vcpu2 f32, y=3, data i_normal, in-place: median ns/element [min..max]

| variant | 256 | 4096 | 65536 | 1048576 | 16777216 |
|---|---|---|---|---|---|
| div | 0.326 [0.310..0.327] | 0.324 [0.323..0.328] | 0.185 [0.166..0.209] | 0.180 [0.174..0.195] | 0.301 [0.288..0.305] |
| recip | 0.071 [0.066..0.076] | 0.058 [0.057..0.063] | 0.070 [0.063..0.224] | 0.278 [0.256..0.309] | 0.293 [0.281..0.299] |
| raw | 0.084 [0.080..0.095] | 0.076 [0.073..0.087] | 0.100 [0.063..0.128] | 0.158 [0.149..0.213] | 0.292 [0.288..0.297] |
| P1 | 0.159 [0.151..0.182] | 0.151 [0.150..0.155] | 0.147 [0.074..0.200] | 0.162 [0.154..0.199] | 0.334 [0.289..0.355] |
| P2 | 0.159 [0.151..0.517] | 0.151 [0.150..0.155] | 0.139 [0.074..0.209] | 0.163 [0.155..0.185] | 0.322 [0.291..0.345] |
| P3 | 0.305 [0.290..0.325] | 0.296 [0.295..0.301] | 0.275 [0.150..0.401] | 0.171 [0.163..0.222] | 0.316 [0.308..0.338] |
| speedup div/P2 | 2.05x | 2.15x | 1.33x | 1.11x | 0.94x |

The complete tables (all divisors, all data sets, both core types, setup and break-even rows) are in
`results/bench_tables.md`. The merged raw data is in `results/bench_core_ultra_7_155u.json`.
