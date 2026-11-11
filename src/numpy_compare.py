"""In-process comparison with a shipped consumer: NumPy's `np.true_divide(array, scalar)`.

Loads native/efd.dll (see native/efd_dll.c) with ctypes and, for several divisors, sizes and data kinds,
 (1) checks that the kernel's output is bit-identical to NumPy's (NaN compared as NaN), and
 (2) times  np.true_divide(a, s, out=o)  against  efd.efdNN_array(o, a, n, s)  (best of several repeats).
Both write into a preallocated output array. This measures what a NumPy user would see for `a / s` if the
float loops had a scalar-divisor fast path; it is not a NumPy patch.

Run on a quiet machine:  python src/numpy_compare.py  [> results/numpy_compare.json]
"""
import ctypes, json, os, platform, sys, time
import numpy as np

here = os.path.dirname(os.path.abspath(__file__))
dll = ctypes.CDLL(os.path.join(here, '..', 'native', 'efd.dll'))
# raw addresses (taken once per array) keep the ctypes call overhead well below a microsecond
for name, ct in (('efd64_array', ctypes.c_double), ('vdiv64_array', ctypes.c_double),
                 ('efd32_array', ctypes.c_float), ('vdiv32_array', ctypes.c_float)):
    fn = getattr(dll, name)
    fn.argtypes = [ctypes.c_void_p, ctypes.c_void_p, ctypes.c_size_t, ct]
    fn.restype = None
dll.efd64_mode.argtypes = [ctypes.c_double]
dll.efd32_mode.argtypes = [ctypes.c_float]


def best(f, reps):
    b = float('inf')
    for _ in range(reps):
        t = time.perf_counter()
        f()
        b = min(b, time.perf_counter() - t)
    return b


def same_bits(a, b):
    ua = a.view(np.uint64 if a.dtype == np.float64 else np.uint32)
    ub = b.view(ua.dtype)
    return bool(np.all((ua == ub) | (np.isnan(a) & np.isnan(b))))


def data(kind, n, dtype, rng):
    if kind == 'normal':
        a = rng.standard_normal(n)
    elif kind == 'uint8':
        a = rng.integers(0, 256, n).astype(np.float64)
    elif kind == 'zeros10':
        a = rng.standard_normal(n)
        a[rng.random(n) < 0.10] = 0.0
    elif kind == 'nan1':
        a = rng.standard_normal(n)
        a[rng.random(n) < 0.01] = np.nan
    elif kind == 'wide':                       # magnitudes over the whole exponent range, incl. subnormals
        a = np.ldexp(rng.standard_normal(n), rng.integers(-1070, 1000, n)) if dtype == np.float64 \
            else np.ldexp(rng.standard_normal(n), rng.integers(-145, 120, n))
    return np.ascontiguousarray(a.astype(dtype))


def main():
    rng = np.random.default_rng(20261110)
    out = dict(numpy=np.__version__, python=sys.version.split()[0], machine=platform.processor(),
               simd=str(getattr(np._core._multiarray_umath, '__cpu_features__', {}).get('AVX2', '?')), rows=[])
    divisors = [255.0, 3.0, 0.1, 1.7320508075688772, 1e-3, 1000.0]
    all_same = True
    for dtype, efd, vdiv, modef in ((np.float64, dll.efd64_array, dll.vdiv64_array, dll.efd64_mode),
                                    (np.float32, dll.efd32_array, dll.vdiv32_array, dll.efd32_mode)):
        for n in (1024, 4096, 65536, 1 << 20, 1 << 24):
            reps = max(7, min(20000, int(6e7 // n)))
            for kind in ('normal', 'uint8', 'zeros10', 'nan1', 'wide'):
                a = data(kind, n, dtype, rng)
                o1 = np.empty_like(a); o2 = np.empty_like(a); o3 = np.empty_like(a)
                pa, p2, p3 = a.ctypes.data, o2.ctypes.data, o3.ctypes.data
                for s in divisors:
                    if kind != 'normal' and s not in (255.0, 0.1):
                        continue
                    sc = dtype(s)
                    with np.errstate(all='ignore'):
                        np.true_divide(a, sc, out=o1)
                        efd(p2, pa, n, float(sc))
                        ok = same_bits(o1, o2)
                        all_same &= ok
                        t_np = best(lambda: np.true_divide(a, sc, out=o1), reps)
                        fs = float(sc)
                        t_efd = best(lambda: efd(p2, pa, n, fs), reps)
                        t_vdiv = best(lambda: vdiv(p3, pa, n, fs), reps)
                    out['rows'].append(dict(dtype=np.dtype(dtype).name, n=n, data=kind, divisor=s,
                                            mode=modef(float(sc)), bit_identical=ok,
                                            numpy_ns=round(t_np / n * 1e9, 4), efd_ns=round(t_efd / n * 1e9, 4),
                                            vdiv_ns=round(t_vdiv / n * 1e9, 4),
                                            speedup_vs_numpy=round(t_np / t_efd, 3)))
    out['all_bit_identical'] = all_same
    json.dump(out, sys.stdout, indent=1)
    print(file=sys.stderr)
    print('all outputs bit-identical to NumPy:', all_same, file=sys.stderr)
    for r in out['rows']:
        if r['data'] in ('normal', 'uint8') and r['divisor'] in (255.0, 0.1):
            print('%-8s n=%-9d %-8s /%-6g mode=%d  numpy %.3f  kernel %.3f  vdiv-loop %.3f ns/elt  speedup %.2fx' % (
                r['dtype'], r['n'], r['data'], r['divisor'], r['mode'], r['numpy_ns'], r['efd_ns'], r['vdiv_ns'],
                r['speedup_vs_numpy']), file=sys.stderr)


if __name__ == '__main__':
    main()
