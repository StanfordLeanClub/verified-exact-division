#!/usr/bin/env python3
"""Merge bench JSONL runs into one JSON file and print Markdown tables.
usage: summarize.py out.json run1.jsonl [run2.jsonl ...]  > tables.md"""
import json, sys, statistics, collections

out = sys.argv[1]
recs, meta, divs, setup, be = [], [], {}, [], []
for fn in sys.argv[2:]:
    for line in open(fn, encoding='utf-8', errors='replace'):
        line = line.strip().lstrip('﻿')
        if not line.startswith('{'):
            continue
        r = json.loads(line)
        r['source_file'] = fn.split('/')[-1]
        k = r.get('kind')
        if k in ('meta', 'meta_end'): meta.append(r)
        elif k == 'divisor': divs[r['divisor']] = r
        elif k == 'setup': setup.append(r)
        elif k == 'breakeven': be.append(r)
        else: recs.append(r)
json.dump({'meta': meta, 'divisors': list(divs.values()), 'setup': setup, 'breakeven': be, 'throughput': recs},
          open(out, 'w'), indent=1)

labels = sorted({r['cpu_label'] for r in recs})
VARS = ['div', 'recip', 'raw', 'P1', 'P2', 'P3', 'P3X', 'P4']
SIZES = [256, 4096, 65536, 1 << 20, 1 << 24]
def key(r): return (r['cpu_label'], r['type'], r['variant'], r['divisor'], r['data'], r['n'], r['inplace'])
idx = {key(r): r for r in recs}
def cell(lab, t, v, d, data, n, ip, field='median_ns'):
    r = idx.get((lab, t, v, d, data, n, ip))
    return r[field] if r else None
def fmt(x): return '-' if x is None else ('%.3f' % x)

print('# divisor setup\n')
print('| divisor | f64 mode | f64 same_sign | f32 mode | f32 same_sign |')
print('|---|---|---|---|---|')
mn = {0: 'DIV', 1: 'EXACT', 2: 'FMA'}
for d in divs.values():
    print('| %.17g | %s | %d | %s | %d |' % (d['divisor'], mn[d['f64_mode']], d['f64_same_sign'], mn[d['f32_mode']], d['f32_same_sign']))

for lab in labels:
    rl = [r for r in recs if r['cpu_label'] == lab]
    ghz = [r['core_ghz'] for r in rl]; ld = [r['load1'] for r in rl]
    print('\n# %s: core clock (dependent-add probe) median %.2f GHz (min %.2f, max %.2f); load1 median %.2f (min %.2f, max %.2f); vCPUs seen %s\n'
          % (lab, statistics.median(ghz), min(ghz), max(ghz), statistics.median(ld), min(ld), max(ld), sorted({r['vcpu'] for r in rl})))
    for t in ('f64', 'f32'):
        for d in (3.0, 255.0):
            for ip in (0, 1):
                print('\n## %s %s, y=%g, data i_normal, %s: median ns/element [min..max]\n' % (lab, t, d, 'in-place' if ip else 'out-of-place'))
                print('| variant | ' + ' | '.join(str(n) for n in SIZES) + ' |')
                print('|---|' + '---|' * len(SIZES))
                for v in VARS:
                    cs = []
                    for n in SIZES:
                        r = idx.get((lab, t, v, d, 'i_normal', n, ip))
                        cs.append('-' if not r else '%.3f [%.3f..%.3f]' % (r['median_ns'], r['min_ns'], r['max_ns']))
                    print('| %s | %s |' % (v, ' | '.join(cs)))
                dv = [cell(lab, t, 'div', d, 'i_normal', n, ip) for n in SIZES]
                for v in ('P2', 'P3', 'P4', 'recip'):
                    xs = [cell(lab, t, v, d, 'i_normal', n, ip) for n in SIZES]
                    print('| speedup div/%s | %s |' % (v, ' | '.join('-' if a is None or b is None else '%.2fx' % (a / b) for a, b in zip(dv, xs))))
        # data sensitivity
        for n in (4096, 65536, 1 << 20):
            for d in (255.0, 3.0, 0.1, 1.7320508075688772, 0.001):
                rows = [r for r in rl if r['type'] == t and r['n'] == n and r['divisor'] == d and r['inplace'] == 0]
                if not rows: continue
                datas = ['i_normal', 'ii_10pct_zero', 'iii_1pct_nan', 'iv_0.1pct_below_tlo', 'v_int_0_255']
                if not any(cell(lab, t, 'div', d, x, n, 0) for x in datas[1:]): continue
                print('\n## %s %s n=%d y=%.17g out-of-place: median ns/element by data\n' % (lab, t, n, d))
                print('| variant | ' + ' | '.join(datas) + ' |')
                print('|---|' + '---|' * len(datas))
                for v in VARS:
                    print('| %s | %s |' % (v, ' | '.join(fmt(cell(lab, t, v, d, x, n, 0)) for x in datas)))
    # all-divisor view at 4096 and 1M, data i
    for t in ('f64', 'f32'):
        print('\n## %s %s data i_normal out-of-place, all divisors: median ns/element (n=4096 / n=1M)\n' % (lab, t))
        print('| divisor | mode | ' + ' | '.join(VARS) + ' |')
        print('|---|---|' + '---|' * len(VARS))
        for d in divs.values():
            y = d['divisor']; m = mn[d['f64_mode' if t == 'f64' else 'f32_mode']]
            print('| %.17g | %s | %s |' % (y, m, ' | '.join('%s / %s' % (fmt(cell(lab, t, v, y, 'i_normal', 4096, 0)), fmt(cell(lab, t, v, y, 'i_normal', 1 << 20, 0))) for v in VARS)))

if setup:
    print('\n# setup cost (ns per efdNN_setup call, median of 15 x 4096 calls)\n')
    print('| cpu | divisor | f64 median | f64 min | f32 median | f32 min | load1 |')
    print('|---|---|---|---|---|---|---|')
    for s in setup:
        print('| %s | %s | %.1f | %.1f | %.1f | %.1f | %.2f |' % (s['cpu_label'], s['divisor'], s['f64_setup_ns_median'], s['f64_setup_ns_min'],
                                                           s['f32_setup_ns_median'], s['f32_setup_ns_min'], s['load1']))
if be:
    print('\n# break-even: ns per call, out-of-place, in L1 (div vs entry = setup + default policy P4 vs P4 with precomputed setup)\n')
    g = collections.defaultdict(dict)
    for r in be: g[(r['cpu_label'], r['type'], r['divisor'], r['n'])][r['variant']] = r['median_ns_per_call']
    for (lab, t, d) in sorted({(k[0], k[1], k[2]) for k in g}):
        ns = sorted(k[3] for k in g if k[:3] == (lab, t, d))
        print('\n## %s %s y=%.17g\n' % (lab, t, d))
        print('| n | div | entry | P4 (no setup) |'); print('|---|---|---|---|')
        first = None
        for n in ns:
            e = g[(lab, t, d, n)]
            if first is None and e.get('entry', 1e9) < e.get('div', 0): first = n
            print('| %d | %.1f | %.1f | %.1f |' % (n, e.get('div', float('nan')), e.get('entry', float('nan')), e.get('P4', float('nan'))))
        print('\nfirst n where entry < div: %s' % first)
