"""Paired ratios with every measured round retained; no workload filtering."""
from pathlib import Path
from collections import defaultdict
import gzip,json,random,statistics as st,sys
root=Path(__file__).resolve().parent
paths=[Path(p) for p in sys.argv[1:]] or sorted((root/'results').glob('tight_bench_cpu*.jsonl')) or sorted((root/'results').glob('tight_bench_cpu*.jsonl.gz'))
rng=random.Random(20261112);rows=[];metadata=[]
pairs=[('original','selected'),('selected','tight_context'),('selected','tight_direct'),
       ('tight_context','tight_direct'),('original','tight_direct'),('division','tight_direct')]
for path in paths:
    text=gzip.decompress(path.read_bytes()).decode() if path.suffix=='.gz' else path.read_text()
    records=[json.loads(s) for s in text.splitlines()]
    meta=next(r for r in records if r['type']=='metadata')
    times=[r for r in records if r['type']=='system_times']
    assert len(times)==2
    idle=times[1]['idle']-times[0]['idle']
    total=times[1]['kernel']-times[0]['kernel']+times[1]['user']-times[0]['user']
    meta.update(raw_file=path.name,busy_fraction=1-idle/total);metadata.append(meta)
    groups=defaultdict(lambda:defaultdict(dict))
    for r in records:
        if r['type']=='trial':
            assert r['processor']==meta['logical_processor']
            groups[r['n'],r['distribution']][r['variant']][r['round']]=r['ns_per_element']
    for (n,dist),vs in groups.items():
        row=dict(cpu=meta['logical_processor'],n=n,distribution=dist,
                 median_ns={v:st.median(xs.values()) for v,xs in vs.items()},ratios={})
        for a,b in pairs:
            assert vs[a].keys()==vs[b].keys() and len(vs[a])==31
            ratios=[vs[a][r]/vs[b][r] for r in sorted(vs[a])]
            boot=sorted(st.median(rng.choices(ratios,k=len(ratios))) for _ in range(5000))
            row['ratios'][a+'/'+b]=dict(median=st.median(ratios),ci95=[boot[125],boot[4874]])
        rows.append(row)
report=dict(metadata=metadata,groups=rows)
(root/'results/tight_summary.json').write_text(json.dumps(report,indent=2))
lines=['# Tightened /3 benchmark','',
       'Paired randomized order, 3 warm-ups, 31 measured rounds, 5,000 bootstrap resamples. All trials retained. Ratios above 1 favor the denominator. One Intel Core Ultra 7 155U; within-run intervals do not establish cross-machine results. No local Lean build overlapped timing.','',
       '| CPU | n | Data | Selected ns | Tight context ns | Tight direct ns | Selected / direct [95%] |',
       '|---:|---:|---|---:|---:|---:|---|']
for r in rows:
    ns=r['median_ns'];sp=r['ratios']['selected/tight_direct']
    lines.append(f'| {r["cpu"]} | {r["n"]} | {r["distribution"]} | {ns["selected"]:.4f} | {ns["tight_context"]:.4f} | {ns["tight_direct"]:.4f} | {sp["median"]:.3f} [{sp["ci95"][0]:.3f}, {sp["ci95"][1]:.3f}] |')
(root/'BENCH_RESULTS.md').write_text('\n'.join(lines)+'\n')
for r in rows:
    if r['n'] in [32,4096,16777216] and r['distribution'] in ['normal','tiny0.1pct','tiny10pct','new_guard_band']:
        print(json.dumps(r))
print('Resolved regressions vs selected:',[(r['cpu'],r['n'],r['distribution']) for r in rows if r['ratios']['selected/tight_direct']['ci95'][1]<1])
