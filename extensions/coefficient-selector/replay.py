"""Independent source replay with one Mathlib import. No prior project oleans used.

Concatenation preserves declaration order and namespaces. The sources have no
private declarations or module-dependent names. Internal imports are replaced by
their exact source text; Mathlib imports stay external. The ordinary module build
is also required and separately recorded.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib,json,os,subprocess,time
root=Path(__file__).resolve().parent
sources=[]
for ns,mods in [('ExactFDiv','Basic Main General Bounded IEEE Setup Final Exists RNE Checker Algorithm Audit'),
                ('Selector','Stability Candidates Checker Scaling Instances Audit')]:
    sources += [root/'lean'/ns/(m+'.lean') for m in mods.split()]
sources += [root/'lean/Div3IEEE'/(m+'.lean') for m in 'Bridge Core Encoding Guard Array Tight Flags Cases Audit'.split()]
imports=[];bodies=[];records=[]
for p in sources:
    content=p.read_text(encoding='utf-8')
    assert '\nprivate ' not in content
    records.append(dict(path=str(p.relative_to(root)),sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
    body=[]
    for line in content.splitlines():
        if line.startswith('import '):
            if line.startswith('import Mathlib.') and line not in imports: imports.append(line)
        else: body.append(line)
    bodies.append('\n/- Source: '+str(p.relative_to(root)).replace('\\','/')+' -/\nsection\n'+'\n'.join(body)+'\nend\n')
stamp=datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S')
target=root/'results'/f'Replay_{stamp}.lean'
target.write_text('\n'.join(imports+bodies),encoding='utf-8')
env=os.environ.copy()
cmd=['lake','env','lean',str(target)];start=time.time()
print('Replaying',len(sources),'source modules; only Mathlib oleans on LEAN_PATH',flush=True)
with (root/'results'/f'Replay_{stamp}.log').open('w',encoding='utf-8') as log:
    r=subprocess.run(cmd,cwd=root/'lean',env=env,stdout=log,stderr=subprocess.STDOUT)
record=dict(exit_code=r.returncode,seconds=time.time()-start,command=cmd,sources=records,
            combined_sha256=hashlib.sha256(target.read_bytes()).hexdigest())
(root/'results'/f'Replay_{stamp}.json').write_text(json.dumps(record,indent=2),encoding='utf-8')
print('Replay',stamp,'exit',r.returncode,flush=True)
raise SystemExit(r.returncode)
