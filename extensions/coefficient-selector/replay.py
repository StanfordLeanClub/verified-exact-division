"""Fresh source replay with enforced axiom policy and real negative controls.

Default: `lake env lean` in lean/. Offline replay may supply --lean and
--lean-path-file for an installed, pinned Mathlib cache. That alternative does
not establish that a fresh Lake dependency installation succeeds.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse, hashlib, json, os, re, subprocess, time
from proof_policy import audit_output, source_policy, parser_negative_controls

def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    root=Path(__file__).resolve().parent
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--lean')
    ap.add_argument('--lean-path-file',type=Path)
    args=ap.parse_args()
    env=os.environ.copy()
    if args.lean_path_file:
        if not args.lean: ap.error('--lean-path-file requires --lean')
        env['LEAN_PATH']=args.lean_path_file.read_text().strip()
    lean=[args.lean] if args.lean else ['lake','env','lean']
    sources=[]
    for ns,mods in [('ExactFDiv','Basic Main General Bounded IEEE Setup Final Exists RNE Checker Algorithm Audit'),
                    ('Selector','Stability Candidates Checker Scaling Instances Audit'),
                    ('Div3IEEE','Bridge Core Encoding Guard Array Tight Flags Cases Audit')]:
        sources += [root/'lean'/ns/(m+'.lean') for m in mods.split()]
    imports=[]; bodies=[]; records=[]; expected=[]
    for p in sources:
        content=p.read_text(encoding='utf-8'); source_policy(content)
        if re.search(r'(?m)^private\s',content): raise ValueError('Private declarations require a module replay')
        records.append(dict(path=p.relative_to(root).as_posix(),sha256=sha(p)))
        expected += re.findall(r'(?m)^#print axioms (\S+)\s*$',content)
        body=[]
        for line in content.splitlines():
            if line.startswith('import '):
                if line.startswith('import Mathlib.'):
                    if line not in imports: imports.append(line)
                elif not re.match(r'import (ExactFDiv|Selector|Div3IEEE)\.',line):
                    raise ValueError('Unexpected import: '+line)
            else: body.append(line)
        bodies.append('\n/- Source: '+p.relative_to(root).as_posix()+' -/\nsection\n'+'\n'.join(body)+'\nend\n')
    if len(expected)!=107 or len(set(expected))!=107:
        raise ValueError('Published audit inventory changed; review policy and inventory explicitly')
    stamp=datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S')
    out=root/'results'; out.mkdir(exist_ok=True)
    target=out/f'Replay_{stamp}.lean'
    target.write_text('\n'.join(imports+bodies),encoding='utf-8')
    record=dict(sources=records,combined_sha256=sha(target),accepted=False)
    start=time.monotonic()
    try:
        parser_controls=parser_negative_controls()
        # Lean accepts these with exit 0. Only the policy must reject them.
        rejected=[]
        for name,code in [
            ('admitted', 'theorem probe : True := by sorry\n#print axioms probe\n'),
            ('added_axiom', 'axiom inventedAssumption : False\ntheorem probe : False := inventedAssumption\n#print axioms probe\n')]:
            probe=out/f'Negative_{name}_{stamp}.lean'; probe.write_text(code)
            r=subprocess.run(lean+[str(probe)],cwd=root/'lean',env=env,capture_output=True,text=True)
            (out/f'Negative_{name}_{stamp}.log').write_text(r.stdout+r.stderr)
            if r.returncode: raise RuntimeError('Negative control failed before policy inspection')
            try: audit_output(r.stdout+r.stderr,['probe'])
            except ValueError: rejected.append(name)
            else: raise RuntimeError('Admitted/axiomatic proof incorrectly accepted')
        print(f'Replaying {len(sources)} source modules; project theorems are not imported from oleans',flush=True)
        r=subprocess.run(lean+[str(target)],cwd=root/'lean',env=env,capture_output=True,text=True)
        output=r.stdout+r.stderr
        (out/f'Replay_{stamp}.log').write_text(output,encoding='utf-8')
        record['lean_exit_code']=r.returncode
        if r.returncode: raise RuntimeError('Lean replay failed')
        record.update(audited_declarations=audit_output(output,expected),
                      parser_negative_controls=parser_controls,
                      real_lean_negative_controls=rejected,accepted=True)
    finally:
        record['seconds']=time.monotonic()-start
        record['mode']='explicit Lean and installed Mathlib cache' if args.lean else 'Lake environment'
        (out/f'Replay_{stamp}.json').write_text(json.dumps(record,indent=2)+'\n')
    (out/'proof_acceptance.json').write_text(json.dumps(record,indent=2)+'\n')
    print('Accepted:',record['audited_declarations'],'audited declarations; negative controls rejected',flush=True)

if __name__=='__main__': main()
