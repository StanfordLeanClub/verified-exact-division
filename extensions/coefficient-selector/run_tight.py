from datetime import datetime,timezone
from pathlib import Path
import hashlib,json,os,subprocess,sys
root=Path(__file__).resolve().parent
mode=sys.argv[1] if len(sys.argv)>1 else 'validate'
cpu=sys.argv[2] if len(sys.argv)>2 else '10'
tmp=root/'compiler_tmp';tmp.mkdir(exist_ok=True)
env=os.environ.copy();env['TMP']=env['TEMP']=str(tmp)
exe=root/'bench_tight.exe'
cmd=['clang','-O2','-mavx2','-mfma','-ffp-contract=off',str(root/'native/bench_tight.c'),'-o',str(exe)]
subprocess.run(cmd,env=env,check=True)
stamp=datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S')
run=[str(exe),cpu,'31']+([] if mode=='bench' else [mode])
stem=f'tight_{mode}_cpu{cpu}_{stamp}'
with (root/'results'/(stem+'.jsonl')).open('w') as out,(root/'results'/(stem+'.stderr.log')).open('w') as err:
    r=subprocess.run(run,stdout=out,stderr=err)
meta=dict(command=cmd,run=run,exit_code=r.returncode,exe_sha256=hashlib.sha256(exe.read_bytes()).hexdigest(),
          source_sha256=hashlib.sha256((root/'native/bench_tight.c').read_bytes()).hexdigest(),
          header_sha256=hashlib.sha256((root/'native/div3_tight.h').read_bytes()).hexdigest())
(root/'results'/(stem+'.meta.json')).write_text(json.dumps(meta,indent=2))
print(stem,'exit',r.returncode,flush=True)
raise SystemExit(r.returncode)
