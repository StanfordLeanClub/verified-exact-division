from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import subprocess

root=Path(__file__).resolve().parent
tmp=root/'compiler_tmp';tmp.mkdir(exist_ok=True)
env=os.environ.copy();env['TMP']=env['TEMP']=str(tmp)
cmd=['clang','-O2','-mavx2','-mfma','-ffp-contract=off',str(root/'native/check_correspondence.c'),'-o',str(root/'check_correspondence.exe')]
subprocess.run(cmd,env=env,check=True)
stamp=datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S')
exe=root/'check_correspondence.exe'
with (root/'results'/f'native_{stamp}.jsonl').open('w') as out, (root/'results'/f'native_{stamp}.stderr.log').open('w') as err:
    r=subprocess.run([str(exe)],stdout=out,stderr=err)
(root/'results'/f'native_{stamp}.meta.json').write_text(json.dumps(dict(command=cmd,exit_code=r.returncode,exe_sha256=hashlib.sha256(exe.read_bytes()).hexdigest()),indent=2))
print('Native replay',stamp,'exit code',r.returncode)
raise SystemExit(r.returncode)
