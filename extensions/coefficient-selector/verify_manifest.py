from pathlib import Path
import hashlib,json
root=Path(__file__).resolve().parent
m=json.loads((root/'MANIFEST.json').read_text())
for name,sha in m['files'].items():
    assert hashlib.sha256((root/name).read_bytes()).hexdigest()==sha,name
print('Verified',len(m['files']),'file hashes')
