"""Independent native acceptance, including executable negative controls.

Python 3, Clang, llvm-objdump, x86-64 AVX2/FMA. No fast-math or LTO.
SoftFloat is downloaded from its author and pinned by archive SHA-256.
Nothing in this script is a formal proof or a performance measurement.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse, hashlib, json, os, re, shutil, subprocess, time, urllib.request, zipfile

ROOT = Path(__file__).resolve().parent
SF_URL = 'https://www.jhauser.us/arithmetic/SoftFloat-3e.zip'
SF_SHA = '21130ce885d35c1fe73fc1e1bf2244178167e05c6747cad5f450cc991714c746'
SF_SOURCES = ['f32_div.c', 's_normSubnormalF32Sig.c', 's_roundPackToF32.c',
              'softfloat_state.c', '8086-SSE/softfloat_raiseFlags.c',
              '8086-SSE/s_propagateNaNF32UI.c']

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def run(cmd, log, env):
    p = subprocess.run([str(x) for x in cmd], env=env, capture_output=True, text=True)
    Path(log).write_text(p.stdout+p.stderr, encoding='utf-8')
    if p.returncode:
        raise RuntimeError(f'Command failed ({p.returncode}); see {log}')
    return p.stdout

def extract_verified(archive, destination):
    if sha(archive) != SF_SHA:
        raise RuntimeError('SoftFloat archive SHA-256 mismatch')
    with zipfile.ZipFile(archive) as z:
        for name in z.namelist():
            if not (destination/name).resolve().is_relative_to(destination.resolve()):
                raise RuntimeError('Archive path escapes destination')
        z.extractall(destination)
    return destination/'SoftFloat-3e'

def mutant_header(original, name):
    # Mutate a copy of the actual header; never modify the production source.
    if name == 'no_guard':
        a = original.replace('!_mm256_testz_si256(flags,flags)', '0')
        return a.replace('(m>0 && m<0x0d400000u)', '(0)')
    if name == 'wrong_high_coefficient':
        return original.replace('0x1.555554p-2f', '0x1.555556p-2f')
    if name == 'only_lane_zero':
        return original.replace('!_mm256_testz_si256(flags,flags)',
            '(_mm256_movemask_ps(_mm256_castsi256_ps(flags)) & 1)')
    if name == 'unfused':
        old = '_mm256_fmadd_ps(x[j],_mm256_set1_ps(0x1.555554p-2f),'
        new = '_mm256_add_ps(_mm256_mul_ps(x[j],_mm256_set1_ps(0x1.555554p-2f)),'
        return original.replace(old,new).replace('fmaf(x,0x1.555554p-2f,x*0x1.555556p-26f)',
                                                 '(x*0x1.555554p-2f+x*0x1.555556p-26f)')
    raise ValueError(name)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--exhaustive', action='store_true')
    ap.add_argument('--softfloat-archive', type=Path)
    ap.add_argument('--clang', default='clang')
    ap.add_argument('--objdump', default='llvm-objdump')
    args=ap.parse_args()
    stamp=datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S')
    work=ROOT/'acceptance_work'/stamp
    work.mkdir(parents=True)
    env=os.environ.copy(); env['TMP']=env['TEMP']=str(work)
    archive=args.softfloat_archive
    if archive is None:
        archive=work/'SoftFloat-3e.zip'
        urllib.request.urlretrieve(SF_URL, archive)
    sf=extract_verified(archive,work/'reference')
    # Use the upstream GCC platform configuration; Clang implements its builtins.
    includes=['-I'+str(sf/'build/Linux-x86_64-GCC'),'-I'+str(sf/'source/8086-SSE'),
              '-I'+str(sf/'source/include')]
    opts=['-O2','-std=c11','-DSOFTFLOAT_FAST_INT64','-DSOFTFLOAT_FAST_DIV64TO32',
          '-DINLINE_LEVEL=5','-DSOFTFLOAT_ROUND_ODD']
    commands=[]; objects=[]
    for i,name in enumerate(SF_SOURCES):
        obj=work/f'sf_{i}.obj'
        cmd=[args.clang,*opts,*includes,'-c',sf/'source'/name,'-o',obj]
        commands.append([str(x) for x in cmd]); run(cmd,work/f'sf_{i}.log',env)
        objects.append(obj)
    harness=work/'harness.obj'
    nativeopts=['-O2','-mavx2','-mfma','-ffp-contract=off','-fno-fast-math']
    cmd=[args.clang,*nativeopts,*includes,'-c',ROOT/'native/acceptance.c','-o',harness]
    commands.append([str(x) for x in cmd]); run(cmd,work/'harness.log',env)
    # Keep the frozen header include tree identical for each mutant.
    sutdir=work/'sut'; (sutdir/'native').mkdir(parents=True)
    shutil.copytree(ROOT/'vendor',sutdir/'vendor')
    original=(ROOT/'native/div3_tight.h').read_text()
    wrapper=(ROOT/'native/acceptance_sut.c').read_text()
    results=[]; assembly_checks={}
    for name in ['actual','no_guard','wrong_high_coefficient','only_lane_zero','unfused','overstore']:
        header=original if name in ['actual','overstore'] else mutant_header(original,name)
        if name not in ['actual','overstore'] and header==original:
            raise RuntimeError(f'Mutation did not apply: {name}')
        (sutdir/'native/div3_tight.h').write_text(header,encoding='utf-8')
        text=wrapper if name!='overstore' else wrapper.replace('div3_tight_array(d, s, n);',
                                                               'div3_tight_array(d, s, n); if(n) d[n]=0;')
        (sutdir/'native/acceptance_sut.c').write_text(text,encoding='utf-8')
        obj=work/(name+'.obj'); exe=work/(name+('.exe' if os.name=='nt' else ''))
        cmd=[args.clang,*nativeopts,'-c',sutdir/'native/acceptance_sut.c','-o',obj]
        commands.append([str(x) for x in cmd]); run(cmd,work/(name+'_compile.log'),env)
        cmd=[args.clang,*nativeopts,obj,harness,*objects,'-o',exe]
        if os.name!='nt': cmd+=['-lm']
        commands.append([str(x) for x in cmd]); run(cmd,work/(name+'_link.log'),env)
        if name=='actual':
            dis=run([args.objdump,'-d',obj],work/'actual_assembly.txt',env)
            chunks=re.split(r'(?m)^[0-9a-f]+ <([^>]+)>:\s*$',dis)
            functions={chunks[i]:chunks[i+1] for i in range(1,len(chunks)-1,2)}
            sut=functions.get('acceptance_sut',functions.get('_acceptance_sut',''))
            hardware=functions.get('acceptance_hardware',functions.get('_acceptance_hardware',''))
            assembly_checks={'sut_vector_fma':bool(re.search(r'vfmadd\w*ps',sut)),
                             'sut_vector_multiply':'vmulps' in sut,
                             'sut_vector_divide':'vdivps' in sut,
                             'hardware_vector_divide':'vdivps' in hardware}
            if not all(assembly_checks.values()):
                raise RuntimeError('Expected instructions absent; inspect actual_assembly.txt')
            sfdis=run([args.objdump,'-d',objects[0]],work/'oracle_assembly.txt',env)
            if re.search(r'\b(v?div[ps][sd]|v?rcp\w*|v?mul[ps][sd]|vfmadd\w*)\b',sfdis):
                raise RuntimeError('Unexpected floating-point arithmetic in f32_div oracle')
        mode='exhaustive' if name=='actual' and args.exhaustive else 'quick'
        start=time.monotonic()
        with (work/(name+'.jsonl')).open('w') as out,(work/(name+'.stderr')).open('w') as err:
            p=subprocess.run([str(exe),mode],stdout=out,stderr=err,env=env)
        row={'variant':name,'exit_code':p.returncode,'seconds':time.monotonic()-start,
             'binary_sha256':sha(exe),'object_sha256':sha(obj),
             'header_sha256':hashlib.sha256(header.encode()).hexdigest()}
        if name=='actual':
            if p.returncode: raise RuntimeError('Actual implementation failed independent reference')
            records=[json.loads(s) for s in (work/(name+'.jsonl')).read_text().splitlines()]
            row['records']=records
            summary=next(r for r in records if r['type']=='result')
            if summary['sweep_inputs'] != (2**32 if args.exhaustive else 2**20):
                raise RuntimeError('Incomplete sweep')
        else:
            failure=(work/(name+'.stderr')).read_text()
            # A compile failure, crash, or arbitrary error is NOT a successful negative control.
            if p.returncode!=2 or not failure.startswith('FAIL'):
                raise RuntimeError(f'Negative control not caught by comparator: {name}')
            row['witness']=failure.strip()
        results.append(row)
        print(name, 'passed' if name=='actual' else 'rejected', flush=True)
    report={'source_revision_assessed':'2aa0bbd8941405369495f24bad913ca6037ed09c',
            'softfloat_url':SF_URL,'softfloat_archive_sha256':SF_SHA,
            'compiler':subprocess.check_output([args.clang,'--version'],text=True).splitlines()[0],
            'source_sha256':{str(p.relative_to(ROOT)).replace('\\','/'):sha(p)
                for p in [ROOT/'acceptance.py',ROOT/'native/acceptance.c',ROOT/'native/acceptance_sut.c',ROOT/'native/div3_tight.h']},
            'assembly_checks':assembly_checks,'results':results}
    (work/'commands.json').write_text(json.dumps(commands,indent=2))
    (work/'summary.json').write_text(json.dumps(report,indent=2))
    # Public summary contains relative sources, hashes and counters; local commands stay in work.
    (ROOT/'results/acceptance.json').write_text(json.dumps(report,indent=2)+'\n')
    print('Evidence:',work,flush=True)

if __name__=='__main__': main()
