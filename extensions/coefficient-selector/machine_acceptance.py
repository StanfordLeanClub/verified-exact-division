"""Compile and check the fixed x86-64 image, then test the linked bytes.

The Lean byte certificate checks exact equality with the frozen image. The
SoftFloat/guard-page harness is additional empirical evidence, not a proof.
All compiler objects, executable files, and commands remain in machine_work/.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse, hashlib, json, os, re, subprocess, sys, time
from acceptance import extract_verified, SF_SOURCES, SF_SHA, SF_URL, run, sha
from tools.extract_machine import emit

ROOT=Path(__file__).resolve().parent
FLAGS=['-O2','-mavx2','-mfma','-ffp-contract=off','-fno-fast-math',
       '-fno-vectorize','-fno-slp-vectorize','-fno-unroll-loops']

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--lean',default='lean')
    ap.add_argument('--lean-path-file',type=Path)
    ap.add_argument('--softfloat-archive',type=Path,required=True)
    ap.add_argument('--exhaustive',action='store_true')
    ap.add_argument('--clang',default='clang')
    args=ap.parse_args()
    stamp=datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S')
    work=ROOT/'machine_work'/stamp;work.mkdir(parents=True)
    env=os.environ.copy();env['TMP']=env['TEMP']=str(work)
    commands=[]
    def cmd(xs,name):
        commands.append([str(x) for x in xs]);return run(xs,work/(name+'.log'),env)
    obj=work/'compiled.obj'
    cmd([args.clang,*FLAGS,'-c',ROOT/'native/certified_div3.c','-o',obj],'compile')
    emit(obj,work/'image')
    image=(work/'image/image.bin').read_bytes()
    if args.lean_path_file:
        env['LEAN_PATH']=args.lean_path_file.read_text().strip()
    certificate=work/'ObservedImage.lean'
    observed='['+','.join(str(b) for b in image)+']'
    certificate.write_text('import Div3Machine.Main\nnamespace Div3Machine\n'
        'set_option maxRecDepth 6000\nset_option maxHeartbeats 2000000\n'
        'def observedImage : List Nat := '+observed+'\n'
        'theorem observed_image : observedImage = imageBytes := by decide +kernel\n'
        '#print axioms observed_image\n#print axioms machine_correct\n'
        '#print axioms memory_permissions\nend Div3Machine\n',encoding='utf-8')
    proof=cmd([args.lean,certificate],'byte_certificate')
    from proof_policy import audit_output
    audit_output(proof,['Div3Machine.observed_image','Div3Machine.machine_correct','Div3Machine.memory_permissions'])
    # Each byte mutation must fail during Lean checking, not in compilation/linking.
    rejected=[]
    for name,offset in [('opcode',0),('branch_target',7),('load_opcode',82),('store_opcode',226),('constant',528)]:
        mutant=bytearray(image);mutant[offset]^=1
        p=work/('Negative_'+name+'.lean')
        p.write_text(certificate.read_text().replace(observed,'['+','.join(map(str,mutant))+']'))
        r=subprocess.run([args.lean,str(p)],env=env,capture_output=True,text=True)
        (work/(name+'_negative.log')).write_text(r.stdout+r.stderr,encoding='utf-8')
        if r.returncode==0 or 'Tactic `decide` proved that the proposition' not in r.stdout+r.stderr:
            raise RuntimeError('Byte negative control did not fail for unequal image: '+name)
        rejected.append(name)
    checked=work/'checked.obj'
    cmd([args.clang,'-c',work/'image/image.S','-o',checked],'assemble')
    sf=extract_verified(args.softfloat_archive,work/'reference')
    includes=['-I'+str(sf/'build/Linux-x86_64-GCC'),'-I'+str(sf/'source/8086-SSE'),'-I'+str(sf/'source/include')]
    opts=['-O2','-std=c11','-DSOFTFLOAT_FAST_INT64','-DSOFTFLOAT_FAST_DIV64TO32','-DINLINE_LEVEL=5','-DSOFTFLOAT_ROUND_ODD']
    objects=[]
    for i,name in enumerate(SF_SOURCES):
        o=work/f'sf_{i}.obj';cmd([args.clang,*opts,*includes,'-c',sf/'source'/name,'-o',o],f'sf_{i}');objects.append(o)
    harness=work/'harness.obj'
    cmd([args.clang,*FLAGS,*includes,'-c',ROOT/'native/acceptance.c','-o',harness],'harness')
    wrapper=work/'wrapper.c'
    wrapper.write_text('#include <immintrin.h>\n#include <stddef.h>\n#include <stdint.h>\n#include <stdio.h>\n#include <stdlib.h>\n#include <string.h>\n'
        '__attribute__((sysv_abi)) void certified_div3(float*,const float*,size_t);\n'
        'extern unsigned char certified_div3_image_end[];\n'
        'static const unsigned char expected[] = {'+','.join(map(str,image))+'};\n'
        'void acceptance_sut(float*d,const float*s,size_t n){\n'
        ' static int checked; if(!checked){\n'
        ' const unsigned char *p=(const unsigned char*)(uintptr_t)&certified_div3;\n'
        ' if((uintptr_t)certified_div3_image_end-(uintptr_t)p!=sizeof expected || memcmp(p,expected,sizeof expected)){\n'
        ' fprintf(stderr,"Loaded image differs from Lean-checked bytes\\n");abort();} checked=1;}\n'
        ' certified_div3(d,s,n);}\n'
        'void acceptance_hardware(float*d,const float*s,size_t n){size_t i=0;\n'
        'for(;n-i>=8;i+=8)_mm256_storeu_ps(d+i,_mm256_div_ps(_mm256_loadu_ps(s+i),_mm256_set1_ps(3.0f)));\n'
        'for(;i<n;++i)d[i]=s[i]/3.0f;}\n')
    wrapper_obj=work/'wrapper.obj'
    cmd([args.clang,*FLAGS,'-c',wrapper,'-o',wrapper_obj],'wrapper')
    exe=work/'machine.exe'
    cmd([args.clang,*FLAGS,checked,wrapper_obj,harness,*objects,'-o',exe],'link')
    start=time.monotonic()
    output=cmd([exe,'exhaustive' if args.exhaustive else 'quick'],'run')
    records=[json.loads(s) for s in output.splitlines()]
    summary=next(r for r in records if r['type']=='result')
    if summary['sweep_inputs']!=(2**32 if args.exhaustive else 2**20):raise RuntimeError('Incomplete input sweep')
    report={'accepted':True,'compiler':subprocess.check_output([args.clang,'--version'],text=True).splitlines()[0],
        'image_sha256':hashlib.sha256(image).hexdigest(),'image_bytes':len(image),'loaded_image_checked':True,
        'byte_negative_controls':rejected,'softfloat_archive_sha256':SF_SHA,'softfloat_url':SF_URL,
        'records':records,'test_seconds':time.monotonic()-start,'binary_sha256':sha(exe),
        'source_sha256':{p.relative_to(ROOT).as_posix():sha(p) for p in [ROOT/'machine_acceptance.py',ROOT/'native/certified_div3.c',ROOT/'native/div3_tight.h',ROOT/'tools/extract_machine.py',ROOT/'lean/Div3Machine/Main.lean',ROOT/'lean/Div3Machine/Operations.lean',ROOT/'lean/Div3Machine/ISA.lean',ROOT/'lean/Div3Machine/Decoder.lean',ROOT/'lean/Div3Machine/Program.lean']}}
    (work/'commands.json').write_text(json.dumps(commands,indent=2)+'\n')
    (work/'summary.json').write_text(json.dumps(report,indent=2)+'\n')
    (ROOT/'results/machine_acceptance.json').write_text(json.dumps(report,indent=2)+'\n')
    print('Accepted checked image, rejected byte mutations, passed linked-image comparisons:',work,flush=True)

if __name__=='__main__':main()
