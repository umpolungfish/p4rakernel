#!/usr/bin/env python3
"""Build the complete native organism with its retained factor/product task."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

ROOT=Path(__file__).resolve().parents[1]
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--out',type=Path,required=True)
args=parser.parse_args()
out=args.out.resolve()
out.mkdir(parents=True,exist_ok=False)
steps=[]
def run(name,command,cwd=ROOT,env=None):
    started=time.monotonic()
    result=subprocess.run([str(x) for x in command],cwd=cwd,env=env,capture_output=True,timeout=600)
    (out/(name+'.stdout')).write_bytes(result.stdout)
    (out/(name+'.stderr')).write_bytes(result.stderr)
    steps.append(dict(name=name,command=[str(x) for x in command],exit_code=result.returncode,seconds=time.monotonic()-started))
    (out/'commands.json').write_text(json.dumps(steps,indent=2)+'\n')
    print(name,result.returncode,flush=True)
    if result.returncode:raise RuntimeError((result.stdout+result.stderr).decode(errors='replace')[-5000:])

run('organism_build',["python3",ROOT/'tests/kernel_features/verify_organism.py','--out',out/'organism'])
environment=os.environ.copy();environment['RUSTFLAGS']='-C target-feature=-crt-static'
run('factor_bridge_build',['cargo','build','--offline','--release','--target','x86_64-unknown-linux-gnu'],
    cwd=ROOT/'organism/factor_bridge',env=environment)
library=ROOT/'organism/factor_bridge/target/x86_64-unknown-linux-gnu/release/liborganism_factor_bridge.so'
import shutil
shutil.copy2(library,out/'factor_bridge.so')
shutil.copy2(out/'organism/vgi_organism.so',out/'vgi_organism.so')
environment=os.environ.copy();environment['LEAN_PATH']=str(out/'organism')
run('factor_entry_compile',[ROOT/'build/stage1/bin/lean','-c',out/'factor.c','RunOrganismFactor.lean'],
    cwd=ROOT/'p4ramill',env=environment)
run('factor_entry_link',[ROOT/'build/stage1/bin/leanc',out/'organism/NativeDialetheicOrganism.c',out/'factor.c',
    '-o',out/'organism-factor'])
files=[ROOT/p for p in ['src/kernel/sixteen3.h','src/kernel/inclosure.h','src/kernel/inclosure.cpp','src/kernel/organism_factor.h',
    'src/kernel/organism_vgi.h','p4ramill/RunOrganismFactor.lean','p4ramill/NativeDialetheicOrganism.lean',
    'organism/factor_bridge/src/lib.rs',
    'organism/factor_bridge/Cargo.toml','organism/factor_bridge/Cargo.lock']]
files += [ROOT.parent/'Vox/src/lib.rs',ROOT.parent/'Vox/src/glut_carrier.rs',ROOT.parent/'Vox/src/factor_synthesis.rs',
          ROOT.parent/'Vox/src/glut_fold.rs',ROOT.parent/'Vox/src/glut_square_phase.rs',
          ROOT.parent/'Vox/src/glut_correlation.rs',ROOT.parent/'Vox/src/glut_system.rs',
          ROOT.parent/'Vox/src/toroidal_division.rs',ROOT.parent/'Vox/src/stark_rotation.rs',ROOT.parent/'Vox/src/glut_root_reentry.rs',
          ROOT.parent/'Vox/src/belnap_word.rs',ROOT.parent/'Vox/src/morphism_factor.rs',
          ROOT.parent/'Vox/src/packed_belnap_word.rs']
files += [ROOT.parent/'Vox/src/carried_torus_frame.rs',ROOT.parent/'Vox/src/geometric_return.rs',ROOT/'organism/source_return_replay.py',ROOT/'organism/factor_bridge/src/sic_geometry.rs',ROOT/'organism/run_factor.py',
          ROOT/'organism/torus_frames_replay.py',ROOT/'organism/sic_geometry_replay.py',ROOT.parent/'G-mOMonadOS/Cargo.toml',
          ROOT.parent/'G-mOMonadOS/build.rs']
files += [ROOT/'organism/factor_bridge/src/source_metric.rs',ROOT/'organism/source_metric_replay.py']
files += sorted((ROOT.parent/'G-mOMonadOS/src').rglob('*.rs'))
images=[out/'organism-factor',out/'factor_bridge.so',out/'vgi_organism.so']
report={'status':'built','compilation_seconds':sum(x['seconds'] for x in steps),
        'sources':{str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in files},
        'images':{str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in images}}
(out/'build.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'status':'built','directory':str(out),'seconds':report['compilation_seconds']}),flush=True)
