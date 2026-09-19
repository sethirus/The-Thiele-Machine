"""Check C3 provenance/replay evidence, without claiming compiler correctness."""
from pathlib import Path
import hashlib,json,subprocess,time
ROOT=Path(__file__).resolve().parents[3]
HERE=Path(__file__).resolve().parent
report={'status':'running','checks':[],'classification_scope':'current pinned hardware artifacts; no synthesis or physical performance claim'}
def write(): (HERE/'validation.json').write_text(json.dumps(report,indent=2)+'\n')
commands=[('pipeline',['python3','scripts/generate_rtl_pipeline_manifest.py','--check']),
          ('transforms',['python3','scripts/audit_rtl_text_transforms.py','--check']),
          ('tests',['python3','-m','pytest','-q','tests/test_rtl_pipeline_manifest.py','tests/test_rtl_text_transform_audit.py','tests/test_canonical_source_pipeline.py'])]
for name,cmd in commands:
    start=time.monotonic()
    with (HERE/(name+'.log')).open('w') as log:
        result=subprocess.run(cmd,cwd=ROOT,stdout=log,stderr=subprocess.STDOUT)
    report['checks'].append({'name':name,'command':cmd,'cwd':str(ROOT),'exit_code':result.returncode,'seconds':time.monotonic()-start})
    if result.returncode: report['status']='failed'
    write();print(name,result.returncode,flush=True)
    if result.returncode: raise SystemExit(result.returncode)
manifest=json.loads((ROOT/'artifacts/rtl_pipeline_manifest.json').read_text())
report['artifacts']=manifest['files']
report['evidence_sha256']={p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in [
    'artifacts/rtl_pipeline_manifest.json','artifacts/rtl_text_transform_audit.json',
    'artifacts/review_revision/REALIZATION_ASSURANCE.md']}
report['status']='passed';write()
