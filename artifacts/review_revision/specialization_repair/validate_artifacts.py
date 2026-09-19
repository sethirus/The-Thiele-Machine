"""Validate regenerated artifact identities and RTL regressions; no timing claim."""
from pathlib import Path
import subprocess,json,hashlib,time
ROOT=Path(__file__).resolve().parents[3]
HERE=Path(__file__).resolve().parent
report={'status':'running','checks':[]}
commands=[('pipeline-after-rebuild',['python3','scripts/generate_rtl_pipeline_manifest.py','--check']),
          ('transforms-after-rebuild',['python3','scripts/audit_rtl_text_transforms.py','--check']),
          ('rtl-regressions',['python3','-m','pytest','-q',
            'tests/test_rtl_assert_dispatch_faults.py','tests/test_rtl_morph_dispatch_faults.py',
            'tests/test_rtl_morph_opcodes.py','tests/test_rtl_mu_charging.py',
            'tests/test_rtl_structural_coverage.py','tests/test_isa_v2_migration_gate.py',
            'tests/test_rtl_pipeline_manifest.py','tests/test_rtl_text_transform_audit.py',
            'tests/test_canonical_source_pipeline.py'])]
for name,cmd in commands:
    start=time.monotonic()
    with (HERE/(name+'.log')).open('w') as log:
        result=subprocess.run(cmd,cwd=ROOT,stdout=log,stderr=subprocess.STDOUT)
    report['checks'].append({'name':name,'command':cmd,'cwd':str(ROOT),'exit_code':result.returncode,'seconds':time.monotonic()-start})
    if result.returncode: report['status']='failed'
    (HERE/'artifact-validation.json').write_text(json.dumps(report,indent=2)+'\n')
    print(name,result.returncode,flush=True)
    if result.returncode: raise SystemExit(result.returncode)
report['artifacts']=json.loads((ROOT/'artifacts/rtl_pipeline_manifest.json').read_text())['files']
report['status']='passed'
(HERE/'artifact-validation.json').write_text(json.dumps(report,indent=2)+'\n')
