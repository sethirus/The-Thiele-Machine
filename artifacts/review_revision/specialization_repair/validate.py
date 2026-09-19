from pathlib import Path
import subprocess,json,hashlib,time
ROOT=Path(__file__).resolve().parents[3]
COQ=ROOT/'coq'
HERE=Path(__file__).resolve().parent
FLAGS=[]
for line in (COQ/'_CoqProject').read_text().splitlines():
    if line.startswith(('-R ','-Q ','-I ')): FLAGS.extend(line.split())
source=COQ/'kernel/foundation/VMUnboundedCM2Specialization.v'
report={'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'status':'running','checks':[]}
commands=[('build',['coqc',*FLAGS,'-time',str(source)]),
          ('integration',['make','kernel/foundation/VMUnboundedCM2Specialization.vo']),
          ('contracts',['coqc',*FLAGS,str(HERE/'Contracts.v')]),
          ('coqchk',['coqchk',*FLAGS,'-silent','-o','Kernel.VMUnboundedCM2Specialization'])]
for name,cmd in commands:
    start=time.monotonic()
    with (HERE/(name+'.log')).open('w') as log:
        p=subprocess.run(cmd,cwd=COQ,stdout=log,stderr=subprocess.STDOUT)
    report['checks'].append({'name':name,'command':cmd,'cwd':str(COQ),'exit_code':p.returncode,'seconds':time.monotonic()-start})
    if p.returncode: report['status']='failed'
    (HERE/'validation.json').write_text(json.dumps(report,indent=2)+'\n')
    print(name,p.returncode,flush=True)
    if p.returncode: raise SystemExit(p.returncode)
report['status']='passed'
(HERE/'validation.json').write_text(json.dumps(report,indent=2)+'\n')
