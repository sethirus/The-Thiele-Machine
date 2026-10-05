import re
names="reg fact fact_eqb instr cost core upd write goto trap record_fact commit_to fact_cap claim check_ok commit_ok certify_ok cexec fires state exec run total_cost start_core start clean_start fetch next_instr halted step run_prog trace_of mentions plain untouched sound earned no_forgery chain".split()
alt='|'.join(sorted(names,key=len,reverse=True))
# EarnedMultiPriced itself: unqualified occurrences
p='EarnedMultiPriced.v'
s=open(p,encoding='utf-8').read()
s=re.sub(r"(?<![A-Za-z0-9_'.])("+alt+r")(?![A-Za-z0-9_'])", lambda m:'pu_'+m.group(1), s)
open(p,'w',encoding='utf-8',newline='\n').write(s)
# dependents: M.name
for p in ['UniversalPCodes.v','UniversalPBridge.v','UniversalPBlocks.v','UniversalPLayout.v',
          'UniversalPPhases.v','UniversalPSim.v','UniversalPRun.v','PresentedUniversal.v','PresentedDemo.v']:
    s=open(p,encoding='utf-8').read()
    s=re.sub(r"(?<![A-Za-z0-9_'.])M\.("+alt+r")(?![A-Za-z0-9_'])", lambda m:'M.pu_'+m.group(1), s)
    open(p,'w',encoding='utf-8',newline='\n').write(s)
