import re,sys,json
files=['UniversalCodes','UniversalBridge','UniversalBlocks','UniversalLayout','UniversalPhases','UniversalSim','UniversalRun']
deps={'UniversalCodes':[], 'UniversalBridge':[], 'UniversalBlocks':['UniversalCodes','UniversalBridge'],
 'UniversalLayout':['UniversalCodes','UniversalBridge','UniversalBlocks'],
 'UniversalPhases':['UniversalCodes','UniversalBridge','UniversalBlocks','UniversalLayout'],
 'UniversalSim':['UniversalCodes','UniversalBridge','UniversalBlocks','UniversalLayout','UniversalPhases'],
 'UniversalRun':['UniversalCodes','UniversalBridge','UniversalBlocks','UniversalLayout','UniversalPhases','UniversalSim']}
decl=re.compile(r"^\s*(?:Local\s+)?(Definition|Fixpoint|Inductive|Record|Lemma|Theorem|Corollary|Fact|Ltac|Remark|Example)\s+([A-Za-z_][A-Za-z0-9_']*)",re.M)
names={}
for f in files:
    s=open('orig/%s.v'%f,encoding='utf-8').read()
    ns=[m.group(2) for m in decl.finditer(s)]
    # record fields
    for m in re.finditer(r"Record\s+\w+[^{]*?:=\s*(\w*)\s*\{(.*?)\}\s*\.",s,re.S):
        body=m.group(2)
        for fm in re.finditer(r"(?:^|;)\s*(\w+)\s*:",body):
            ns.append(fm.group(1))
    names[f]=ns
if sys.argv[1]=='list':
    for f in files: print(f,len(names[f]),' '.join(names[f]))
    sys.exit()
def newname(n):
    if n=='U': return 'U_P'
    return 'pu_'+n
for f in files:
    s=open('orig/%s.v'%f,encoding='utf-8').read()
    vis=set(names[f])
    for d in deps[f]: vis|=set(names[d])
    # rename unqualified occurrences
    pat=re.compile(r"(?<![A-Za-z0-9_'.])("+'|'.join(sorted(vis,key=len,reverse=True))+r")(?![A-Za-z0-9_'])")
    s=pat.sub(lambda m:newname(m.group(1)),s)
    s=s.replace('M.multi_','M.pu_multi_')
    s=s.replace('Require Minimal.EarnedMulti.','Require Minimal.EarnedMultiPriced.')
    s=s.replace('Module M := Minimal.EarnedMulti.','Module M := Minimal.EarnedMultiPriced.')
    s=s.replace('Minimal.UniversalCodes','Minimal.UniversalPCodes')
    for g in ['Bridge','Blocks','Layout','Phases','Sim']:
        s=s.replace('Kernel.Universal'+g,'Minimal.UniversalP'+g)
    out=f.replace('Universal','UniversalP')+'.v'
    open(out,'w',encoding='utf-8',newline='\n').write(s)
    print('wrote',out)
