import sys
p=sys.argv[1]
s=open(p,encoding='utf-8').read()
s=s.replace(r"q) /\n     (forall", "q) /"+chr(92)+"\n     (forall")
s=s.replace(r"q) /\n  (forall", "q) /"+chr(92)+"\n  (forall")
open(p,'w',encoding='utf-8',newline='\n').write(s)
