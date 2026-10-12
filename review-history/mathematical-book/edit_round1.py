from pathlib import Path
import json,re
R=Path(__file__).parent
ps={x['id']:x['text'] for x in json.loads((R/'round1.json').read_text())}
changes={}
def edit(n,new): changes[n]=new
def sub(n,a,b):
 t=changes.get(n,ps[n]);assert a in t,(n,a);changes[n]=t.replace(a,b)
def regex(n,a,b):
 t=changes.get(n,ps[n]);new,k=re.subn(a,b,t,flags=re.S);assert k,(n,a);changes[n]=new
for n in [16,19,24,25,30,35,40,43,53,54,57,58]:edit(n,'')
sub(3,'checked by Coq','checked by a small proof-checking program')
sub(5,'proved them correct in\nCoq','proved them correct')
sub(6,"which no proof checker can check","which those mathematical results do not decide")
sub(7,'Coq-checked monitors','monitors')
sub(8,"A proof is the case this book is built on. A proof checked by a proof assistant is a check that could\nhave said no, and the checker vouches that the proof fits its statement; whether the statement says\nwhat you meant is still yours to read.","A proof is one example: checking its steps is a procedure that can reject them. Whether its statement\nsays what you meant is still yours to read.")
sub(9,'whole number, the universal programs that run on that host, and the Coq files that define all of\nit.','whole number, and the universal programs that run on that host.')
sub(10,'borrowed from the Coq undecidability library','due to Minsky, using the construction of Forster, Larchey-Wendling and coauthors')
sub(11,', checked in Coq &', ' &')
sub(11,'the Coq Library of Undecidability','Forster, Larchey-Wendling and coauthors')
sub(11,'L as a model of computation in Coq','L as a model of computation')
sub(11,'the list of what\'s trusted, in one place','the separation of mathematical guarantees from implementation tests')
sub(12,'proved in\nCoq.','proved correct.')
sub(13,'By the time the Coq proofs finally landed','By the time the arguments took shape')
sub(14,'I did not know what Coq was, ','')
regex(15,r'I used the checker to catch gaps.*?I had to refuse that too\.',"So I read every statement. A derivation can settle an empty question, and I had to refuse that too.")
edit(17,"The theorem is about every certification system, a system with the toll among its conditions,\nand about no system without it. One edge matters:\n"+ps[17].split('the theorem does not assume',1)[1].join(['the theorem does not assume','']) if False else "The theorem is about every certification system, a system with the toll among its conditions,\nand about no system without it. One edge matters: the theorem does not assume"+ps[17].split('the theorem does not assume',1)[1])
sub(17,'the checked statement','the statement')
sub(18,' All of these are in NecFFloor.v.','')
sub(20,' All four are in NecFMerge.v.','')
regex(21,r'The checked version is.*?state is a list of bits of any length,', 'Its state can be represented by a list of bits of any length,')
edit(22,"There are three separate claims here, and I need to keep them apart. The\nstrip machine is permanent and forgets nothing. It also has infinitely many states:\nno finite list holds every finite strip. Neither claim involves a cost. To certify for free,\ncount the strip's length as a whole number and let each move add one at cost zero.\nNothing merges, merge pricing holds, and the toll fails.")
regex(23,r'The file states.*?The thing that',"The move is injective and can switch the reading both on and off. Pricing the turn at zero\nmeets merge pricing, since no move merges, and fails the toll.\nThe thing that")
regex(26,r"That's \\code\{[^}]+\}, and what",'What')
regex(26,r'\(The\nsame file shows.*?door three is about\nwhether they must\.\)', '(A price of one on that move satisfies all three premises, so the premises can hold together;\ndoor three is about whether they must.)')
regex(27,r' \(both facts are checked\nfor these four sheets,.*?\)\.', '.')
sub(27,'next to it in the file sits a','there is also a')
edit(28,ps[28].split('Checked as')[0].rstrip()+" The counting argument also shows that at least $k$ states collapse,\nwithout any price premise.")
regex(29,r'\(\\code\{[^}]+\}; the pair is in\n', '(the pair is in\n')
regex(31,r'\n\(Checked name:.*?\)\n','\n')
# Keep the counterexample constructive on the page, rather than replacing a source locator with an unsupported assurance.
regex(32,r'\(a four-state machine.*?NecFMerge.v\)',r"(take four states $s,a,b,c$, with only $s$ reading no, and a move\n$s\\mapsto a$, $a\\mapsto b$, $b\\mapsto b$, $c\\mapsto c$)")
regex(33,r'Checked as.*?, for any map', 'The argument holds for any map')
regex(34,r'\n\(\\code\{nec.*?\)\.$','.')
regex(36,r'Their formal counterparts.*?\. The machine', 'The machine')
sub(36,'the run form is a checked theorem','the run form is a theorem')
sub(37,'checked over any machine','proved over any machine')
sub(37,'factors through gives descent, all in NecFCounter.v; the','factors through gives descent; the')
sub(38,"instance (the checked record carries the toll as a field, so that's every certification\nsystem)","instance, which is exactly what a certification system is")
sub(38,"embeds those frameworks' full type systems, and the files say so.","embeds those frameworks' full type systems.")
regex(39,r' Checked as.*?\. What has no counterpart',' What has no counterpart')
edit(41,'The result holds for arbitrary sets of states and observations.')
sub(42,'what ShadowPricing.v proves the other way is','what the argument proves in the other direction is')
edit(44,r'''The argument holds for any pair like $A$ and $B$, over arbitrary sets of states, claims,
transcripts and explanation relations; it uses only their claim values and their shared
transcript. A verifier sound and complete for the claim under an explanation relation cannot
look only at the bare part once two transcripts with that same bare part are explained, one by
a state with the claim and one by a state without it. The three escapes use full states,
a commitment satisfying the contract, or truthful responses. The cost $1$ in the definition
above is not used in any of these arguments; it is a chosen price.''')
regex(45,r"\(that theorem's proof builds it;.*?\)","(that theorem's proof builds it)")
edit(46,"Put with the three escapes, the whole picture holds for every Thiele-complete machine\nand for the small machine: "+ps[46].split("the bare-transcript\nverifier",1)[1].join(["the bare-transcript\nverifier",""]) if False else "Put with the three escapes, the whole picture holds for every Thiele-complete machine\nand for the small machine: the bare-transcript\nverifier"+ps[46].split("the bare-transcript\nverifier",1)[1])
sub(48,"This is the book's word; there's no Coq definition of it.","This is the book's word.")
edit(49,r'''For any system with a counter that obeys conservation, put the two arguments together.
The tree bound applies to the sum of the charges of a run, without needing $|\Omega'| > 0$;
conservation identifies that sum with the counter's rise. A system satisfying both gets
the theorem. The bill form is also part of Theorem~\ref{thm:ent-cs} below. The tree half is
the lemma above; the rest is arithmetic on the two lengths, the leaf count and the counter.
Notice what's missing from the hypotheses: anything tying the lists to the run. That's the
shape of the bound.''')
edit(50,ps[50][ps[50].index('Theorem~'):])
edit(51,ps[51][ps[51].index('Part (3)'):])
regex(52,r'Read off Definition.*?The toll constrains',r'Read off Definition~\\ref{def:certsys}. The toll constrains')
sub(55,'StructuralRecordAxis.v proves exactly the facts I named for each:','The examples establish exactly the facts I named for each:')
sub(55,"true by\ninspection, and isn't a separate theorem.",'true by\ninspection.')
sub(56,"it's\nchecked over an arbitrary base", "it works\nover an arbitrary base")
sub(56,', all in NecWArgued.v.','.')
edit(59,ps[59][ps[59].index('When the cups'):])
# Supplementary batches append to this dictionary before export.
if (R/'extra_round1.py').exists():exec((R/'extra_round1.py').read_text())
out=[dict(before=ps[n],after=t,reason=f'Mathematical presentation, passage R{n}') for n,t in sorted(changes.items()) if t!=ps[n]]
(R/'clean-edits.json').write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n')
print('Manual edits',len(out))
