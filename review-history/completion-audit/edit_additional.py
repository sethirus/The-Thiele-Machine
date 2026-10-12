from pathlib import Path
import json
R=Path(__file__).parent;repo=Path('/workspace/The-Thiele-Machine-book-design');changes=json.loads((R/'document-edits.json').read_text())
def edit(file,old,new,reason):
 p=repo/file;s=p.read_text();assert s.count(old)==1,(file,old[:75],s.count(old));snap=R/'before'/file;snap.parent.mkdir(parents=True,exist_ok=True)
 if not snap.exists():snap.write_text(s)
 p.write_text(s.replace(old,new));changes.append(dict(file=file,before=old,after=new,reason=reason));(R/'document-edits.json').write_text(json.dumps(changes,indent=2)+'\n')
f='monograph/monograph.tex'
edit(f,'Press release, 31 October 2002, on the indictment of Andrew Fastow;','Press release, 2 October 2002, on the criminal complaint against Andrew Fastow;','The cited Justice Department primary document is dated October 2 and describes a complaint, not the later indictment.')
edit(f,'Kent Weare (2016). Ethereum DOS Attack. InfoQ, 19 September 2016.','Kent Weare (2016). Ethereum Security Alert Issued, Ethereum Foundation Responds with ``From Shanghai, With Love''. InfoQ, 19 September 2016.','Use the actual article title displayed by the cited publisher.')
edit(f,r'''\href{https://faculty.lynchburg.edu/~nicely/twins/twins.html}{Author's page}. ''','',"Remove a confirmed dead author-page link; retain the journal citation and attribution.")
f='monograph/thiele_machine_math_spec.tex'
edit(f,'and a halting-preserving translation of two-counter instances into one-counter instances would make it decidable','and a computable halting-preserving translation of two-counter instances into one-counter instances would make it decidable','The obstruction excludes effective translations, not arbitrary set-theoretic functions.')
old='A base whose moves have only finitely many different effects at each state (one with finitely many moves, for instance), or one whose step ignores the current state, lifts to no Thiele-complete machine under any claim language and capacity'
new=old+' through the direct one-move interface. This does not exclude grouping several base steps into one macro move'
edit(f,old,new,'State the direct-interface restriction; the macro lift permits ordinary finite instruction sets.')
f='TECHNICAL_DISCLOSURE.md'
edit(f,'it runs every program of the small machine from every start (`U_simulation`)','it runs every program of the small machine from every clean start start(x, y), through the prescribed host loading (`U_simulation`)','Keep the universal-program claim within the loading and clean-start theorem.')
edit(f,'with finite memory, a step that writes a permanent record is not injective','when the whole extended state space is finite, an instruction that raises a permanent record is not injective','A finite base alone does not exclude unbounded hidden history.')
f='docs/THEOREM_MEANINGS.md'
edit(f,'a flip of k > 0 states beside m certified ones, from the uniform distribution on those m + k states, dissipates at least','an instruction flipping k > 0 states beside m certified ones, on the uniform input distribution over those m + k states, has mean heat at least','Make ensemble mean explicit in the theorem guide.')
print(len(changes),'total companion and source corrections')
