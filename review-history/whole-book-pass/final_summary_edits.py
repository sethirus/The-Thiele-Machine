from audit import edit,R
from pathlib import Path
import json,difflib
pairs=[
('contribution_merge', 'for a permanent flip, and a built counterexample for each premise; and the mechanization of all\nof it (Section~\\ref{sec:a2-not-arbitrary}).', 'for a permanent flip, and a built counterexample for each premise\n(Section~\\ref{sec:a2-not-arbitrary}).'),
('contribution_proofs', 'ledger, the toll derived from it, its single-move and counted forms, the counterexamples, and\nthe mechanized proofs, and the physics is a named premise and is Landauer\'s.', 'ledger, the toll derived from it, its single-move and counted forms, and the counterexamples.\nThe physics is a named premise and is Landauer\'s.'),
('contribution_demon', 'measuring and erasing in more than one way is Fahn\'s (1996). Mine: the four-state demon and the three-state ring as checked\nmodels, and the two-state impossibility (Section~\\ref{sec:narrowing}). Kind: mechanization\nand illustration of a known physical point inside my ledger.', 'measuring and erasing in more than one way is Fahn\'s (1996). Mine: the four-state demon, the three-state ring\nand the two-state impossibility (Section~\\ref{sec:narrowing}). Kind: finite models\nillustrating a known physical point inside my ledger.'),
('contribution_windows', 'mechanization of an elementary lemma, plus specific facts about the machine and the definition.', 'an elementary observation about what a window hides, plus specific facts about the machine and the definition.'),
('contribution_entitlement', 'count is mechanized: in its bill form over any certification system, and for the record moves of', 'count is proved in its bill form over any certification system, and for the record moves of'),
('contribution_latch', 'form (I found no prior statement in the searches I ran), built from old notions; the latch form\nis mechanized, and so is the agreement up to the price list.', 'form (I found no prior statement in the searches I ran), built from old notions. The proofs\nshow why the record must latch and why its price list remains a separate choice.'),
('contribution_quantum_proofs', 'chain from ``the counts pass\'\' to ``the pinned level-one matrix is positive semidefinite\'\' to\n``$S^2 \\le 8$\'\'; checked proofs of the representation in finite dimension, real or complex, on two eight-level systems, and of the arcsine characterization;', 'chain from ``the counts pass\'\' to ``the pinned level-one matrix is positive semidefinite\'\' to\n``$S^2 \\le 8$\'\'; explicit constructions of the representation in finite dimension, real or complex, on two eight-level systems, and a proof of the arcsine characterization;'),
('contribution_quantum_kind', '(Section~\\ref{sec:chsh} and its derivation appendix). Kind: mechanization, with a new proof of a\nknown equivalence in one slice.', '(Section~\\ref{sec:chsh} and its derivation appendix). Kind: an integer procedure connecting\ncounts to these known bounds, with a new proof of a known equivalence in one slice.'),
('contribution_monitor', 'Kind: an instance of monitor enforcement, implemented and mechanized, with two things on top', 'Kind: an instance of monitor enforcement with two things on top'),
('derivation_quantum_chain', 'certificate computed from outcome counts, and a mechanized chain from ``the counts pass\'\' to PSD', 'certificate computed from outcome counts, and the argument from ``the counts pass\'\' to PSD')]
for tag,a,b in pairs:edit(tag,a,b,'Describe the contribution through its construction and argument rather than its proof-assistant treatment; retain prior-work credit.')
p=Path('/workspace/The-Thiele-Machine-book-design/monograph/monograph.tex');old=(R/'before.tex').read_text();es=json.loads((R/'edits.json').read_text());es.sort(key=lambda x:old.index(x['before']));spans=[(old.index(e['before']),old.index(e['before'])+len(e['before']),e) for e in es]
for a,b in zip(spans,spans[1:]):assert a[1]<=b[0],(a[2]['tag'],b[2]['tag'])
s=old
for a,b,e in reversed(spans):s=s[:a]+e['after']+s[b:]
p.write_text(s);(R/'working.tex').write_text(s)
(R/'changes.patch').write_text(''.join(difflib.unified_diff(old.splitlines(True),s.splitlines(True),fromfile='before.tex',tofile='working.tex')))
(R/'Changed-passages.txt').write_text('\n\n'.join(f"{i}. {e['tag']}\nReason: {e['reason']}\n\nBEFORE\n{e['before']}\n\nAFTER\n{e['after']}" for i,e in enumerate(es,1)))
print(len(es),'total edits')
