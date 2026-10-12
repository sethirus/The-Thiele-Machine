from pathlib import Path
import json
R=Path(__file__).parent
repo=Path('/workspace/The-Thiele-Machine-book-design')
changes=json.loads((R/'document-edits.json').read_text())
def edit(file,old,new,reason):
    p=repo/file;s=p.read_text();assert s.count(old)==1,(file,old[:80],s.count(old))
    snap=R/'before'/file;snap.parent.mkdir(parents=True,exist_ok=True)
    if not snap.exists():snap.write_text(s)
    p.write_text(s.replace(old,new))
    changes.append(dict(file=file,before=old,after=new,reason=reason))
    (R/'document-edits.json').write_text(json.dumps(changes,indent=2)+'\n')
edit('README.md','bases with uniformly finite instruction branching, and bases whose moves ignore their state, fail the stated universal-base requirement','bases with only finitely many possible next states at each state, and bases whose moves ignore their state, fail the direct one-move universal-base requirement (a macro interface can group several base steps)', 'State the direct-interface restriction and the actual pointwise finite-branching hypothesis; this does not rule out ordinary finite instruction sets used through a macro interface.')
edit('monograph/thiele_machine_math_spec.tex',r'through the direct one-move interface. This does not exclude grouping several base steps into one macro move (\texttt{lift\_finite\_branching\_not\_complete}, \texttt{lift\_stateless\_not\_complete}).',r'through the direct one-move interface (\texttt{lift\_finite\_branching\_not\_complete}, \texttt{lift\_stateless\_not\_complete}). This does not exclude grouping several base steps into one macro move.', 'Keep theorem identifiers beside the statements they prove.')
links=[
('The passage on proof as an act is on p.~28.', 'https://archive-pml.github.io/martin-lof/pdfs/Meanings-of-the-Logical-Constants-1983.pdf', 'Lecture text'),
('p.~338 of the chapter as posted on his website.', 'https://www.tau.ac.il/~corry/publications/articles/pdf/bourbaki-structures.pdf', "Author's chapter"),
('Notices of the American Mathematical Society 55(11), pp. 1370--1379.', 'https://webhomes.maths.ed.ac.uk/~v1ranick/papers/hales2.pdf', 'Article text'),
('is Note~5 to 2.41, p.~30.', 'https://www.bipm.org/documents/20126/2071204/JCGM_200_2012.pdf', 'BIPM text'),
('Oxford: Clarendon Press, 1922, p.~11.', 'https://www.gutenberg.org/cache/epub/33663/pg33663-images.html', '1922 translation'),
('Proceedings of the 21st Annual Computer Security Applications Conference (ACSAC), Tucson, pp. 28--40.', 'https://dwheeler.com/trusting-trust/wheelerd-trust.pdf', "Author's paper"),
('all p.~183; ``no guarantee that this minimum is in fact achievable,\'\' p.~187.', 'https://fab.cba.mit.edu/classes/862.22/notes/computation/Landauer-1961.pdf', 'Paper scan'),
('half of English ``determined by the structure of the language,\'\' p.~399.', 'https://www.csd.uoc.gr/~hy590-38/shannon1948.pdf', 'Paper text'),
]
for anchor,url,label in links:
    edit('monograph/monograph.tex',anchor,anchor+' '+r'\href{'+url+'}{'+label+'}.', 'Add a checked, accessible primary-text link to the existing bibliography entry.')
print(len(changes),'document corrections')
