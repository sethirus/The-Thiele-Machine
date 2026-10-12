from pathlib import Path
import difflib
import hashlib
import html
import json
import re

from reportlab.lib import colors
from reportlab.lib.styles import ParagraphStyle, getSampleStyleSheet
from reportlab.lib.units import mm
from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer, KeepTogether

ROOT = Path(__file__).parent
SOURCE = Path('/workspace/The-Thiele-Machine-book-design/monograph/monograph.tex')
original = SOURCE.read_text()
edits = []

def add(title, reason, old, new):
    assert original.count(old) == 1, (title, original.count(old))
    edits.append(dict(number=len(edits)+1, title=title, reason=reason,
                      source_line=original[:original.index(old)].count('\n')+1,
                      before=old, after=new))

add('The opening result',
    'Let the opening land on what the machine does. The theorem references immediately before this sentence already identify the supporting results.',
    '''So the guarantee holds for every
program, carried through one interpreter, with the cost counted exactly, and all of it is checked
in Coq.''',
    '''So the guarantee holds for every
program, carried through one interpreter, with the cost counted exactly.''')

add('The list of proved claims',
    'Name the status as proved and retain the explicit assumptions. The method used to check the derivation need not lead the list.',
    '''Checked by a proof assistant, with every assumption printed, for any system with the named parts:''',
    '''Proved, with every assumption printed, for any system with the named parts:''')

add('The short version',
    'Keep the summary about the result and its premises. Part V already explains the checking procedure.',
    '''The headline result is proved in Coq (a proof assistant: software
that checks every step of a proof), with every premise printed.''',
    '''The headline result is proved with every premise printed.''')

add('The front-matter account of the tools',
    'Preserve the account of how the work was produced. Replace the appeal to acceptance by Coq with a direct statement of the limited job given to the checker and auditor.',
    '''I used language models to
write the code and the proofs in this project, and I trust language models about as far as
I can throw them, which is exactly why every formal declaration is checked by a proof
assistant that doesn't care who or what wrote it. Coq rejects a wrong proof the same whether
a tenured professor or a model hands it over, and it accepted these, with none of my own
axioms anywhere in them, re-checkable by the procedure in Part V. Being self-taught and
using modern tools didn't make this looser. It's the reason I made a machine check the
formal corpus, and then built an auditor to read over the checker's shoulder for every way I
might have cheated, on purpose or by accident (Part V says what it looks for). It doesn't
trust me either. Good.''',
    '''I used language models to
write the code and the proofs in this project, and I trust language models about as far as
I can throw them. Every argument still has to hold up when you read it. I used a proof
checker to look for gaps in the formal derivations, and built an auditor to look for the
ways I'd let an assumption do the work. Neither can tell me that I've asked the right
question or that a definition means what I say it means. Part V gives the procedure and
its limits. The work stands or falls on the arguments.''')

add('The small-machine chapter’s summary',
    'Keep the assumption status and the exact source files, while removing the repeated account of compilation and printouts from the chapter’s conclusion.',
    r'''Every result above is closed: Coq reports no assumptions for any of them. That isn't
my say-so. EarnedCore.v and its link file, EarnedCoreLinks.v, each end by asking Coq to print the assumptions of each headline
theorem, and the build of Section~\ref{sec:coq} compiles them and fails unless every one comes
back closed. The
project-wide audit of Section~\ref{sec:coq} lists these files too, and every theorem in them comes
back closed there as well. The base
file uses nothing but Coq's standard library, so you can check it with nothing else
installed; the link file adds only the book's own abstract records and the library of
undecidability proofs.''',
    r'''The formal derivations of these results use no added axioms; each theorem still has
the hypotheses printed in its statement. The sources are EarnedCore.v and EarnedCoreLinks.v,
and Section~\ref{sec:coq} gives the assumption audit and the procedure for repeating it.
The base file uses only Coq's standard library; the link file adds the book's abstract
records and the library of undecidability proofs.''')

add('The precedents in “Why I used it”',
    'Introduce the examples by the checking practice they illustrate. The existing paragraph explaining why you used the tool stays exactly as written.',
    '''Two precedents show that a proof assistant is a serious tool. Neither of them is a
toy.''',
    '''Two precedents show how a large proof can be checked by a small program.''')

add('The shared foundation',
    'Sharing a foundation is a shared dependency, not an independent confirmation. Also qualify the incompleteness claim rather than treating it as an unconditional slogan.',
    r'''It doesn't mean Coq's own foundation is proved
consistent; it's believed consistent, and that can't be proved from inside, by Gödel (Section~\ref{sec:diagonal}),
so the foundation is trusted, and ``trusted'' has substance: it's the same kernel CompCert and
the four-colour proof stand on, and a bug in it would take all of them down together, which
is a kind of safety in numbers.''',
    r'''It doesn't mean Coq's own foundation is proved
consistent. Gödel's second incompleteness theorem limits what a sufficiently strong,
effectively axiomatized theory can establish about its own consistency, if it is consistent
(Section~\ref{sec:diagonal}). The foundation and the implementation of the checker remain
dependencies. CompCert and the four-colour formalization share them; that does not make
them independent checks of those dependencies.''')

add('The invitation to challenge the work',
    'Remove the suggestion that readers need a kernel exploit to challenge the book. Retain all three concrete targets and the example that distinguishes certification from learning.',
    r'''Before the list, the honest part about it. Most targets below are theorems Coq has checked,
and knocking one of those over head-on would take a bug in Coq's kernel. That can happen, but
it isn't where I'd put my money. The places a reader can actually win are aimed at me,
and there are three. None of them goes through Coq. A sentence of mine that says more than the Coq statement it cites
(Appendix~\ref{sec:coq-statements} puts the load-bearing ones side by side to make that easy). A Coq
definition that doesn't capture the English word it's named for:''',
    r'''Before the list, three places to aim at me. A sentence of mine that says more than
the formal statement it cites (Appendix~\ref{sec:coq-statements} puts the load-bearing ones
side by side to make that easy). A definition that doesn't capture the English word it's named for:''')

add('The concluding statement of the machine’s results',
    'Let the results carry the conclusion. Retain the assumption status because the next paragraph contrasts it with the assumptions used for the game check.',
    '''All of that is proved in Coq with
no axioms: each file prints the assumptions of every headline theorem, and every line
comes back closed.''',
    '''The formal derivations of those results use no added axioms; the hypotheses of each
theorem are printed in its statement.''')

add('The concluding invitation to the reader',
    'Keep the admission that you found no counterexample without turning that search into an appeal to the checker’s authority. Preserve the distinction between a false theorem and an overreaching interpretation.',
    r'''I hunted. I came up empty. For a theorem Coq has
checked, that's no surprise: finding one would take a bug in the checker. The places a reader can really win are where my sentence says more
than the statement does, or a definition doesn't catch the word it's named for, and
Section~\ref{sec:falsification} starts with those.''',
    r'''I hunted. I came up empty. That leaves the arguments here for you to examine.
Even where a theorem holds, my sentence can say more than it establishes, or a definition
can fail to catch the word it's named for. Section~\ref{sec:falsification} starts with those.''')

# Construct the patch in memory only. Never write a revised manuscript.
proposed = original
for edit in edits:
    proposed = proposed.replace(edit['before'], edit['after'], 1)

structural = r'^\\(?:part|section|subsection|subsubsection|label|begin|end|clearpage|newpage).*'
assert re.findall(structural, original, re.M) == re.findall(structural, proposed, re.M)
assert original.count('\n\n') == proposed.count('\n\n')

(ROOT / 'proposed-edits.json').write_text(json.dumps(edits, indent=2, ensure_ascii=False)+'\n')
(ROOT / 'proposed-edits.patch').write_text(''.join(difflib.unified_diff(
    original.splitlines(keepends=True), proposed.splitlines(keepends=True),
    fromfile='a/monograph/monograph.tex', tofile='b/monograph/monograph.tex')))

aux = (SOURCE.parent / 'page-composition/build/book.aux').read_text()
refs = dict(re.findall(r'\\newlabel\{([^}]+)\}\{\{([^}]+)\}', aux))

def readable(s):
    s = re.sub(r'\\ref\{([^}]+)\}', lambda m: refs.get(m[1], m[1]), s)
    s = s.replace('~', ' ').replace('``', '“').replace("''", '”')
    return re.sub(r'\s+', ' ', s).strip()

intro = ('Ten proposed edits to the emphasis on Coq. None has been applied. '
         'They preserve the order and paragraph boundaries of the affected passages. '
         'All headings, personal narrative, theorem statements, proofs, source identifiers, '
         'and reproduction instructions remain as written. This is a focused editorial proposal, '
         'not a new mathematical audit or a book-design revision.')
note = ('The manuscript already says “Gap-catcher. Not the proof. The proof is the argument.” '
        'That passage needs no edit. The proposals bring the opening, summaries and invitations '
        'to scrutiny into line with it. Gallina does not appear by name in the current manuscript. '
        'The extended history in “What Coq is, and why” remains: shortening that authored excursion '
        'would be a separate editorial choice. These changes address the repeated appeal to the tool, '
        'not every mention of its use.')

style = '''body{max-width:850px;margin:60px auto;padding:0 24px;color:#202020;background:#faf9f5;font:18px/1.6 Georgia,serif}h1,h2,.label{font-family:Arial,sans-serif}h1{font-size:32px}h2{font-size:23px;margin-top:48px}.meta,.reason{color:#555;font-size:15px}.label{font-size:12px;letter-spacing:.08em;text-transform:uppercase;margin-bottom:4px}.passage{margin-top:0;padding-left:18px;border-left:2px solid #ccc}.after{border-color:#355c49}section{break-inside:avoid}a{color:#355c49}@media print{body{margin:0;background:white}h2{break-after:avoid}}'''
parts = ['<!doctype html><html lang="en"><meta charset="utf-8"><title>Proposed editorial changes — The Thiele Machine</title><style>'+style+'</style><body>',
         '<h1>The argument carries the book</h1><p class="meta">The Thiele Machine · Manuscript by Devon Thiele · Proposed edits only</p>',
         '<p>'+html.escape(intro)+'</p><p>'+html.escape(note)+'</p>']
for e in edits:
    parts.append(f'<section><h2>{e["number"]}. {html.escape(e["title"])}</h2><p class="reason">Source line {e["source_line"]}. {html.escape(e["reason"])}</p>')
    for key, label in [('before','Current'),('after','Proposed')]:
        parts.append(f'<p class="label">{label}</p><p class="passage {key}">{html.escape(readable(e[key]))}</p>')
    parts.append('</section>')
parts.append('</body></html>')
(ROOT / 'proposed-edits.html').write_text('\n'.join(parts))

styles = getSampleStyleSheet()
styles.add(ParagraphStyle(name='Reading', fontName='Times-Roman', fontSize=11, leading=15, spaceAfter=10))
styles.add(ParagraphStyle(name='SmallNote', fontName='Helvetica', fontSize=9, leading=12, textColor=colors.HexColor('#555555'), spaceAfter=10))
styles.add(ParagraphStyle(name='ChangeTitle', fontName='Helvetica-Bold', fontSize=14, leading=18, spaceBefore=18, spaceAfter=10, keepWithNext=True))
styles.add(ParagraphStyle(name='Tag', fontName='Helvetica-Bold', fontSize=8, leading=12, spaceBefore=5, spaceAfter=4, keepWithNext=True))
story = [Paragraph('The argument carries the book', styles['Title']),
         Paragraph('The Thiele Machine · Manuscript by Devon Thiele · Proposed edits only', styles['SmallNote']),
         Paragraph(html.escape(intro), styles['Reading']), Paragraph(html.escape(note), styles['Reading'])]
for e in edits:
    group = [Paragraph(f'{e["number"]}. {html.escape(e["title"])}', styles['ChangeTitle']),
             Paragraph(f'Source line {e["source_line"]}. '+html.escape(e['reason']), styles['SmallNote'])]
    for key, label in [('before','CURRENT'),('after','PROPOSED')]:
        group.extend([Paragraph(label, styles['Tag']), Paragraph(html.escape(readable(e[key])), styles['Reading'])])
    story.append(KeepTogether(group))

def footer(canvas, doc):
    canvas.setFont('Helvetica', 8)
    canvas.setFillColor(colors.HexColor('#666666'))
    canvas.drawString(22*mm, 15*mm, 'PROPOSAL ONLY · Manuscript unchanged')
    canvas.drawRightString(188*mm, 15*mm, str(doc.page))

doc = SimpleDocTemplate(str(ROOT/'proposed-edits.pdf'), pagesize=(210*mm,297*mm),
                        rightMargin=22*mm, leftMargin=22*mm, topMargin=22*mm, bottomMargin=24*mm,
                        title='The Thiele Machine — Proposed editorial changes', author='')
doc.build(story, onFirstPage=footer, onLaterPages=footer)
assert SOURCE.read_text() == original
(ROOT/'verification.json').write_text(json.dumps({
    'source': str(SOURCE), 'source_sha256': hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
    'proposal_count': len(edits), 'all_source_passages_unique': True,
    'structural_commands_unchanged_in_proposal': True, 'paragraph_break_count_unchanged_in_proposal': True,
    'manuscript_written': False, 'patch_applied': False
}, indent=2)+'\n')
print(f'Created {len(edits)} proposed edits; manuscript unchanged.')
