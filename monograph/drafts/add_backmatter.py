"""Set the appendices (and, when given, the sources) after the afterword of thiele_machine.tex."""
import sys, importlib
sys.path.insert(0, 'drafts')
from md2tex import convert
APPS = [('drafts/24_things_i_had_to_learn_first.md', 'sec:vocab', None),
        ('drafts/25_every_assumption_in_one_place.md', 'sec:assumptions', None),
        ('drafts/26_whats_mine_and_what_isnt.md', 'sec:whats-mine', 'ch26_special')]
p = 'thiele_machine.tex'; s = open(p).read()
mark = '%' + '=' * 75 + '\n\\appendix\n'
if mark in s:
    s = s[:s.index(mark)] + '\\end{document}\n'
out = [mark]
for d, label, blocks in APPS:
    special = importlib.import_module(blocks).special if blocks else {}
    out.append(convert(open(d).read(), label, special) + '\n')
if len(sys.argv) > 1:
    out.append(open(sys.argv[1]).read() + '\n')
i = s.rindex('\\end{document}')
s = s[:i] + ''.join(out) + '\\end{document}\n'
open(p, 'w').write(s)
