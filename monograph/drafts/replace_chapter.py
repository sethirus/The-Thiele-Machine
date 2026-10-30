"""Replace one chapter of thiele_machine.tex with a fresh conversion of its draft."""
import sys, importlib
sys.path.insert(0, 'drafts')
from md2tex import convert
draft, label, blocks = sys.argv[1], sys.argv[2], (sys.argv[3] if len(sys.argv) > 3 else None)
special = importlib.import_module(blocks).special if blocks else {}
tex = convert(open(draft).read(), label, special)
p = 'thiele_machine.tex'; s = open(p).read()
bar = '%' + '=' * 75 + '\n'
title = open(draft).read().strip().split('\n')[0].strip()
i = s.index(bar + '\\section{%s}' % title)
j = s.find(bar + '\\section{', i + 1)
if j < 0: j = s.index('\\end{document}')
s = s[:i] + tex + '\n' + s[j:]
open(p, 'w').write(s)
