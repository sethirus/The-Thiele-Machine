import sys
# usage: splice.py target.v part.v MARKER
# replaces the first occurrence of MARKER line in target with part contents followed by MARKER
t, p, m = sys.argv[1], sys.argv[2], sys.argv[3]
s = open(t, encoding='utf-8').read()
part = open(p, encoding='utf-8').read()
i = s.index(m)
s = s[:i] + part + s[i:]
open(t, 'w', encoding='utf-8', newline='\n').write(s)
