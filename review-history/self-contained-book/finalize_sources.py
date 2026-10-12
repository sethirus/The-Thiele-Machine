from pathlib import Path
R=Path(__file__).parent;p=R/'apply_self_contained.py';s=p.read_text();anchor="s=re.sub(r'\\n{3,}','\\n\\n',s)"
extra=r'''s=s.replace(r'\section{Sources and mathematical dependencies}',r'\section{Sources}')
s=s.replace('These works provide the mathematical dependencies and intellectual background cited\nin the book.', 'These works are cited for their results, history and intellectual context.')
s=s.replace('construction is given in Section~\\ref{sec:universal-host} and\nSection~\\ref{sec:presented-universal}, and the counter and lambda references identify the\nestablished machinery under them.', r'''+'"""'+r'''construction is given in Sections~\ref{sec:universal-host} and~\ref{sec:presented-universal}
and Appendices~\ref{sec:quoting-construction}--\ref{sec:universal-blocks}. The counter and
lambda references credit the established constructions.'''+'"""'+''')
'''
assert anchor in s;s=s.replace(anchor,extra+anchor);p.write_text(s)
p=R/'check_manuscript.py';s=p.read_text().replace(r'\section{Sources and mathematical dependencies}',r'\section{Sources}');p.write_text(s)
