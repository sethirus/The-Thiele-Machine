special={
"[table: the sorter and the copier": r"""\begin{center}
\small
\begin{tabular}{@{}lp{3.2cm}cc p{3.2cm}cc@{}}
step & sorter does & record & count & copier does & record & count\\ \hline
start & nothing yet & no & 0 & nothing yet & no & 0\\
1 & sorts (ordinary steps) & no & 0 & copies in the typed list & no & 0\\
2 & checks ``in order'' on this list: passes & no & 1 & (no check) & no & 0\\
3 & raises the record & yes & 2 & tries to raise the record: refused & no & 1\\ \hline
\end{tabular}
\end{center}""",
}
