special={
"[row: 0101": r"""\begin{center}\texttt{0101010101010101 0101010101010101}\end{center}""",
"[table: three descriptions": r"""\begin{center}
\small
\begin{tabular}{@{}lrrr@{}}
Message & Original row & Two flips & Five specified flips\\ \hline
Write all 32 digits & 33 & 33 & 33\\
Repeat 01, list exceptions & 13 & 23 & 38\\
Repeat 010100, no exceptions & does not fit & depends & 17\\ \hline
\end{tabular}

\footnotesize For the last column, flip positions 5, 11, 17, 23 and 29. That defeats one
short description and supplies another. Pattern descriptions include the type bit,
length field and exception-count field. The raw row uses one type bit followed by
its thirty-two digits.
\end{center}""",
}
