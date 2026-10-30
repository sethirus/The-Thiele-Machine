special={
"[table: the four doors": r"""\begin{center}\small
\begin{tabular}{@{}p{0.38\linewidth}rr>{\raggedright\arraybackslash}p{0.17\linewidth}@{}}
\toprule
Door & Wrong answers & Average steps & A Thiele machine? \\
\midrule
No shortcut at all, the long way every time & 0 & 25{,}992 & \\
1. Box stays up, editions wrap around & 37{,}564 & 17{,}027 & yes, and wrong \\
2. Box stays up, editions never reused (four to spend) & 0 & 22{,}529 & yes \\
3. One box, knocked down by every write & 0 & 20{,}082 & no: a toggle \\
4. Box tied to the value checked & 0 & 17{,}997 & yes \\
\bottomrule
\end{tabular}

\footnotesize Twenty thousand programs of forty moves each, on a number from 0 to 5; the long
way costs a thousand steps and the shortcut one. Wrong answers are counted over all of them.
\end{center}""",
}
