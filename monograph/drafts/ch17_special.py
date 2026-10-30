special={
"[figure: genesis, two branches": r"""\begin{center}
\begin{tikzpicture}[>=stealth,every node/.style={align=center,font=\small}]
\node (g) at (0,0) {genesis\\round 0};
\node (l) at (-2,-1.8) {left\\round 1};
\node (r) at (2,-1.8) {right\\round 1};
\node (ll) at (-2,-3.5) {left child\\round 2};
\node (rr) at (2,-3.5) {right child\\round 2};
\draw[->] (g)--node[left] {A, B}(l);
\draw[->] (g)--node[right] {B, C}(r);
\draw[->] (l)--node[left] {A, B}(ll);
\draw[->] (r)--node[right] {B, C}(rr);
\end{tikzpicture}
\end{center}""",
"[table: the inclusion climb": r"""\begin{center}
\small
\begin{tabular}{@{}cll@{}}
Step & Card handed over & What you rebuild \\ \hline
Start & $d_3$ itself & $d_3$ \\
1 & $d_2$, on the left & $b$, joining $d_2$ and $d_3$ \\
2 & $a$, on the left & $L$, joining $a$ and $b$ \\
3 & $R$, on the right & the root, joining $L$ and $R$ \\ \hline
\end{tabular}
\end{center}""",
"[table: the five systems": r"""\begingroup\small
\begin{longtable}{@{}>{\raggedright\arraybackslash}p{0.15\linewidth}>{\raggedright\arraybackslash}p{0.17\linewidth}>{\raggedright\arraybackslash}p{0.16\linewidth}>{\raggedright\arraybackslash}p{0.18\linewidth}>{\raggedright\arraybackslash}p{0.21\linewidth}@{}}
\toprule
\textbf{System} & \textbf{Fee at the write} & \textbf{Bond} & \textbf{Budget} & \textbf{What my copy shows} \\
\midrule
\endhead
\bottomrule
\endlastfoot
Casper finality & none & the deposit, taken on a contradicting vote & none & two contradicting final checkpoints mean a third of the stake can be slashed \\
Gas & 20000 for a fresh slot, mostly refunded if taken back, up to a cap & none & the gas limit of each block & a write left standing in an empty slot nets at least 20000 \\
Attestation & none on the quoted registers & none & none on those registers & the quote can't tell you what it never measured \\
Transparency & none; a bad certificate can be seen & none & none & the RFC's own examples pass \\
Proof-carrying code & none required & none & none & a comparison of ideas; no checker is built here \\
\end{longtable}
\endgroup""",
}
