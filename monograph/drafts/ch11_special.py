special={
"[figure: Alice and Bob": r"""\begin{center}
\begin{tikzpicture}[thiele]
\node[pipe,text width=3.3cm,minimum width=0pt] (a) at (0,0) {Alice sends\\stamp 2};
\node[pipe,text width=3.3cm,minimum width=0pt] (b) at (5.8,0) {Bob receives\\stamp 3};
\node[pipe,text width=3.3cm,minimum width=0pt] (c) at (5.8,-2.8) {Bob replies\\stamp 4};
\node[pipe,text width=3.3cm,minimum width=0pt] (d) at (0,-2.8) {Alice receives\\stamp 5};
\draw[pipearrow] (a) -- node[above=6pt]{message} (b);
\draw[pipearrow] (b) -- node[left=8pt]{next local act} (c);
\draw[pipearrow] (c) -- node[below=6pt]{reply} (d);
\node[pipe,text width=9.1cm,minimum width=0pt] at (2.9,-5.1)
  {Elsewhere, Carol numbers an unrelated act 1.\\A smaller stamp alone does not prove a causal connection.};
\end{tikzpicture}

\small Start Bob at zero and Alice just after her local act 1. On receipt,
each raises the local count above both its old value and the incoming stamp.
\end{center}""",
}
