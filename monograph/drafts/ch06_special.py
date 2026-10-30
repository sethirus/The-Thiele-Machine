special={
"[figure: the five stages": r"""\begin{center}
\begin{tikzpicture}[thiele]
\node[pipe,text width=3.4cm,minimum width=0pt] (a) {proposed\\\texttt{0000}};
\node[pipe,text width=3.4cm,minimum width=0pt,below=0.55cm of a] (b) {set up\\\texttt{1000}};
\node[pipe,text width=3.4cm,minimum width=0pt,below=0.55cm of b] (c) {run\\\texttt{1100}};
\node[pipe,text width=3.4cm,minimum width=0pt,below=0.55cm of c] (d) {read\\\texttt{1110}};
\node[pipe,text width=3.4cm,minimum width=0pt,below=0.55cm of d] (e) {recorded\\\texttt{1111}};
\draw[pipearrow] (a.south) -- (b.north);
\draw[pipearrow] (b.south) -- (c.north);
\draw[pipearrow] (c.south) -- (d.north);
\draw[pipearrow] (d.south) -- (e.north);
\end{tikzpicture}

\small Read down the drawing. Zero means cup down, one means cup up. Four cups give five stages
along this run because each new stage turns up one unused cup.
\end{center}""",
"[figure: the diamond]": r"""\begin{center}
\begin{tikzpicture}[thiele]
\node[pipe,text width=3.6cm,minimum width=0pt] (n) at (0,0) {Neither act\\\texttt{000}};
\node[pipe,text width=3.6cm,minimum width=0pt] (r) at (-3.2,2.6) {Experiment repeated\\\texttt{100}};
\node[pipe,text width=3.6cm,minimum width=0pt] (c) at (3.2,2.6) {Calculation checked\\\texttt{010}};
\node[pipe,text width=3.6cm,minimum width=0pt] (b) at (0,5.2) {Both acts\\\texttt{111}};
\draw[pipearrow] (n) -- (r);
\draw[pipearrow] (n) -- (c);
\draw[pipearrow] (r) -- (b);
\draw[pipearrow] (c) -- (b);
\end{tikzpicture}

\small Read the cups as repeat, calculation, both. Neither middle point
includes the other. The third cup repeats information already supplied by
the first two; it is useful for showing thresholds, not needed for storage.
\end{center}""",
}
