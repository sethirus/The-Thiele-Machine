# Blocks for chapter 20 (what keeping takes without heat). The measurement rows below were
# moved here from chapter 19's table because they test the quantum and fresh-state parts,
# which chapter 20 covers. Every row was checked against its source (2026-10-30).
special={
"[table: what has been measured": r"""\begingroup\small
\begin{longtable}{p{0.28\textwidth} p{0.64\textwidth}}
The loop & Rauer, Erne, Schweigler, Cataldini, Tajik and Schmiedmayer (2018): in an isolated
gas of thousands of atoms, the phase correlations, one collective measure of its coherence, came
partly back around, twice, each time a little lower. A collective quantity of a closed system
returned; the full state of the gas wasn't shown to return, and in a system that size couldn't be. \\[3pt]
Heat of collapse & Vinante and others (2017): a cantilever at millikelvin shows a force noise
of unknown origin, compatible with the heating one collapse model predicts. Donadi,
Piscicchia, Curceanu, Di\'osi, Laubenstein and Bassi (2021): the radiation a gravity-driven
collapse would give off wasn't seen at Gran Sasso, ruling out the version of that model with
no adjustable settings. These test the noise a collapse model adds, not a Landauer price on a
kept outcome. \\[3pt]
The ceiling on fresh states & Bekenstein's proposed bound uses energy and size; it isn't a
measured count of states. \\
\end{longtable}
\endgroup""",
"[table: the four-place box": r"""\begin{center}
\small
\begin{tabular}{@{}ccccc@{}}
Place & Tabletop & Pull the first lever & Pull the second lever & A start? \\ \hline
$a_0$ & 1 & end & $a_0$ & yes \\
$b_0$ & 2 & $b_0$ & $b_1$ & yes \\
$b_1$ & 0 & $b_1$ & end & yes \\
end & 0 & end & end & no \\ \hline
\end{tabular}
\end{center}""",
"[figure: the grid square": r"""\begin{center}
\begin{tikzpicture}[>=stealth, every node/.style={align=center,font=\small}]
\node (a) at (0,0) {grid $(0,0)$\\reads both bits set};
\node (b) at (4.4,0) {grid $(1,0)$\\reads first bit cleared};
\node (c) at (0,-2.7) {grid $(0,1)$\\reads second bit cleared};
\node (d) at (4.4,-2.7) {grid $(1,1)$\\reads both cleared};
\draw[->] (a)--node[above] {first lever}(b);
\draw[->] (a)--node[left] {second}(c);
\draw[->] (b)--node[right] {second}(d);
\draw[->] (c)--node[below] {first lever}(d);
\end{tikzpicture}
\end{center}""",
}
# Prose that goes with the last row (moved from chapter 19): Bekenstein's bound ties entropy to
# energy and size under its own physical assumptions; it doesn't hand you a finite list of a
# device's states. The counting in this book takes finitely many states as an assumption.
