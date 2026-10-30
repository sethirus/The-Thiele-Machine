special={
"[figure: four cards into three boxes": r"""\begin{center}
\begin{tikzpicture}[thiele]
\node[cnode] (a) at (0,1.5) {A: one quarter};
\node[cnode] (b) at (0,.5) {B: one quarter};
\node[cnode] (c) at (0,-.5) {C: one quarter};
\node[cnode] (d) at (0,-1.5) {D: one quarter};
\node[pipe,text width=4cm,minimum width=0pt] (x) at (6,1.5) {X: one half\\could have been A or B};
\node[pipe,text width=4cm,minimum width=0pt] (y) at (6,-.5) {Y: one quarter\\was C};
\node[pipe,text width=4cm,minimum width=0pt] (z) at (6,-2.5) {Z: one quarter\\was D};
\draw[pipearrow] (a) -- (x);
\draw[pipearrow] (b) -- (x);
\draw[pipearrow] (c) -- (y);
\draw[pipearrow] (d) -- (z);
\end{tikzpicture}

\small Half the time one question is left open; half the time the card is known.
On average, half a bit is lost.
\end{center}""",
"[figure: work in, heat out": r"""\begin{center}
\begin{tikzpicture}[thiele]
\node[pipe,text width=5.8cm,minimum width=0pt] (a)
  {Old trap\\bead where it was};
\node[pipe,text width=5.8cm,minimum width=0pt,below=1.1cm of a] (b)
  {Changed trap\\bead in the same place};
\node[pipe,text width=5.8cm,minimum width=0pt,below=1.1cm of b] (c)
  {Same changed trap\\bead moved};
\draw[pipearrow] (a.south) -- node[right=8pt]{work in} (b.north);
\draw[pipearrow] (b.south) -- node[right=8pt]{heat out} (c.north);
\end{tikzpicture}

\small Work in minus heat out is the change in stored energy.
Either one can be negative on a single step.
\end{center}""",
"[table: bead simulation": r"""\begin{center}\small
\begin{tabular}{rrrr}
\toprule
Tilt time (s) & Success rate & Heat out on success & Work in on success\\
\midrule
2  & 0.909 & 2.517 & 2.501\\
5  & 0.916 & 1.466 & 1.490\\
10 & 0.913 & 1.073 & 1.095\\
20 & 0.899 & 0.830 & 0.907\\
40 & 0.893 & 0.773 & 0.782\\
80 & 0.869 & 0.693 & 0.719\\
\bottomrule
\end{tabular}

\footnotesize At the slowest setting the sampling errors are about $0.023\,kT$ for heat and
$0.011\,kT$ for work. They leave out error from the time step and from the model.
\end{center}""",
"[table: what has been measured": r"""\begingroup\small
\begin{longtable}{p{0.28\textwidth} p{0.64\textwidth}}
A merge, the floor & Jun, Gavrilov and Bechhoefer (2014): one bead in a feedback trap.
Squash two wells into one: $0.71 \pm 0.03\,kT$ of work, in the slow limit. Run the same
moves without the tilt, so nothing is squashed: $0.05 \pm 0.03\,kT$, also in the slow limit,
within two error bars of zero. $\ln 2$ is $0.693$. Same bead, same trap. \\[3pt]
The floor, three more ways & B\'erut and others (2012), a glass bead; Hong, Lambson, Dhuey
and Bokor (2016), tiny magnetic memory bits, within two standard deviations of Landauer;
Gaudenzi, Burzur\'i, Maegawa, van der Zant and Luis (2018), molecular spins at one kelvin. \\[3pt]
Lopsided wells & Gavrilov and Bechhoefer (2016), the feedback trap of Jun and others with a
lopsided double well: the average work to erase came out below $kT\ln 2$. The floor as
stated is for a symmetric memory. \\[3pt]
Time against heat & B\'erut and others (2012; B\'erut, Petrosyan and Ciliberto 2015): heat
$= kT\ln 2 + B/\tau$ fits with $B = 8.15\,kT\cdot\mathrm{s}$; left free, the floor of the fit
comes out at $0.72\,kT$. The floor is reached only as the time goes to infinity. \\[3pt]
How long a bit stays put & The same bead: the paper estimates a typical time to hop the
barrier of about 3,000 seconds at $8\,kT$, and about ten seconds at $2.2\,kT$. Those are
statistical time scales. The barrier height sets how long the bit is kept; it isn't itself
a measured heat payment. \\[3pt]
The loop & Rauer, Erne, Schweigler, Cataldini, Tajik and Schmiedmayer (2018): the coherence
of an isolated gas of thousands of atoms came back around. A collective quantity of a closed
system returned; the full state of the gas wasn't shown to return, and couldn't be. \\[3pt]
Heat of collapse & Vinante and others (2017): a cantilever at millikelvin shows a force noise
of unknown origin, compatible with the heating one collapse model predicts. Donadi,
Piscicchia, Curceanu, Di\'osi, Laubenstein and Bassi (2021): the radiation a gravity-driven
collapse would give off wasn't seen at Gran Sasso, ruling out the version of that model with no adjustable settings.
These test the noise a collapse model adds, not a Landauer price on a kept outcome. \\[3pt]
The ceiling on fresh states & Bekenstein's proposed bound uses energy and size; it isn't a
measured count of states. \\
\end{longtable}
\endgroup""",
}
