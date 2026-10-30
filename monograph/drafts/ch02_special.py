special={
"If you're on A and looking at a 1": r"""\begin{quote}
If you're on A and looking at a 1: leave it, move the coin one square right, stay on A.\\
If you're on A and looking at a blank: write a 1 there, don't move, and change the letter to STOP.
\end{quote}""",
"[1] 1": r"""\begin{center}
\begin{tabular}{cccl}
\textbf{[1]} & 1 & \textvisiblespace & A\\
1 & \textbf{[1]} & \textvisiblespace & A\\
1 & 1 & \textbf{[\,\textvisiblespace\,]} & A\\
1 & 1 & \textbf{[1]} & STOP
\end{tabular}
\end{center}""",
"The step law.": r"""\begin{theorem}[The step law]\label{thm:step-law}
Let a rule give every state exactly one next state, and run it from a start $x_0$, writing
$x_0, x_1, x_2, \ldots$ for the run. Either every step lands on a state not visited before, or
there is a first step that lands on a visited state, from $x_n$ to $x_{n+1} = x_j$ with
$j \le n$. In that case every earlier step was fresh; if $j = 0$ the run has circled back to its
start, and if $j > 0$ the states $x_{j-1}$ and $x_n$ are different and both step to $x_j$, a
merge; and from $x_j$ on the run repeats with period $n + 1 - j$.
\end{theorem}""",
"Proof. If no state repeats": r"""\begin{proof}
If no state repeats, every step is fresh. Otherwise take the first step that lands on a visited
state, from $x_n$ to $x_{n+1} = x_j$. Every step before it was fresh, because this is the first
repeat. If $j > 0$, the states $x_{j-1}$ and $x_n$ both step to $x_j$. They are different:
$x_{j-1}$ comes earlier in the run than $x_n$, and if they were the same state, the run would
already have repeated a state before this step, which it didn't. Either way, one rule gives one
next state, so $x_{n+1} = x_j$ forces $x_{n+2} = x_{j+1}$, and so on: the run repeats from $x_j$ on.
\end{proof}""",
"Halting.": r"""\begin{theorem}[Halting]\label{thm:halting-hole}
A rule that may give some states no next state can settle a reading that stays settled with no
two states sharing a next state. Give every stopped state a next state by stepping it to itself,
and the step onto it becomes a merge: any state $c$ that steps onto a stopped state $h$, with $h$
stepping to $h$, shares its landing with $h$.
\end{theorem}""",
"Proof. With two states": r"""\begin{proof}
With two states $a$ (not done) and $b$ (done), $a$ stepping to $b$ and $b$ having no next
state, only one arrow exists, so no two arrows meet. Let $b$ step to $b$: now $a$ and $b$ both
step to $b$, and $a$ and $b$ are different. In general, if $c \ne h$, $c$ steps to $h$ and $h$
steps to $h$, then $c$ and $h$ share a next state.
\end{proof}""",
}
