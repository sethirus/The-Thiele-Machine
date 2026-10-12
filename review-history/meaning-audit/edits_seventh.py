from audit import edit,span
span('opening-input-preparation',"And the heat isn't owed by every run.","And Landauer's principle is physics.",r'''And the heat isn't owed by every run. Landauer's principle, in the general form Part II adopts,
bounds mean heat by the uncertainty actually removed from the prepared inputs. For a deterministic
run from a known start, it supplies no positive heat floor; that doesn't show the device gives off
none (Theorem~\ref{thm:known-state}). Preparing both members of a colliding pair can give a
positive floor. The ledger toll still charges its mark on a known run, because merge pricing
prices the instruction regardless of which input was prepared. That is a premise of the ledger,
not another conclusion about heat.''','Keep preparation-dependent physical heat separate from preparation-independent instruction pricing.')
edit('ladyman-scope',r'''of their L-machines. That's the merge-pricing premise with an argument under it, and if you want
to argue with the premise, that's the paper to argue with.''',r'''of their L-machines. That's a physical argument under their stated model of a machine.
It deserves to be argued with on those terms; it does not by itself establish the book's
whole-number ledger charge.''','A physical result under L-machine assumptions does not imply the abstract merge-pricing rule.')
span('surroundings-heat-scope','Read that way, Landauer\'s premise is the claim',r'\subsection{How much:',r'''The heat claim needs more than moving a distinction outside the machine: another memory
could retain it. Under the physical conditions used here, when resetting removes actual
uncertainty into a thermal reservoir, Landauer bounds the mean heat handed over. None of
that heat has to be heat \emph{wasted}. Takahiro Sagawa's 2014 analysis says that erasure
can, in principle, approach a process that produces no entropy overall: the reservoir's
entropy goes up by what the machine's goes down. A positive mean heat transfer can therefore
be unavoidable without being wasteful. A known input has no uncertainty to remove, and
this entropy-loss premise alone sets no positive heat floor for it.''','Information transferred to another memory is not necessarily heat; distinguish heat transfer, total entropy production, and input uncertainty.')
span('device-envelope-quantifier',"So here's what this section actually earns.","Here's the general case,",r'''So here's what this section actually earns. A finite machine's permanent flag-raising
instruction has two allowed starting states that land on one state. Prepare those two
with equal chances: that instruction removes one bit, and under the adopted physical
premise its mean heat is at least $k_B T\ln2$. That is a worst-case preparation, not a
positive charge on every execution. A known start gives no positive entropy-loss floor;
whether a device can attain zero heat also depends on its dynamics and controls. The
ledger charges the merging instruction regardless of the preparation because merge
pricing explicitly requires that. The counting proves a collision, the preparation
determines the uncertainty removed, and the physical premises connect that removal to heat.''','State the existential worst-case preparation explicitly instead of implying a uniform physical cost.')
span('relaxation-scope','And one limited piece of the chances-and-time-spans version,','Hold that argument to what it says.',r'''There is also a limited statement about how long a noisy record lasts, using a different
quantity: total entropy production during relaxation. Take a device with no outside hand:
a random process hopping among finitely many states at rates that never change, with a
reverse for every hop and local detailed balance, able to get from any state to any other.
Require at least one up-state and one down-state. Left to run, it settles into a long-run
spread $\pi$. Measure each up or down stretch from its entrance, with entrances sampled
in the stationary process, and call the mean lengths $T_{\mathrm{up}}$ and
$T_{\mathrm{down}}$. Start the device in a known no-state $s$. The total entropy it
produces over relaxation is at least
$\ln(1+T_{\mathrm{up}}/T_{\mathrm{down}})$, in units of $k_B$.

The argument is three lines once the pieces have names. With fixed rates, total entropy
production is at least the drop in relative entropy to $\pi$; that follows from
Massimiliano Esposito and Christian Van den Broeck's split of entropy production (2010).
A known start $s$ has relative entropy $-\ln\pi(s)$, at least $-\ln\pi(\mathrm{no})$,
and the relative entropy runs down to zero as the device settles. The stationary chances
of up and down have the ratio of their mean stretch lengths, because crossings up and
down balance. Hence $-\ln\pi(\mathrm{no})=\ln(1+T_{\mathrm{up}}/T_{\mathrm{down}})$.

For a large up-to-down ratio, doubling that ratio raises this lower bound by about
$k_B\ln2$. Making both stretches longer by the same factor leaves it unchanged. Across
a family of devices whose ratio tends to infinity, the bound diverges; no single finite
irreducible device in this class keeps its flag up forever. This is a relaxation bound,
not a heat charge on each flip. It uses neither a thermodynamic reverse-path construction
nor time-symmetric control, so it does not identify the quantities in those other results.
It also does not close the known-input escape from the deterministic entropy-loss bound:
this noisy evolution and its total entropy production are a different question.''','Separate stochastic total entropy production from heat and deterministic logical entropy; remove unsupported identification with absolute irreversibility and time-symmetric control; distinguish ratio from absolute lifetime.')
edit('relaxation-exact-quantity',r'''exact price of the whole relaxation, and the bound is reached.''',r'''exact total entropy production of the whole relaxation, in units of $k_B$, and the
bound $-\ln\pi(s)$ is reached.''','Name the quantity and exact bound instead of calling it a generic price.')
edit('leaving-time-units',r'''up-states times their leaving times, comes to exactly one second.''',r'''up-states times their leaving times, comes to exactly one. Rates measured per second
times times measured in seconds give a dimensionless one.''','Correct the units in the backward equation for mean exit times.')
edit('narrowing-price-premise',r'''forgetting: on a finite machine, a flag
that stays up was paid for because raising it merged two states.''',r'''forgetting: under merge pricing, a finite machine's permanent flag-raising instruction
was paid for because it merges two states somewhere.''','Carry the pricing premise and operation-level quantifier into the next chapter.')
