# Results

This file states the settled results about the small machine, Thiele
completeness over any event and with certification, the universal machine
and its definition, the record axis and the events it can
carry, recursion and undecidability, pricing and physics, and the real systems
the repository models. Further settled results are stated, with their premises
and declarations, in the mathematical specification
(monograph/thiele_machine_math_spec.tex) and are not repeated here: the CHSH
bounds and the bound named for Boris Tsirelson, who showed in 1980 that
quantum correlations give a CHSH value of at most 2√2, the lifting of every
universal base of every model of computation, the composition of
Thiele-complete machines, the priced host's program U_P and the computably
presented machines it runs, the verified compiler and its extraction to OCaml,
the theorem of the logician Henry Rice (1953) and the recursion theorem of the
logician Stephen Kleene (1938) for the two-counter machine, the record over
any order, and the results showing that each premise and each clause is
needed. Each result below names the Coq declarations that carry it and has one
of four statuses:

- **Proved.** The result has a proof, written out in the monograph for the
  results the monograph states, and a named Coq theorem states it formally.
  The formal version is a tool for catching mistakes; the argument is the
  reason to believe the result.
- **Refuted.** A Coq theorem states its negation, and a named declaration
  supplies the counterexample.
- **Conditional.** A Coq theorem states the result under a named premise
  that no machine fact discharges. The premise is a hypothesis of the
  statement; no axiom is added for it.
- **Not formalized here.** The question lies outside the formal development.
  The reason is given in one line.

Every theorem cited below is closed under the global context, except the ones
listed under "Standard-library axioms" at the end, which use only the Coq
standard library's real-number, classical-logic and functional-extensionality
axioms. No cited theorem uses a project axiom. `tests/test_results_doc.py`
checks that every cited declaration exists in `coq/` or `minimal/` and that
each cited theorem's axiom status (closed, or using only the standard-library
axioms listed at the end) agrees with the assumption receipt in
`artifacts/print_assumptions_all_proofs.txt`, which the receipt generator
writes on Linux.

## The small machine

The small machine of minimal/EarnedCore.v has two counters, a table of
checked facts, a certification flag and a ledger. Its counter instructions are
a two-counter machine and cost no marks; CHECK, COMMIT and CERTIFY cost one
each.

- **Proved.** From a clean start, every certified run contains a passing
  CHECK, then a passing COMMIT of that same claim with the counter untouched
  in between, then CERTIFY. Coq: `earned_certification_provenance`.
- **Proved.** On a run from a clean start, a fact whose counter has not been
  written since its check names a true claim about that counter.
  Coq: `checker_soundness`.
- **Proved.** From a clean start, a run ending with the flag up adds at least
  three to the ledger, and three is reached. Coq: `certified_run_min_cost`, `min_cost_tight`.
- **Proved.** The showcase check can fail, and a run whose check fails is
  refused forever. Coq: `earned_run_check_can_fail`,
  `earned_run_refused_forever`.
- **Proved.** The machine runs any two-counter program, halting exactly when
  the program halts. Coq: `simulation_run`, `halting_correspondence`.
- **Proved.** Its halting problem is undecidable, by reduction from the
  vendored two-counter result; it satisfies the certification floor, is
  adequate as a record-carrying machine, is a base-driven record over its base
  (program and core, everything but the ledger and the flag), and moves its
  record as a latch. Coq: `earned_core_halting_undecidable`,
  `earned_core_floor`, `earned_core_adequate`, `earned_core_honest`,
  `earned_core_is_latch`.
- **Proved.** For the machine over any property language with an exact
  equality test and a proved checker, the floor holds, and from a clean start
  provenance, checker soundness, no forging and the minimum cost of three
  hold, and read as a Thiele machine it is sound. Sorted lists are one instance,
  with a run that certifies and a run that is refused. Coq:
  `generic_earned_certification_provenance`, `generic_checker_soundness`,
  `generic_no_forging`, `generic_nfi_floor`, `generic_certified_run_min_cost`,
  `earned_generic_cs_sound`, `sorted_cs_sound`, `sorted_cs_demo_certifies`,
  `sorted_cs_demo_refused`.

## Thiele completeness over any event

The monograph calls the notion of this section Thiele-complete, and calls the
notion of the next section certified Thiele-complete. This file keeps the Coq
names: neutral-complete is `neutral_complete` (minimal/NeutralComplete.v), and
Thiele-complete is `thiele_complete` (minimal/ThieleComplete.v).

A machine is neutral-complete when some interface gives it four clauses, with
no claim, no checker and no certificate: a universal base (a two-counter
machine runs inside it) whose moves cannot touch the record, with a record
that stays up once it is up; a record that is down at every loaded start;
exact prices, nothing for a base move and one mark for every other move, with
the ledger adding the price of each move; and distinction, one fixed run that
raises the record from one loaded start and not from another. The event the
record registers is not fixed in advance; any event that some run tells apart
will do.

- **Proved.** In every neutral-complete machine a move that raises the record
  is not a base move, so the machine obeys the toll and has a universal base.
  From any state with the record down, a run that ends with it up contains a
  mark and raises the ledger by at least one. Coq: `nc_raise_is_mark`,
  `nc_is_weak`, `nc_floor_one`.
- **Proved.** Every neutral-complete machine hides its record and its ledger
  from its own window. From one loaded start, two runs end at the same window,
  one with the record up and one with it down, and two runs end at the same
  window with ledgers at least one mark apart. No function of the window gives
  the record, and none gives the ledger, at the end of every run from every
  loaded start. Every window is shown, record down and ledger unchanged, one
  free base move after some loaded start. Coq: `nc_hides_record`,
  `nc_hides_ledger`, `nc_no_oracles`, `nc_every_window_printed`.
- **Proved.** Every universal base lifts to a neutral-complete machine: add
  marks, each costing one and latching an event of the base state into the
  record. With the event "counter A is at least 1" the lift of any universal
  base is neutral-complete. For any family of events, the lift meets the
  distinction clause exactly when some fixed list of base moves leads two
  loaded starts to states that one of the events tells apart, and then it is
  neutral-complete. Coq: `every_base_lifts_neutrally`,
  `nlift_neutral_complete`, `nlift_distinction_iff`.
- **Proved.** A latch on an event that holds everywhere distinguishes nothing:
  its record is up after one step from every start. A latch tells two starts
  apart when its event holds along one run and not along the other.
  The distinction clause is what rules out a record that registers nothing.
  Coq: `latch_constant_up`, `latch_distinguishes`.
- **Proved.** Every Thiele-complete machine is neutral-complete. Thiele
  completeness through an interface is exactly neutral completeness through
  the same interface with its claims forgotten, plus three clauses: loaded
  starts are clean, the record rises only on an earned chain of a check, a
  commit and a certificate with a sound checker, and some claim's check can
  pass at one loaded start and fail at another. Coq:
  `thiele_complete_neutral`, `tc_iff_nc_plus_certification`.
- **Refuted.** Neutral completeness implies Thiele completeness. The paid
  test, a two-counter machine whose moves cost nothing plus a mark that
  registers "A is 0" and a mark that raises the record from every state, is
  neutral-complete and is not Thiele-complete; no Thiele-complete machine has
  a move that raises the record from every state. Coq: `nc_strictly_weaker`,
  `paid_test_has_tick`.
- **Proved.** Machines that fail one clause are not neutral-complete: every
  clock (the two-counter machine with every move costing one, under any
  reading of its configuration as the record), the silent machine (whose
  record never rises), the paid test with one more free move that lowers the
  record, a machine whose record no move changes while loaded starts disagree
  on it, and the paid test with every move priced one. Coq: `clock_not_nc`,
  `silent_not_nc`, `drop_not_nc`, `frozen_not_nc`, `paid_all_not_nc`.

## Thiele completeness

A Thiele machine (one whose record-raising steps cost at least one, the toll)
is weakly Thiele-complete when a two-counter machine runs inside it, that is,
when some interface gives it a universal base, with nothing asked of its
record. Thiele-complete asks for four clauses (minimal/ThieleComplete.v): a
universal base whose moves cost no marks and cannot touch the record, and a record that stays up once it is up; a record that,
from a clean start, rises only after a passing check of a claim, a commitment
to that same claim with nothing it is about changed in between, and a
certificate, with the checker proved to mean what it says; exact prices, one
mark for each of those three acts and nothing for anything else; and a claim
whose check, commit and certificate raise the record from a loaded start
exactly when the claim holds there, with the claim holding at some loaded
starts and failing at others.

- **Proved.** The small machine is Thiele-complete, and so are the same
  machine over any property language with an exact equality test, a proved
  checker and some property true of one number and false of another, and the
  sorted-list machine.
  Coq: `earned_core_thiele_complete`, `earned_generic_thiele_complete`,
  `sorted_machine_thiele_complete`.
- **Proved.** In every Thiele-complete machine the ledger counts the record
  moves; from a clean start, a run that raises the record adds at least three
  to the ledger, the claim it stands on holds at its CHECK and still holds at
  its COMMIT, and only CERTIFY raises the record; the check can fail, and
  some run certifies. Coq:
  `ledger_counts_record_moves`, `certificate_costs_three`,
  `committed_claim_holds` (the theorem of that name in `ThieleComplete.v`),
  `check_can_fail`, `some_run_certifies`, `only_certify_raises`.
- **Refuted.** Weak Thiele completeness implies Thiele completeness. Every
  clock-style machine is weakly Thiele-complete and fails the definition,
  whatever its record; so do a latched clock, a paid latch and a silent
  machine. Coq: `clock_weakly_thiele_complete`, `clock_not_thiele_complete`,
  `latch_clock_weakly_thiele_complete`, `latch_clock_not_thiele_complete`,
  `paid_latch_weakly_thiele_complete`, `paid_latch_not_thiele_complete`,
  `silent_weakly_thiele_complete`, `silent_not_thiele_complete`.
- **Proved.** Every Thiele-complete machine hides its record and its ledger
  from its own window: two runs from one clean start end at the same window,
  one certified with its ledger at least three marks higher, the other
  uncertified with its ledger unchanged. No function of the window recovers
  either. Coq: `complete_two_runs`, `complete_hides_record`,
  `complete_hides_ledger`, `thiele_complete_hides`.
- **Proved.** Every Thiele-complete machine is a Thiele machine whose
  window is blind to its reading. Coq: `thiele_complete_floor`,
  `complete_cs_window_blind`.

## The universal machine

- **Proved.** A host built on the small machine runs any of its programs as a
  guest, keeps a mirror that, from a loaded host, equals the guest's certified
  flag, and raises the mirror only in a guest step that passed CERTIFY,
  charged in that step, for every sequence of host moves. Coq:
  `record_agreement`, `no_free_host_certification_step`,
  `no_free_host_certification`, with the host's certification floor
  `host_nfi`. On this host, a machine from elsewhere enters through the
  two-counter encoding, and its own price list is not kept. On the priced
  host's program U_P, a computably presented machine keeps its own ledger plus
  a surcharge, which is at most 2 when the machine's reading starts at no and
  exactly 3 when it starts at yes (see the specification).
- **Proved.** U is one fixed program of the small machine's own instruction
  kinds, with no guest step built into anything. It runs every program of the
  small machine from every clean start start(x, y): each guest step is
  matched by a later U state, or both have halted. Coq: `U_simulation`.
- **Proved.** U halts exactly when its guest halts, with the guest's answer in
  its first two registers. Coq: `universal_halting`, `universal_output`.
- **Proved.** U's flag goes up at some step of its run if and only if the
  guest's goes up at some step of the guest's run, by its own check, its own
  commit and its own certificate. Coq: `universal_flag_iff`,
  `universal_earned`.
- **Proved.** U's ledger equals the guest's wherever the two runs line up, and
  lies between two consecutive guest ledgers everywhere else.
  Coq: `universal_ledger_exact`.
- **Proved.** The machine U runs on is Thiele-complete.
  Coq: `universal_thiele_complete`.

## The universal machine, defined

The definition `neutral_universal` (coq/kernel/foundation/NeutralUnivDef.v)
is the universal Thiele machine of the monograph; a certified universal
Thiele machine adds certification on top. It fixes a class of guests, a host,
an observation of each guest's state and a bound K, and asks for one program,
a reading of the host's state as a line, registers and a trap, a set of
raising lines, a load template, a coding of each guest into registers and a
decode from registers, such that (N0) the host is neutral-complete with its
counter moves as exactly its base moves; (N1) the run halts exactly when the
guest's run stops, at a state that matches the guest's last; (N2) the run
passes, at strictly increasing times, through host states that decode to the
guest's states, with the host's record equal to the guest's latched record
and the host's ledger equal to the guest's plus at most K; (N3) every record
move the program executes either traps or raises the record exactly when its
line is a raising line, from every untrapped state; (N4) the host is a
register host: INC, DEC and HALT on registers at price 0, record moves at
price 1 that leave the registers alone and go to the next line or trap, and
the next move fixed by the line and the trap; (N5) each guest is loaded with
the record down, no trap, a fixed line and the guest written into the
registers, and the decode reads only registers. The plain definition of
coq/kernel/foundation/UMachDef.v keeps (N1), (N2) and the host's own raise
and drops the rest.

- **Proved.** U is a neutral universal machine with surcharge 0 for every
  program of the small machine from every clean start. U_P is one with
  surcharge at most 3 for every computably presented machine. U_P's program
  read on a host with registers, INC, DEC, HALT, a mark, TICK and PAY and
  nothing else (CHECK, COMMIT and PAY read as PAY, CERTIFY as TICK) is one
  with surcharge at most 3 for the same class. Each matches its guests at
  strictly increasing times. Coq: `U_neutral_universal`,
  `UP_neutral_universal`, `UN_neutral_universal`, `U_in_order`,
  `UP_in_order`.
- **Proved.** The surcharge on a guest that raises its record for one mark is
  the price of certification. No Thiele-complete host with clean loads runs
  the countdown guest (count register 0 down, then mark) with a surcharge
  bound below 2, even with the order dropped, while the host with
  registers, TICK and PAY runs the whole countdown class with surcharge 0. On
  a guest whose record is up at its start, every host with a clean load pays
  at least one by the first matching time, and one is attained. Coq:
  `tc_cdown_two`, `down_universal`, `up_floor`, `up_attained`.
- **Proved.** Each clause stops a cheat. The host with a built-in guest step
  is no register host under any reading of its state. A host whose mark reads
  a register, and one whose record move reads a hidden copy of the guest's
  datum, meet every other clause and fail the raise by line; so does a host
  whose record move carries out a hidden copy's own mark. A host with a free
  move that fetches, decodes and executes the guest's next instruction meets
  everything else and is no register host. Coq: `gstep_not_reg`, `oracle_y`,
  `mirror_y`, `mirror2_not_line`, `need_N4`.
- **Proved.** The decode clause, as `neutral_universal` states it, lets the
  decode carry the guest: on a class of guests that never halt and never
  mark, a host loaded with all registers zero for every guest meets the
  definition with surcharge 0, its decode adding the guest in. Coq:
  `smuggle_universal`.
- **Proved.** Under the raise by line and the register-host clause, the line,
  the registers, the record and the ledger of a run before any trap depend
  only on the line, the registers and the record it starts from, whatever
  else the state holds. A host that carries a hidden copy of the guest,
  stepped by its counter moves, shows exactly the run of the host without it.
  Coq: `nr_determined`, `shadow_idle`.
- **Proved.** A guest that has paid while its record is down makes a host
  with a permanent record run a record move after which the record is still
  down, which is what PAY does. On U's host, which has no PAY, a four-line
  loop of COMMITs on an untouched claim pays the value of a register in marks,
  without raising the record or trapping. Coq: `pay_needed`,
  `commit_pay_loop`.
- **Proved.** The certified universal machine is the neutral one plus
  certification: its definition holds exactly when the neutral definition
  holds through the interface with its claims forgotten, the host's loads are
  clean for the full interface, the earned-record and non-vacuity clauses
  hold, and every rise of the host's record stands on an earned chain whose
  claim is tied to the guest. The earned part of that last clause already
  follows from Thiele completeness and clean loads. Coq:
  `cu_iff_nu_plus_certification`, `earned_part_free`.
- **Proved.** Thiele completeness of the host and an earned record do not by
  themselves stop a host that steps the guest with a built-in move: U's host
  with three free moves that fetch, decode and execute a guest instruction is
  Thiele-complete, and the host whose paid moves carry out the guest's own
  CHECK, COMMIT and CERTIFY has, whenever its flag is up at a matching time,
  its own check, commit and certificate on a guest check, commit and
  certificate that passed. The register-host clause is what excludes them.
  Coq: `hybrid_thiele_complete`, `mirror_earned`.
- **Proved.** The host machine of U, which has no PAY, is Thiele-complete and
  runs every two-counter program as a clock: after two set-up steps and two
  host steps per program step, registers 0 and 1 hold the program's counters,
  the trap and the flag are down, the ledger is one plus the number of
  program steps, and the host has halted exactly when the program has
  stopped. Coq: `thiele_complete_host_clock`.

## The record axis

The questions here ask how much of a machine the record axis pins down.

- **Proved.** Over any deterministic base, a computation-driven, priced,
  permanent, written record factors as a latch: the next record is the old
  record or a function of the base state (`record_axis_is_latch`). Two
  permanent records factor as two latches, each reading the other
  (`record_pair_is_two_latches`). Coq: `record_axis_is_latch_holds`,
  `record_pair_is_two_latches_holds`.
- **Proved.** Both premises do work: a record that can switch back off is not
  a latch, and a record switched on by a hidden clock is permanent and is not
  driven by the computation. Coq: `toggle_not_latch`, `toggle_not_permanent`,
  `clock_record_permanent`, `clock_record_not_driven`.
- **Proved.** Every base can carry the axis: the base plus a latch on any
  event it reaches, charging one unit when the latch sets, is a base-driven
  record. A reversible base with unbounded memory can carry one and stay
  reversible, paying room at every step; with finite memory a step that writes a permanent record is not
  injective. Coq: `latch_core_honest`, `history_latch_honest`,
  `history_latch_injective`, `finite_reversible_cannot_write`.

## Growing records

A growing record takes values in a partial order and only moves up
(`HonestGrowingExtension`).

- **Proved.** Every base-driven growing record satisfies a complete family of
  permanent threshold-update equations, one per lower threshold, and keeps its
  price schedule (`growing_record_decomposes`). This is a representation
  lemma: the threshold events are built from the driving function, and the
  schedule is a premise carried through. Coq: `growing_record_decomposes_holds`.
- **Proved.** The complete family of lower thresholds determines the record
  value (`thresholds_determine_record`). Coq:
  `thresholds_determine_record_holds`.
- **Proved.** On a growing record, pricing every strict value change is
  equivalent to pricing every false-to-true threshold flip
  (`record_price_iff_threshold_price`).
  Coq: `record_price_iff_threshold_price_holds`.
- **Refuted.** One Boolean latch carries every base-driven growing record
  (`one_latch_suffices`). Counterexample: a fully priced three-value chain
  over a one-state base (`ThreeMachine`, `OneBase`, `ThreeCover`, with the base-driven
  conditions proved by `three_honest`). Three values cannot be decoded from one base
  state and one bit. Coq: `one_latch_refuted`.
- **Proved.** A pairwise-distinct, pointwise-monotone chain of k-bit vectors
  has at most k + 1 members (`chain_needs_bits`). A chain through n
  distinct values in this representation needs at least n - 1 bits. The
  bound concerns monotone Boolean-vector encodings only; other encodings are
  outside it. Coq: `chain_needs_bits_holds`.

## Accountable finality

- **Proved.** In the Casper FFG model, two finalized blocks on conflicting
  branches imply a quorum whose votes satisfy a slashing condition. The proof
  is constructive. Coq: `accountable_safety`, `conflicting_records_are_priced`,
  with the key step `distinct_justified_same_epoch_slashes`. This is the
  accountable-safety theorem of Casper FFG, the finality gadget Vitalik
  Buterin and Virgil Griffith proposed for Ethereum in 2017. It shows that
  slashable votes exist. Whether a slash is executed, or finality deleted, is
  outside the model.
- **Proved.** The premise of accountable safety is inhabited: a concrete
  three-validator fork finalizes two conflicting blocks and its slashed
  quorum is computed. Coq: `casper_fork_exists`, `casper_fork_slashable`.
- **Proved.** Writing a finalization record need not slash anyone: a
  one-validator setting finalizes with no slashing.
  Coq: `finalization_without_slashing`.

Accountable conflict fits the permanent-record axis when a contradiction
entails a stated penalty. A record that is actually revoked does not: a
revocable flip is not forced to pay the finite-state price, and it keeps
nothing (`revocable_certificate_escapes`).

## Probabilistic records

In a finite positive-weight branching model:

- **Refuted.** A deterministic latch handles branching
  (`deterministic_latch_handles_branching`). Counterexample:
  `fair_branch_kernel`, whose two positive branches force one event value to
  be both false and true. Coq: `deterministic_latch_handles_branching_refuted`.
- **Refuted.** Equal branch support and equal branch charges determine the
  branch weights (`schedule_determines_probabilities`). Counterexample:
  `fair_branch_kernel` (weights 1 and 1) against `biased_branch_kernel`
  (weights 1 and 2), both honest by `fair_branch_honest` and
  `biased_branch_honest`. Coq: `schedule_determines_probabilities_refuted`.
  Uniqueness up to the schedule fails; the probability kernel has to be
  preserved as well.
- **Proved.** The relation that preserves ordered weight lists exactly is
  reflexive. This is a well-formedness check only.
  Coq: `probability_preserving_equivalence_reflexive_holds`.

## Bases and granularity

`weak_base_equiv` relates two observed bases when they agree on the chosen
observations and on halting, and a step on either side matches zero or more
steps on the other.

- **Proved.** `weak_base_equiv` is an equivalence relation.
  Coq: `weak_base_equiv_refl_holds`, `weak_base_equiv_sym_holds`,
  `weak_base_equiv_trans_holds`.
- **Proved.** Weakly equivalent bases agree on whether the record axis is a
  latch over them. The statement does not use its equivalence premise, since
  `record_axis_is_latch_holds` proves both sides for every deterministic base.
  Coq: `weak_equiv_preserves_record_latch_holds`.
- **Proved.** The record axis is a latch over three concrete bases: the toy
  Turing machine, the Cook and Reckhow unit-cost RAM over natural numbers
  (the random-access machine Stephen Cook and Robert Reckhow defined to
  measure time bounds, Journal of Computer and System Sciences 7, 1973;
  indirect load and store, conditional jumps), and the lambda calculus L
  under weak call-by-value reduction.
  Coq: `record_axis_is_latch_on_tm_holds`, `record_axis_is_latch_on_ram_holds`,
  `record_axis_is_latch_on_l_holds`.
  The RAM is a separate machine with random access through registers
  (`ram_store_then_load`, `ram_jump_pos_taken`, `ram_halted_stutters`,
  `ram_pointer_demo_runs`). The L step function is computed by structure and
  agrees with the reduction relation (`l_step_fun_correct`,
  `l_base_halted_iff_irreducible`, `l_base_run_is_star`, `star_is_l_base_run`).

## Concrete record machines

- **Proved.** A tied RAM appends the overwritten value to its record on every
  write; an untied RAM leaves its record unchanged, and equal base values do
  not determine an untied record. Coq: `ram_tied_overwrite_records_old_value`,
  `ram_untied_overwrite_has_no_record`,
  `ram_untied_record_not_determined_by_base`.
- **Proved.** Unbounded and modular arithmetic updates are undone by their
  syntactic inverses. These are reversible cores in the style of Janus, the
  reversible programming language that Christopher Lutz and Howard Derby
  wrote at Caltech in 1982 and that Tetsuo Yokoyama and Robert Glück gave a
  formal semantics in 2007. The full Janus language is outside the model.
  Coq: `janus_like_unbounded_inverse`, `janus_like_bounded_inverse`.
- **Proved.** In list memory, a write to an existing cell reads back, the
  tied step appends exactly the address and old value, the untied record never
  changes, and both machines agree on memory and program counter. Coq:
  `concrete_ram_write_reads_back`, `concrete_tied_ram_records_overwrite`,
  `concrete_untied_ram_record_unchanged`, `concrete_tied_and_untied_same_base`,
  with the executed example `concrete_ram_two_cell_witness`.

## Recursion and undecidability

- **Proved.** Over any substrate with a recursion theorem, a representable
  two-way branch, and a shortcut predicate that respects behavior and is
  nontrivial, no decider the substrate can run returns true exactly when the
  predicate holds.
  Coq: `structural_shortcut_undecidable`, `admits_shortcut_not_decidable`.
  The natural-number substrate meets the recursion premise by construction:
  `nat_structural_shortcut_undecidable`, `nat_self_undecidable`.
- **Proved.** The lambda calculus L, built from its reduction rules, has the
  second recursion theorem, Rice's theorem and an undecidable halting problem.
  Coq: `second_recursion`, `L_rice`, `L_halting_undecidable`. L is the
  calculus Yannick Forster and Gert Smolka presented as a model of
  computation for computability theory in Coq (Interactive Theorem Proving,
  ITP 2017), and Yannick Forster, Fabian Kunze, Gert Smolka and Maximilian
  Wuttke later checked in Coq that L and Turing machines simulate each other
  (ITP 2021). The Turing-completeness of L is not re-proved in the
  repository's own files; it comes from the models-equivalence theorem of the
  vendored Coq Library of Undecidability Proofs
  (vendor/coq-undecidability/theories/Synthetic/Models_Equivalent.v), which is
  checked with the build.
- **Proved.** The complement of two-counter halting is undecidable, from the
  vendored two-counter result. Coq: `MM2_HALTING_compl_undec`.

## The bill

The monograph's point is that nothing becomes something for free: a
distinction that comes into being dissipates by happening (in any real
device, in finite time; physics, with one proved instance below), and keeping
it is paid on top, in a merge or in room. Certification is the sharpest case.

- **Proved.** Every step of a deterministic run on any set of states is fresh,
  a merge (two distinct states with one next state), or a revisit from the
  same state after which the run is periodic. No finiteness is assumed.
  Coq: `step_law`, `merge_is_collision`, `revisit_means_loop`.
- **Proved.** On any set of states, a run that raises a permanent reading
  either merges two of its states or visits a fresh state at every step; an
  injective raising move visits a fresh state every time. Coq:
  `run_merges_or_fresh`, `permanent_flip_iterates_distinct`. A finite memory
  keeps the history of a reset through at most (M - 1)/(N - 1) repetitions,
  and the bound is attained. Coq: `retention_bound`, `tight_exact`.
- **Proved.** Writing a 0 on a blank cell merges blank with zero, and a
  finite extension of the cell still merges; an endless tape avoids the merge
  only by paying a fresh cell every write. Coq: `write_is_a_merge`,
  `four_state_escape_fails`, `tape_write_injective`.
- **Proved.** An injective step on finitely many states returns every run to
  its start, so a reversible finite machine keeps nothing. Coq:
  `returns_to_start`, `reversible_keeps_nothing`.
- **Proved.** A biased Brownian walk produces strictly positive entropy per
  tick at any nonzero speed, and heat times time is at least the distance
  squared. Coq: `heat_at_any_speed`, `heat_time_floor`.
- **Proved** in the monograph and in Coq: one mark per crossing of the reading
  from no to yes, `flips_le_cost` (coq/kernel/nfi/CostFrameworks.v).
- **Proved** in the monograph, with no Coq counterpart: the certainty bill (under entropy pricing,
  the uncertainty about the start is the part the run destroyed, at most its
  cost in bits, plus the part the end state still holds); and the same bill at
  every scale (a coarse merge forces a fine merge, unless the fine step leaves
  the described states or there are endlessly many of them).

## Pricing and physics

- **Proved.** For instructions with decidable equality, under every cost
  schedule that prices merges, no injective instruction is forced to have
  positive price (`no_price_beyond_merges`); with `forced_priced_iff_merges`,
  forced price is exactly non-injectivity. It is a direct corollary of
  `forced_priced_iff_merges` and says nothing about schedules outside that
  class. Coq: `no_forced_price_beyond_merges`.
- **Proved** at the logical level. A permanent finite write is a many-to-one
  step, so it pays logically (`permanent_flip_logical_payment`).
  Coq: `permanent_write_has_logical_payment`. Economic, cryptographic, and
  heat payment each need a premise about that level and are not derived.
- **Proved.** An eight-state machine with four program slots and a
  certification flag meets the three premises of the finite argument as
  theorems: it is finite, its certificate is permanent, its certify step and
  its jumps merge states, its advance step does not, and its cost rule prices
  exactly the merges, so A2 holds. Coq: `fin_finite`, `fin_permanent`,
  `fcertify_merges`, `fnext_injective`, `fin_merging_priced`,
  `fin_a2_from_merging_price`.
- **Refuted.** Mu has an intrinsic joule value (`no_intrinsic_joule_scale`
  states the refutation). Two distinct external scales fit the same
  natural-number ledger. Coq: `mu_has_no_intrinsic_joule_value`.
- **Proved**, with the scale supplied as an argument: at the Landauer scale
  `k_B T ln 2`, one mu unit is `k_B T ln 2` (`mu_landauer_calibration`), the
  product of the ledger and the scale. Coq: `calibrated_mu_landauer_energy`.
  The scale is named for Rolf Landauer, who argued at IBM in 1961 that a step
  that cannot be run backwards requires a minimal heat generation.
  Fixing the scale is a premise; nothing here measures it.
- **Conditional.** Given the `landauer_heat` premise and `0 <= kT`, flipping a
  permanent reading on a finite state space, with m certified states and k > 0
  flipping ones and starting from the uniform distribution on those m + k
  states, releases heat at least `kT ln((m + k)/m)`
  (`landauer_permanence_heat_floor`). Coq:
  `permanence_heat_floor_uses_landauer`, through `permanent_flip_heat_floor`.
  The finite-state entropy is invariant under permutation of the state
  enumeration: `semantics_entropy_permutation_invariant`. The heat floor is
  Landauer's principle applied to this step; the proved content is the link
  from a permanent record write to a many-to-one step.
- **Proved.** A two-state calorimeter protocol: a canonical reset from
  half-excited to ground satisfies a discrete master equation exactly, and at
  fixed Hamiltonian the bath receives `Delta / 2`. Coq:
  `canonical_reset_satisfies_master_equation`, `canonical_reset_heat_exact`.
- **Proved**, with the scale built in: choosing the gap `2 k_B T ln 2` gives
  heat `k_B T ln 2`. Coq: `selected_gap_gives_landauer_heat`.
- **Refuted.** The master equation and a one-unit ledger change force the
  Landauer bound. Counterexample: the same reset with gap `k_B T ln 2` releases
  half that heat; two different gaps give the same dynamics, which do not
  depend on the gap, and different heat.
  Coq: `canonical_reset_heat_below_landauer_at_small_gap`,
  `master_equation_does_not_fix_heat_scale`. The canonical reset is a
  bookkeeping toy with no second law: its rates (up 0, down 1) are in detailed
  balance at no gap (`canonical_rates_break_detailed_balance`), and with rates
  that are, a fixed-gap relaxation settles at `1 / (1 + exp (Delta / kT))`,
  which is `1/5` at the gap `2 k_B T ln 2`, and never below it
  (`detailed_balance_never_empties`, `landauer_gap_settles_at_one_fifth`).
- **Proved.** A driven reset with rates in detailed balance pays `k_B T ln 2`
  in work: raising the gap in steps and letting the register settle at each,
  the work is never below the free-energy change and exceeds it by at most the
  step size times the fall in population; for `N` equal raises from gap 0 to
  `D` it lies between `kT ln 2 - kT exp (- D / kT)` and `kT ln 2 + D / (2 N)`,
  with at most `exp (- D / kT)` left excited. Work minus heat is the change in
  mean energy. Coq: `detailed_balance_settles_at_gibbs`,
  `detailed_balance_thermalizing_step`, `driven_first_law`,
  `driven_work_second_law`, `driven_work_near_free_energy`,
  `driven_reset_work_window`.
- **Proved.** The protocol's ledger change is one unit, the price of one
  certification step on the small machine. No state map between the protocol
  and the machine is claimed. Coq: `canonical_reset_is_one_mu`.

## Real-system models

Each model below is narrow. None is a full security, consensus, database, or
audit-log theorem.

- **Proved** boundary checks for RFC 9162 Certificate Transparency: the
  iterative inclusion and consistency verifiers of RFC 9162 Sections 2.1.3.2
  and 2.1.4.2 reject the boundary cases, and symbolic runs accept the
  Section 2.1.5 examples. Coq: `rfc9162_inclusion_boundary_safe`,
  `rfc9162_consistency_boundary_safe`, `rfc9162_example_inclusion_d0`,
  `rfc9162_example_consistency_4_7`. Appending to a log history keeps old
  entries and grows the size (`ct_extension_preserves_entries`,
  `ct_extension_size_monotone`). Collision resistance and signed-tree-head
  authenticity are cryptographic premises and are not proved; the symbolic
  digests rule collisions out by construction and serve only to run the RFC
  control flow.
- **Proved** for a toy proof-carrying-code fragment: the executable checker
  accepts exactly the address-bound verification condition, a typed
  certificate entails it, and an out-of-range access is rejected.
  Coq: `pcc_checker_accepts_iff_vc`, `pcc_certificate_implies_vc`,
  `pcc_unsafe_program_rejected`, `pcc_safe_instance`. This mirrors the roles
  in George C. Necula's proof-carrying code (PCC, POPL 1997), where a program
  ships with a proof that it is safe. The full system is outside this model.
- **Refuted.** A bare sign/verify interface implies the authenticity of a
  Trusted Platform Module (TPM) quote.
  Counterexample: a scheme that always signs false and accepts every
  signature accepts true (`degenerate_accepts_forgery`).
  Coq: `tpm_interface_authenticity_refuted`. Authenticity needs a trusted-key
  or unforgeability premise.
- **Proved**: five narrow countermodels, each for a point that a governing
  source already addresses. A Certificate Transparency client's local view
  cannot detect a split log (`ct_local_view_insufficient`; RFC 9162, Section
  11.3, "Misbehaving Logs", <https://www.rfc-editor.org/rfc/rfc9162.html>). A
  quote checker must bind its selection of platform configuration registers,
  the PCR selection (`tpm_selection_binding_is_necessary`; tpm2-tools advisory
  GHSA-8rjm-5f5f-h4q6, CVE-2024-29039, on tpm2_checkquote and an altered PCR
  selection, <https://www.tenable.com/cve/CVE-2024-29039>). A local chain
  suffix does not fix the trusted anchor
  (`weak_subjective_suffix_insufficient`; Ethereum's weak-subjectivity
  guidance, <https://ethereum.org/en/developers/docs/consensus-mechanisms/pos/weak-subjectivity/>). An acknowledged commit needs a durable commit record
  (`wal_ack_requires_durability`; PostgreSQL documentation, Write-Ahead
  Logging (WAL), <https://www.postgresql.org/docs/current/wal-intro.html>). A
  current local log does not establish a past event
  (`audit_local_snapshot_insufficient`; NIST SP 800-92, Guide to Computer
  Security Log Management, Karen Kent and Murugiah Souppaya, 2006,
  <https://csrc.nist.gov/pubs/sp/800/92/final>). Each is a generic two-state
  collision or durability counterexample that does not need the record axis.
  No surveyed consequence is both new and specific to the record axis.

## The pointer criterion

The pointer-observable criterion is a thesis. Choosing the observers and
the event is a modeling choice that proofs cannot make. The formal
definitions and the selected model instances are proved only inside their
observer maps.

- **Proved.** Twelve candidate events over seven observer maps proliferate
  exactly as follows. Coq: `twelve_candidate_measurements_checked`.

  | Event | Observer map | Proliferates |
  |---|---|---|
  | finalized block | proof of stake | yes |
  | proposer work | proof of stake | no |
  | committed state | gas metering | yes |
  | scratch work | gas metering | no |
  | attestation issued | trusted execution | yes |
  | measurement noise | trusted execution | no |
  | certificate included | Certificate Transparency | yes |
  | prover effort | Certificate Transparency | no |
  | certificate checked | proof-carrying code | yes |
  | prover effort | proof-carrying code | no |
  | MAC authenticity | symmetric MAC | no |
  | signature authenticity | digital signature | yes |

  The MAC row is a model counterexample to universal proliferation
  (`mac_model_not_proliferating`). Reading it as a statement about forgery in
  deployed systems is a separate modeling premise.
- **Proved.** Swapping which event the fragments mirror swaps the unique
  pointer: the second event becomes the pointer and the first does not
  proliferate. Coq: `swapped_event_is_pointer_checked`,
  `first_event_not_proliferating`.
- **Refuted.** Consensus among authenticated observers that update by a
  local rule forces the observed event to be permanent. Counterexample:
  `toggle_game`, two observers that agree and update by negation, so the
  event turns false. Coq: `toggle_game_refutes_strong_pointer_necessity`.
- **Conditional.** If at least one observer exists, every view is sound and
  complete for the event, and a true view stays true (`durable_views`), the
  event is permanent. The persistence premise carries the conclusion.
  Coq: `durable_consensus_implies_permanence`.

## Not formalized here

- **Full proof-carrying code.** Necula's system (SAL execution, the LF
  encoding, the verification-condition generator, and both soundness
  translations) is another system; formalizing it is outside the Thiele
  Machine.
- **Full embeddings of four cost calculi.** Graded modal effect semantics
  (Dominic Orchard, Vilem Liepelt and Harley Eades, who put grades into the
  types of a working language, ICFP 2019), the cost translation of the
  programming-language researchers Norman Danner, Daniel Licata and Ramyaa
  (ICFP 2015), automatic amortized resource analysis, and linear-logic
  resource semantics are other systems. The repository proves the fragments
  it uses: `a2_and_aara_iff_exact`, `flips_le_cost`,
  `certification_system_is_potential_method`, `nfi_by_potential`.
- **Certificate Transparency gossip and checkpoint distribution.** RFC 9162
  leaves gossip undefined, and the weak-subjectivity guidance specifies no
  distribution protocol, so there is no protocol semantics to formalize.
- **Persistent-memory durability barriers.** This needs a hardware model of
  flush completion and power failure that the platform documentation does
  not give.
- **Storage-energy and joule calibration.** These need physical measurement
  on a device; none is part of this repository.
- **Cryptographic hardness.** Collision resistance, signature
  unforgeability, and signed-tree-head authenticity appear only as premises.

## Standard-library axioms

These cited theorems depend on axioms drawn only from the Coq standard library:
the real-number axioms `ClassicalDedekindReals.sig_forall_dec` and
`ClassicalDedekindReals.sig_not_dec`,
`Classical_Prop.classic`, and
`FunctionalExtensionality.functional_extensionality_dep`.

- `calibrated_mu_landauer_energy`
- `canonical_rates_break_detailed_balance`
- `canonical_reset_heat_below_landauer_at_small_gap`
- `canonical_reset_heat_exact`
- `canonical_reset_satisfies_master_equation`
- `detailed_balance_never_empties`
- `detailed_balance_settles_at_gibbs`
- `detailed_balance_thermalizing_step`
- `driven_first_law`
- `driven_reset_work_window`
- `driven_work_near_free_energy`
- `driven_work_second_law`
- `heat_at_any_speed`
- `heat_time_floor`
- `landauer_gap_settles_at_one_fifth`
- `master_equation_does_not_fix_heat_scale`
- `mu_has_no_intrinsic_joule_value`
- `permanence_heat_floor_uses_landauer`
- `permanent_flip_heat_floor`
- `selected_gap_gives_landauer_heat`
- `semantics_entropy_permutation_invariant`
