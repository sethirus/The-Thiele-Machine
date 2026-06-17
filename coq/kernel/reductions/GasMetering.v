(** GasMetering: gas-schedule exactness against the pricing-uniqueness kernel.

    An execution-fee schedule (EVM-style gas) is a local pricing law: each
    step is charged or it isn't, and the schedule is trusted to charge
    exactly where it says it charges. This file instantiates
    [LocalPredicatePricedSystem] with charge predicate "this instruction
    commits state" (state-root finalization as the certification event).

    Main theorem [gas_schedule_exactness]: any schedule satisfying the two
    conditions an honest fee market wants —
      floor:        no state-certifying step is free, and
      no-overcharge: nothing else is billed as a commitment —
    is extensionally the cert-flip schedule with exact unit pricing. This is
    [exact_commitment_pricing_characterization] wearing EVM vocabulary.

    Corollaries: an undercharged committing opcode admits a zero-cost
    certifying trace (the historical 2016 underpriced-opcode DoS episodes
    are this corollary executed against mainnet); charging a non-committing
    step breaks exactness in the other direction.

    FALSIFIER: construct a conforming schedule (floor + no-overcharge) whose
    charge predicate differs from cert-flip on some reachable step. Coq
    accepts its construction if it exists; [gas_schedule_exactness] falls.

    This file does not bound gate counts, model gas refunds, or price
    anything except the commitment event itself. *)

From Coq Require Import List Arith.PeanoNat Lia Bool.
Import ListNotations.

From Kernel Require Import CommitmentPredicateAdequacy.

(* The constructive bridge at the end of the file prices the kernel VM's own
   certification channel, so the abstract fee-market results land on the
   machine the kernel is about. *)
From Kernel Require Import VMState VMStep SimulationProof AbstractNoFI.

(** * Vocabulary

    Three words of EVM jargon, glossed once so the rest reads plainly.

    GAS.  The per-step execution fee. In the kernel's terms this is
    [lps_cost]: a state-dependent nat charged when a step runs. "Out of
    gas" and refund mechanics are out of scope; we price steps, not
    budgets.

    OPCODE.  One instruction of the execution layer — [lps_instr]. An
    opcode's fee may depend on the state it executes in (EVM does this
    too: SSTORE on a fresh slot vs. a warm one), which is why [lps_cost]
    takes the state as an argument.

    COMMITMENT.  The certification event: the step after which the state
    root is finalized — externally checkable, no longer revisable. The
    kernel's [lps_cert] is the "is this state committed?" flag, and
    [cert_flip_local] is the predicate "this step takes an uncommitted
    state to a committed one." That flip is the A2 event wearing a
    blockchain costume.

    A gas schedule is then exactly a [LocalPredicatePricedSystem]: it
    picks a charging predicate [lps_charge] ("which steps cost gas?")
    and is trusted to bill where the predicate says and nowhere else
    ([lps_charged_costs] / [lps_uncharged_free]). The alias below adds
    no structure; it lets the theorems read in fee-market vocabulary. *)

Definition GasSchedule := LocalPredicatePricedSystem.

(** * Main 1: the exactness characterization, in gas vocabulary.

    [gas_schedule_exactness]: a gas schedule satisfies the two
    conditions an honest fee market wants —

      floor:         total gas collected on any trace is at least the
                     number of commitment events in it
                     ([quantitative_certification_floor]), and
      no-overcharge: total gas never exceeds that count
                     ([no_overcharge_for_commitments])

    — exactly when its charging predicate is extensionally the
    cert-flip predicate and every charged step costs exactly one unit
    ([local_predicate_same] + [exact_unit_pricing]). Under equal trust
    there is one exact schedule for pricing commitment, and it charges
    on commitment.

    HONESTY NOTE: since [GasSchedule] is definitionally
    [LocalPredicatePricedSystem], this theorem IS the kernel's
    [exact_commitment_pricing_characterization] carried over unchanged —
    the proof is a one-line instantiation, and the contribution of this
    statement is the reading, not new mathematics. The new mathematics
    in this file is downstream: the failure modes (Mains 2 and 3) and
    the concrete inhabitants ([toy_gas_schedule_is_exact],
    [thiele_vm_commit_pricing_is_exact]). *)
(* INQUISITOR NOTE: alias for exact_commitment_pricing_characterization — deliberate vocabulary re-export; the file's new content is the failure modes and concrete instances below. *)
Theorem gas_schedule_exactness :
  forall G : GasSchedule,
    (quantitative_certification_floor G /\
     no_overcharge_for_commitments G)
    <->
    (local_predicate_same G (cert_flip_local G) (lps_charge G) /\
     exact_unit_pricing G).
Proof.
  exact exact_commitment_pricing_characterization.
Qed.

(** * Main 2: an undercharged opcode admits a free commitment.

    If some opcode [i], executed in some uncommitted state [s], commits
    the state but the schedule does not charge it, then the one-step
    trace [[i]] from [s] certifies at total gas zero. The proof is
    nothing but [lps_uncharged_free]: a trusted schedule bills only
    where its predicate says, so a predicate gap is a free pass through
    the commitment event.

    The theorem prices the limiting case: the charge on a committing
    step is missing entirely, and the trace is free. The 2016 Ethereum
    underpriced-opcode DoS episodes (the attacks that forced the EIP-150
    repricing) were the graded version of the same failure shape —
    opcodes priced far below their real cost, attackers buying state
    growth almost free. The fix, repricing, is restoring the charging
    predicate's coverage; in the limiting case that is exactly
    [covers_cert_flips].

    FALSIFICATION: exhibit [G], [s], [i] with an uncharged committing
    step whose one-step trace still costs gas. That would mean a
    trusted schedule billed outside its own predicate, contradicting
    [lps_uncharged_free]: it would break the kernel record, not
    just this file. *)
Theorem undercharged_opcode_admits_free_commitment :
  forall (G : GasSchedule) (s : lps_state G) (i : lps_instr G),
    lps_cert G s = false ->
    lps_cert G (lps_step G s i) = true ->
    lps_charge G s i = false ->
    lps_total_cost G [i] s = 0.
Proof.
  intros G s i _ _ Huncharged.
  simpl.
  rewrite (lps_uncharged_free G s i Huncharged).
  reflexivity.
Qed.

(** Corollary: a schedule with even one undercharged committing opcode
    fails the universal certification floor outright — some certifying
    trace is free. One missed flip is enough; the floor is not a
    statistical property that survives small leaks.

    Instantiation note: this is [floor_necessary_for_covers_cert_flips]
    read in contrapositive at the witnessing step. *)
Corollary undercharged_opcode_breaks_certification_floor :
  forall (G : GasSchedule) (s : lps_state G) (i : lps_instr G),
    lps_cert G s = false ->
    lps_cert G (lps_step G s i) = true ->
    lps_charge G s i = false ->
    ~ universal_certification_floor G.
Proof.
  intros G s i Hstart Hfinal Huncharged Hfloor.
  pose proof (floor_necessary_for_covers_cert_flips G Hfloor
                s i Hstart Hfinal) as Hcharged.
  rewrite Huncharged in Hcharged.
  discriminate Hcharged.
Qed.

(** * Main 3: overcharging breaks exactness in the other direction.

    If the schedule charges a step that is not a commitment (the step
    does not flip cert false-to-true), then total gas on the one-step
    trace through it exceeds its commitment count, so the schedule
    overcharges relative to commitments. Undercharging kills the floor
    (Main 2); overcharging kills the ceiling. Exactness pins the
    predicate from both sides — that pincer is what makes the
    characterization in Main 1 an "iff" rather than a one-way bound.

    Instantiation note: this is the contrapositive of the kernel's
    [no_overcharge_forces_charge_only_on_cert_flips] at the witnessing
    step. *)
Theorem overcharge_breaks_exactness :
  forall (G : GasSchedule) (s : lps_state G) (i : lps_instr G),
    lps_charge G s i = true ->
    cert_flip_local G s i = false ->
    ~ no_overcharge_for_commitments G.
Proof.
  intros G s i Hcharged Hnoflip Hno.
  pose proof (no_overcharge_forces_charge_only_on_cert_flips G Hno
                s i Hcharged) as Hflip.
  rewrite Hnoflip in Hflip.
  discriminate Hflip.
Qed.

(** * A concrete exact schedule: the characterized class is inhabited.

    Mains 1-3 would be vacuously true of an empty class. So here is the
    smallest gas-metered machine that earns the characterization:

    State:  one bit — "has the state root been committed?"
    Opcodes:
      [OpCompute] — pure computation; never touches the committed flag.
      [OpCommit]  — finalizes; sets the committed flag.
    Cert:   the flag itself.
    Charge: the canonical predicate — charge exactly when the commit
            flips the flag (committing an already-committed state is a
            no-op and free, like a warm SSTORE writing the same value).
    Cost:   one unit per charged step, zero otherwise. *)

Inductive toy_op : Type :=
  | OpCompute
  | OpCommit.

Definition toy_step (s : bool) (i : toy_op) : bool :=
  match i with
  | OpCompute => s
  | OpCommit  => true
  end.

(** Charge exactly when [OpCommit] flips the flag false-to-true. *)
Definition toy_charge (s : bool) (i : toy_op) : bool :=
  match i with
  | OpCompute => false
  | OpCommit  => negb s
  end.

Definition toy_cost (s : bool) (i : toy_op) : nat :=
  if toy_charge s i then 1 else 0.

Lemma toy_charged_costs :
  forall (s : bool) (i : toy_op),
    toy_charge s i = true -> toy_cost s i >= 1.
Proof.
  intros s i Hcharged.
  unfold toy_cost.
  rewrite Hcharged.
  lia.
Qed.

Lemma toy_uncharged_free :
  forall (s : bool) (i : toy_op),
    toy_charge s i = false -> toy_cost s i = 0.
Proof.
  intros s i Huncharged.
  unfold toy_cost.
  rewrite Huncharged.
  reflexivity.
Qed.

Definition toy_gas_schedule : GasSchedule :=
  {| lps_state  := bool;
     lps_instr  := toy_op;
     lps_step   := toy_step;
     lps_cost   := toy_cost;
     lps_cert   := fun b => b;
     lps_charge := toy_charge;
     lps_charged_costs  := toy_charged_costs;
     lps_uncharged_free := toy_uncharged_free |}.

(** The toy's charging predicate is extensionally the cert-flip
    predicate: four cases (two states, two opcodes), checked by
    computation. *)
Lemma toy_charge_is_cert_flip :
  local_predicate_same toy_gas_schedule
    (cert_flip_local toy_gas_schedule)
    (lps_charge toy_gas_schedule).
Proof.
  split; intros s i H; destruct s, i;
    cbv in H; cbv; congruence.
Qed.

(** Each charged step costs exactly one unit — true definitionally,
    since [toy_cost] is written as the indicator of [toy_charge]. *)
Lemma toy_exact_unit_pricing :
  exact_unit_pricing toy_gas_schedule.
Proof.
  intros s i.
  reflexivity.
Qed.

(** The toy schedule satisfies both honest-fee-market conditions, by
    the right-to-left direction of Main 1. So the class Main 1
    characterizes is inhabited, and the mains above are statements
    about real schedules, not about an empty set. *)
Theorem toy_gas_schedule_is_exact :
  quantitative_certification_floor toy_gas_schedule /\
  no_overcharge_for_commitments toy_gas_schedule.
Proof.
  apply (proj2 (gas_schedule_exactness toy_gas_schedule)).
  split.
  - exact toy_charge_is_cert_flip.
  - exact toy_exact_unit_pricing.
Qed.

(** * The Thiele VM itself is in the characterized class.

    The toy shows the class is inhabited; this shows it is inhabited by the
    machine the kernel is about. Price the VM's certification channel with
    the canonical unit schedule — charge exactly the steps that flip
    [vm_certified] false-to-true, one unit each — and the result is a
    [GasSchedule] satisfying both honest-fee-market conditions. This is the
    constructive bridge from the abstract fee-market characterization back
    to the kernel's concrete step semantics ([vm_apply]). *)

Definition thiele_commit_charge (s : VMState) (i : vm_instruction) : bool :=
  andb (negb s.(vm_certified)) (vm_apply s i).(vm_certified).

Definition thiele_commit_cost (s : VMState) (i : vm_instruction) : nat :=
  if thiele_commit_charge s i then 1 else 0.

Lemma thiele_commit_charged_costs :
  forall (s : VMState) (i : vm_instruction),
    thiele_commit_charge s i = true -> thiele_commit_cost s i >= 1.
Proof.
  intros s i Hcharged.
  unfold thiele_commit_cost.
  rewrite Hcharged.
  lia.
Qed.

Lemma thiele_commit_uncharged_free :
  forall (s : VMState) (i : vm_instruction),
    thiele_commit_charge s i = false -> thiele_commit_cost s i = 0.
Proof.
  intros s i Huncharged.
  unfold thiele_commit_cost.
  rewrite Huncharged.
  reflexivity.
Qed.

Definition thiele_vm_gas_schedule : GasSchedule :=
  {| lps_state  := VMState;
     lps_instr  := vm_instruction;
     lps_step   := vm_apply;
     lps_cost   := thiele_commit_cost;
     lps_cert   := fun s => s.(vm_certified);
     lps_charge := thiele_commit_charge;
     lps_charged_costs  := thiele_commit_charged_costs;
     lps_uncharged_free := thiele_commit_uncharged_free |}.

(** The VM schedule's charging predicate is the cert-flip predicate on the
    nose: both sides unfold to the same boolean. *)
Lemma thiele_charge_is_cert_flip :
  local_predicate_same thiele_vm_gas_schedule
    (cert_flip_local thiele_vm_gas_schedule)
    (lps_charge thiele_vm_gas_schedule).
Proof.
  split; intros s i H; exact H.
Qed.

Lemma thiele_exact_unit_pricing :
  exact_unit_pricing thiele_vm_gas_schedule.
Proof.
  intros s i.
  reflexivity.
Qed.

(** The kernel VM's certification channel, priced at the canonical unit
    schedule, satisfies both honest-fee-market conditions. The abstract
    characterization is about this machine too, not only about toys. *)
Theorem thiele_vm_commit_pricing_is_exact :
  quantitative_certification_floor thiele_vm_gas_schedule /\
  no_overcharge_for_commitments thiele_vm_gas_schedule.
Proof.
  apply (proj2 (gas_schedule_exactness thiele_vm_gas_schedule)).
  split.
  - exact thiele_charge_is_cert_flip.
  - exact thiele_exact_unit_pricing.
Qed.

(** The exact commitment price is a floor under the VM's real cost model:
    on every committing step, the unit price charged by
    [thiele_vm_gas_schedule] is at most the mu the instruction actually
    pays ([instruction_cost]). The inequality composes the schedule's
    definitional unit price with the kernel's A2 lemma
    [no_free_certification_certified]: mu covers the commitment floor —
    with room to spare, since mu also prices computation that commits
    nothing, which is exactly why mu itself is not the exact commitment
    pricer and the unit schedule above is. *)
Theorem thiele_unit_price_lower_bounds_mu :
  forall (s : VMState) (i : vm_instruction),
    thiele_commit_charge s i = true ->
    thiele_commit_cost s i <= instruction_cost i.
Proof.
  intros s i Hcharged.
  unfold thiele_commit_cost.
  rewrite Hcharged.
  unfold thiele_commit_charge in Hcharged.
  apply Bool.andb_true_iff in Hcharged.
  destruct Hcharged as [Hbefore Hafter].
  apply Bool.negb_true_iff in Hbefore.
  pose proof (no_free_certification_certified s i Hbefore Hafter).
  lia.
Qed.

Print Assumptions gas_schedule_exactness.
Print Assumptions undercharged_opcode_admits_free_commitment.
Print Assumptions undercharged_opcode_breaks_certification_floor.
Print Assumptions overcharge_breaks_exactness.
Print Assumptions toy_gas_schedule_is_exact.
Print Assumptions thiele_vm_commit_pricing_is_exact.
Print Assumptions thiele_unit_price_lower_bounds_mu.
