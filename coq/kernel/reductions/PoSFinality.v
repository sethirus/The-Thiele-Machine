(** PoSFinality: proof-of-stake finality against the certification-cost kernel.

    Casper-style finality gadgets (Buterin–Griffith 2017) name their central
    failure mode "nothing at stake": when finalizing costs a validator
    nothing, conflicting finalizations are free. This file instantiates that
    folk theorem against the kernel's abstract records.

    Negative direction: a finality gadget whose finalize step carries zero
    stake-at-risk is a [CostBearingSystem] realizing the
    [dishonest_forge_system] pattern — finalization flips from false to true
    at total cost 0, so by [free_forgery_violates_A2] no A2 field can be
    constructed for it. Nothing-at-stake IS free forgery, in the kernel's
    exact sense.

    Positive direction: a slashing-enforced gadget (every finalizing step
    risks stake >= 1) is a genuine [CertificationSystem], and the finality
    cost floor is [universal_nfi_any_substrate] instantiated: every run from
    unfinalized to finalized risks at least one unit of stake.

    FALSIFIER: exhibit a protocol whose known nothing-at-stake status
    contradicts the formal classification: a zero-stake-at-finalize gadget
    that still admits an A2 proof, or a slashing gadget (finalize
    risks >= 1) with a finalizing trace of total stake-at-risk 0. Coq accepts
    the construction if it exists; either breaks this file.

    This file does not model economic rationality, network timing, or
    validator collusion. It prices exactly one event: the finalization flip. *)

From Coq Require Import List Arith.PeanoNat Lia Bool.
Import ListNotations.

From Kernel Require Import UniversalCertificationCost HonestCostTracking.

Section PoSFinality.

(** The validator's local view of the chain is fully abstract.  It could be
    a fork-choice tree, an attestation pool, a block DAG — the theorems below
    never look inside it.  All the kernel prices is the finality flip. *)
Variable ValidatorView : Type.

(** The gadget's instruction set, reduced to the two moves finality theory
    actually distinguishes:

    - [PoSVote delta]: cast a vote, updating the local view by an arbitrary
      function [delta].  Votes accumulate evidence; they never finalize.
    - [PoSFinalize]: commit.  This is the irrevocable step — the one event
      whose price is in question. *)
Inductive pos_instr : Type :=
| PoSVote (delta : ValidatorView -> ValidatorView)
| PoSFinalize.

(** Gadget state: the validator's current view paired with the finality
    flag.  The flag is the certification bit of this file. *)
Definition pos_state : Type := (ValidatorView * bool)%type.

(** One step of the gadget.  A vote rewrites the view and leaves the flag
    alone; finalize sets the flag and leaves the view alone. *)
Definition pos_step (s : pos_state) (i : pos_instr) : pos_state :=
  match i with
  | PoSVote delta => (delta (fst s), snd s)
  | PoSFinalize   => (fst s, true)
  end.

(** The certification event under study: is this state finalized? *)
Definition pos_finalized : pos_state -> bool := snd.

(** Votes are cert-neutral: no [PoSVote] step changes the finality flag.
    This is what makes the A2 case analysis for the slashing gadget exact —
    the only instruction that can flip the flag is [PoSFinalize]. *)
Lemma vote_preserves_finalized :
  forall (s : pos_state) (delta : ValidatorView -> ValidatorView),
    pos_finalized (pos_step s (PoSVote delta)) = pos_finalized s.
Proof.
  reflexivity.
Qed.

(** ** Negative direction: nothing at stake.

    The gadget with stake-at-risk identically zero.  This is a perfectly
    good [CostBearingSystem] (the record without A2), because nothing in
    an unconstrained cost-bearing world stops a protocol from declaring
    finalization free.  The two theorems after it show what that declaration
    costs the protocol: membership in the honest class. *)
Definition nothing_at_stake_gadget : CostBearingSystem :=
  {| cb_state := pos_state;
     cb_instr := pos_instr;
     cb_step  := pos_step;
     cb_cost  := fun _ => 0;
     cb_cert  := pos_finalized |}.

(** [nothing_at_stake_free_finalization]: from any unfinalized state, the
    one-instruction trace [PoSFinalize] reaches a finalized state at total
    stake-at-risk 0.

    This is the nothing-at-stake attack in its smallest form, and it is the
    PoS instance of [dishonest_free_certification] from the kernel: a
    non-empty trace flipping cert false-to-true at total cost zero.  Note
    the witness is not exotic — it is the gadget's own finalize instruction,
    used exactly as designed.  The defect is in the price, not the path. *)
Theorem nothing_at_stake_free_finalization :
  forall s : pos_state,
    pos_finalized s = false ->
       cb_cert nothing_at_stake_gadget s = false
    /\ cb_cert nothing_at_stake_gadget
          (cb_run nothing_at_stake_gadget [PoSFinalize] s) = true
    /\ cb_total_cost nothing_at_stake_gadget [PoSFinalize] = 0.
Proof.
  intros s Hunfinal.
  repeat split.
  - exact Hunfinal.
Qed.

(** [nothing_at_stake_is_free_forgery]: the zero-stake gadget admits no A2
    field.  Concretely: the honesty law "every finalizing step risks stake
    at least 1" is refutable for [nothing_at_stake_gadget], so no
    [CertificationSystem] record can be built over its (step, cost, cert)
    data.  Nothing-at-stake and free forgery are the same defect, stated in
    two vocabularies.

    The quantifier [forall v : ValidatorView] supplies the one thing the
    refutation needs: an inhabitant of the state space.  (Over an empty
    view type the gadget has no states and the honesty law holds
    vacuously, so the witness view is genuinely load-bearing.)

    This is [free_forgery_violates_A2] applied at the unfinalized state
    [(v, false)] with instruction [PoSFinalize] — an instantiation of the
    kernel theorem, stated here so the PoS reading is on the record. *)
Theorem nothing_at_stake_is_free_forgery :
  forall v : ValidatorView,
    ~ (forall (s : cb_state nothing_at_stake_gadget)
              (i : cb_instr nothing_at_stake_gadget),
          cb_cert nothing_at_stake_gadget s = false ->
          cb_cert nothing_at_stake_gadget
                  (cb_step nothing_at_stake_gadget s i) = true ->
          cb_cost nothing_at_stake_gadget i >= 1).
Proof.
  intro v.
  apply (free_forgery_violates_A2
           nothing_at_stake_gadget (v, false) PoSFinalize);
    reflexivity.
Qed.

(** ** Positive direction: slashing.

    A slashing schedule is a cost function [stake_at_risk] on instructions,
    and the slashing condition is the single inequality
    [stake_at_risk PoSFinalize >= 1]: finalizing puts at least one unit of
    stake on the line.  That inequality is exactly A2 for this gadget,
    because [PoSFinalize] is the only instruction that can flip the flag. *)

(** A2 for the slashing gadget, discharged by case analysis on the
    instruction.  [PoSVote] never flips the finality flag (the cert value
    before and after the step is the same bit, so the false-to-true
    hypotheses are contradictory); [PoSFinalize] is covered by the slashing
    condition directly. *)
Lemma slashing_cert_costs :
  forall (stake_at_risk : pos_instr -> nat),
    stake_at_risk PoSFinalize >= 1 ->
    forall (s : pos_state) (i : pos_instr),
      pos_finalized s = false ->
      pos_finalized (pos_step s i) = true ->
      stake_at_risk i >= 1.
Proof.
  intros stake_at_risk Hslash s i Hbefore Hafter.
  destruct i as [delta|].
  - rewrite vote_preserves_finalized in Hafter.
    rewrite Hbefore in Hafter.
    discriminate.
  - exact Hslash.
Qed.

(** The slashing-enforced gadget as a [CertificationSystem].  The record's
    A2 field is not assumed: it is constructed from the slashing condition
    via [slashing_cert_costs].  A slashing gadget is an honest
    cost-tracking system in the kernel's exact sense — that is the whole
    content of this definition. *)
Definition slashing_gadget
           (stake_at_risk : pos_instr -> nat)
           (Hslash : stake_at_risk PoSFinalize >= 1) : CertificationSystem :=
  {| cs_state := pos_state;
     cs_instr := pos_instr;
     cs_step  := pos_step;
     cs_cost  := stake_at_risk;
     cs_cert  := pos_finalized;
     cs_cert_costs := slashing_cert_costs stake_at_risk Hslash |}.

(** [slashing_finality_floor]: under any slashing schedule, every trace
    that takes any state from unfinalized to finalized carries total
    stake-at-risk at least 1.

    No trace shape is assumed: votes may rewrite the view arbitrarily, the
    finalize step may come anywhere in the trace, the trace may finalize
    and keep going.  The floor holds because the trace must contain a
    flag-flipping step somewhere, and slashing prices that step.

    This is [universal_nfi_any_substrate] instantiated at
    [slashing_gadget] — the proof is a single application of the kernel
    theorem, and the doc comment says so.  The work specific to this file
    was already done in [slashing_cert_costs]: showing that the slashing
    condition IS the A2 field for this instruction set. *)
Theorem slashing_finality_floor :
  forall (stake_at_risk : pos_instr -> nat)
         (Hslash : stake_at_risk PoSFinalize >= 1)
         (trace : list pos_instr)
         (s0 : pos_state),
    pos_finalized s0 = false ->
    pos_finalized
      (cs_run (slashing_gadget stake_at_risk Hslash) trace s0) = true ->
    cs_total_cost (slashing_gadget stake_at_risk Hslash) trace >= 1.
Proof.
  intros stake_at_risk Hslash trace s0 Hbefore Hafter.
  exact (universal_nfi_any_substrate
           (slashing_gadget stake_at_risk Hslash) trace s0 Hbefore Hafter).
Qed.

End PoSFinality.

Print Assumptions nothing_at_stake_free_finalization.
Print Assumptions nothing_at_stake_is_free_forgery.
Print Assumptions slashing_finality_floor.
