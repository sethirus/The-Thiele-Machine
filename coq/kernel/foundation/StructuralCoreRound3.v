(** StructuralCoreRound3: uniqueness up to the price schedule.

    Adequacy in [StructuralCore] and [StructuralCoreRound2] puts a floor on
    the price of certifying (A2), while their sameness relations compare
    charges exactly. A machine that bills one extra unit per step is
    adequate and not the same ([StructuralUniqueness]), yet it is the same
    machine with a different price list. This file compares machines modulo
    the schedule: charges are not compared, and every machine in play
    carries a monotone ledger that satisfies A2. The claim it states is
    "one structure, many price lists."

    The record must be tied to the computation, in two strengths.

    - [HonestExtension3a]: the record is some reading of the Thiele state
      the cover assigns, the same reading at every state ([record_tied]).
      A record that is not a reading of the computation is not a record of
      it.
    - [HonestExtension3b]: the record is the Thiele core's own certification
      reading, read through the cover.

    Structure is observed through the entry condition's own cover: the
    sameness relation may only relate a state to the Thiele state the cover
    assigns it. So the structure of the Thiele VM is taken as given, since
    every machine admitted runs the VM step for step. A sameness relation
    that watched only the record light and halting would say little, since
    a universal machine can reproduce almost any pattern of lights. *)

From Coq Require Import Arith.PeanoNat.
From Kernel Require Import StructuralCore StructuralCoreRound2.

(** The record is some reading of the Thiele state the cover assigns. *)
Definition record_tied (M : RCM) (C : ComputationalCover M ThieleCore) : Prop :=
  exists g : rc_state ThieleCore -> bool,
    forall m, rc_cert M m = g (cover_state M ThieleCore C m).

(** The record is the Thiele core's own certification reading, through the
    cover. *)
Definition record_is_certification (M : RCM) (C : ComputationalCover M ThieleCore)
  : Prop :=
  forall m, rc_cert M m = rc_cert ThieleCore (cover_state M ThieleCore C m).

(** A price schedule in play: a monotone ledger satisfying A2. *)
Definition priced (M : RCM) : Prop := ledger_carried M /\ rc_a2 M.

Definition HonestExtension3a (M : RCM) (C : ComputationalCover M ThieleCore)
  : Prop :=
  record_tied M C /\ priced M /\ record_permanent M /\ reachable_record_write M.

Definition HonestExtension3b (M : RCM) (C : ComputationalCover M ThieleCore)
  : Prop :=
  record_is_certification M C /\ priced M /\ record_permanent M /\
  reachable_record_write M.

(** Sameness modulo the schedule, observed through the cover: states are
    related only to the Thiele state the cover assigns; related states agree
    on the record light and on halting and step to related states; starting
    states are covered in both directions. Charges are not compared. Both
    sides carry an A2 schedule. *)
Definition equiv_mod_schedule_via (M : RCM) (C : ComputationalCover M ThieleCore)
  : Prop :=
  priced M /\ priced ThieleCore /\
  exists R : rc_state M -> rc_state ThieleCore -> Prop,
    (forall m t, R m t -> cover_state M ThieleCore C m = t) /\
    (forall m, rc_init M m -> exists t, rc_init ThieleCore t /\ R m t) /\
    (forall t, rc_init ThieleCore t -> exists m, rc_init M m /\ R m t) /\
    (forall m t, R m t ->
       rc_cert M m = rc_cert ThieleCore t /\
       (rc_halted M m <-> rc_halted ThieleCore t) /\
       R (rc_next M m) (rc_next ThieleCore t)).

Definition uniqueness_round3a : Prop :=
  forall M C, HonestExtension3a M C -> equiv_mod_schedule_via M C.

Definition uniqueness_round3b : Prop :=
  forall M C, HonestExtension3b M C -> equiv_mod_schedule_via M C.
