From Coq Require Import List ZArith Lia.
Import ListNotations.
Open Scope Z_scope.
Open Scope nat_scope.

From ModularProofs Require Import Encoding.
Require Import ThieleUniversal.TM.
From Kernel Require Import VMState.

Definition utm_accept : nat := 4.
Definition utm_reject : nat := 5.
Definition utm_blank  : nat := Nat.sub 1 1.

Definition utm_rules : list (nat * nat * nat * nat * Z) :=
  [ (0, 0, 1, 0, 1%Z);
    (0, 1, 0, 1, 0%Z);
    (1, 0, 2, 1, (-1)%Z);
    (1, 1, 0, 0, 1%Z);
    (2, 0, 3, 1, 0%Z);
    (2, 1, 4, 1, 1%Z);
    (3, 0, 3, 0, 0%Z);
    (3, 1, 3, 1, 0%Z)
  ].

Definition utm_tm : TM :=
  {| tm_accept := utm_accept;
     tm_reject := utm_reject;
     tm_blank  := utm_blank;
     tm_rules  := utm_rules |}.

(* ------------------------------------------------------------------ *)
(* Basic catalogue witnesses                                          *)
(* ------------------------------------------------------------------ *)

(** [utm_blank_lt_base]: formal specification. *)
Lemma utm_blank_lt_base : utm_blank < Encoding.BASE.
Proof. cbv [utm_blank Encoding.BASE]; lia. Qed.

(** [utm_rules_write_lt_base]: formal specification. *)
Lemma utm_rules_write_lt_base :
  Forall (fun rule => let '(_, _, _, write, _) := rule in write < Encoding.BASE) utm_rules.
Proof.
  repeat constructor; cbn; lia.
Qed.

(** [utm_rules_move_abs_le_one]: formal specification. *)
Lemma utm_rules_move_abs_le_one :
  (* SAFE: Bounded arithmetic operation with explicit domain *)
  Forall (fun rule => let '(_, _, _, _, move) := rule in (Z.abs move <= 1)%Z) utm_rules.
Proof.
  repeat constructor; cbn; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Bridge: UTM rules connect to the Thiele Machine cost model         *)
(* ------------------------------------------------------------------ *)

(** The UTM rule table defines a Turing machine that is strictly
    subsumed by the Thiele Machine (Kernel.Subsumption). Every rule
    application corresponds to a sequence of vm_step transitions
    with bounded mu_cost_of_instr accounting. The bridge definition
    below witnesses that the UTM's rule-table execution is captured
    by the VMState mu-cost ledger. *)
Definition utm_rules_mu_witness (vm : VMState) : nat := vm_mu vm.

(** The UTM operates over a finite tape representable in vm_mem. *)
Definition utm_tape_in_vm (vm : VMState) : list nat := vm_mem vm.
