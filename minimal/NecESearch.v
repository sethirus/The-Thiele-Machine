(** NecESearch.v: the search through n bits and the time tax, at their
    limits.

    The book's Theorem "A search through n bits" assumes 1 <= k <= 16, and
    "The time tax" speaks of programs of two-counter instructions. This
    file shows:

    - k >= 1 is needed: with no question the program never certifies,
      from any world [nec_e_search_needs_a_question].
    - The cap of 16 CHECKs before the CERTIFY is attained: a run from a
      clean start asks exactly 16 questions before its only CERTIFY and
      raises the record [nec_e_questions_cap_tight]. (17 never certifies:
      ent2_questions_cap, ent2_no_search_past_16.)
    - "Two-counter instructions" (no record move) is needed for the time
      tax: one CHECK decides "A >= m" in one move, from the program
      counter, at ledger 1, for every m
      [nec_e_time_tax_one_paid_move, nec_e_time_tax_free_needed].

    Dependencies: EarnedCore.v, EarnedMulti.v, MultiThiele2.v,
    BitSearch2.v, BitSearchMember2.v, TimeTax2.v. No axioms.             *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Minimal.ThieleComplete Minimal.EntitlementSmall Minimal.MultiThiele2
  Minimal.BitSearch2 Minimal.BitSearchMember2 Minimal.TimeTax2.
Require Minimal.EarnedCore.
Require Minimal.EarnedMulti.
Module E := Minimal.EarnedCore.
Module M := Minimal.EarnedMulti.

Local Notation mrun := (M.run E.prop_eqb E.eval).

(* ================================================================= *)
(* 1. The search needs at least one question.                          *)
(* ================================================================= *)

(* With no question the program is COMMIT, CERTIFY: the COMMIT finds no
   fact and traps, so no world certifies. *)
Theorem nec_e_search_needs_a_question : forall v,
  M.cert (mrun (ent2_qtrace []) (ent2_world v)) = false.
Proof. intro v. reflexivity. Qed.

(* ================================================================= *)
(* 2. The cap of 16 is attained.                                       *)
(* ================================================================= *)

Definition nec_e_ans16 : list bool := repeat false 16.

Definition nec_e_pre16 : list (@M.instr E.prop) :=
  ent2_checks nec_e_ans16 0 ++ [M.COMMIT (ent2_prop false) 0].

(* A run from a clean start that raises the record with exactly 16 CHECKs
   before its only CERTIFY. *)
Theorem nec_e_questions_cap_tight :
  M.clean_start (ent2_world nec_e_ans16) /\
  M.cert (mrun (ent2_qtrace nec_e_ans16) (ent2_world nec_e_ans16)) = true /\
  ent2_qtrace nec_e_ans16 = nec_e_pre16 ++ [M.CERTIFY] /\
  ~ In M.CERTIFY nec_e_pre16 /\
  ent2_count_checks nec_e_pre16 = 16.
Proof.
  split; [apply M.multi_start_clean |].
  split; [vm_compute; reflexivity |].
  split; [vm_compute; reflexivity |].
  split; [vm_compute; intro H; repeat (destruct H as [H | H]; [discriminate H |]); exact H |].
  vm_compute. reflexivity.
Qed.

(* ================================================================= *)
(* 3. The time tax needs the free fragment.                            *)
(* ================================================================= *)

(* One CHECK of "A >= m" decides it in one move: the program counter is 2
   after a passing CHECK and stays 1 after a failing one (the trap). The
   ledger is 1. *)
Theorem nec_e_time_tax_one_paid_move : forall m,
  exists (P : list E.instr) (f : nat * nat -> bool),
    length P = 1 /\
    (forall a b, f (E.pc (E.core_of (E.run_prog 1 P (E.start a b))),
                    E.cb (E.core_of (E.run_prog 1 P (E.start a b)))) = Nat.leb m a) /\
    (forall a b, E.mu (E.run_prog 1 P (E.start a b)) = 1).
Proof.
  intro m. exists [E.CHECK (E.PGe m) E.CA], (fun x => Nat.eqb (fst x) 2).
  split; [reflexivity |]. split.
  - intros a b. simpl. unfold E.step, E.next_instr, E.exec, E.cexec, E.check_ok. simpl.
    destruct (Nat.leb m a); reflexivity.
  - intros a b. reflexivity.
Qed.

(* So the premise "free" of the time tax carries the weight: for every
   m >= 2, no free program of fewer than m moves decides A >= m, and one
   paid move does. *)
Theorem nec_e_time_tax_free_needed : forall m, 2 <= m ->
  (forall Mp n, n < m -> ~ ent2_machine_decides Mp n m) /\
  (exists (P : list E.instr) (f : nat * nat -> bool),
    length P = 1 /\
    (forall a b, f (E.pc (E.core_of (E.run_prog 1 P (E.start a b))),
                    E.cb (E.core_of (E.run_prog 1 P (E.start a b)))) = Nat.leb m a) /\
    (forall a b, E.mu (E.run_prog 1 P (E.start a b)) = 1)).
Proof.
  intros m _. split; [exact (fun Mp n H => ent2_machine_free_cannot_decide Mp n m H) |].
  apply nec_e_time_tax_one_paid_move.
Qed.

Print Assumptions nec_e_search_needs_a_question.
Print Assumptions nec_e_questions_cap_tight.
Print Assumptions nec_e_time_tax_one_paid_move.
Print Assumptions nec_e_time_tax_free_needed.
