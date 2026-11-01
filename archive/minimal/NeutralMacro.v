(** NeutralMacro.v: thm:lift-macro (3)-(4) in neutral form, and
    the small machine's unconditional certificate. *)
From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Minimal.ThieleComplete.
Require Import Minimal.LiftMacro.
Require Minimal.EarnedCore.
Module E := Minimal.EarnedCore.
Require Import Minimal.NeutralComplete.

(* Every base by simulation lifts neutrally (grouped box + window event). *)
Theorem sim_base_lifts_neutrally : forall M0 (B : sim_base M0),
  neutral_complete (nlift (macro_machine M0) unit (win_event (macro_machine M0) (sim_to_macro_ub B))).
Proof. intros M0 B. apply every_base_lifts_neutrally. Qed.

(* The five-lever box: no universal base, yet its grouped box lifts neutrally. *)
Theorem fl_macro_lifts_neutrally :
  ~ inhabited (universal_base fl_box) /\
  neutral_complete (nlift (macro_machine fl_box) unit
                     (win_event (macro_machine fl_box) (sim_to_macro_ub fl_sim_base))).
Proof. split; [exact fl_no_universal_base | apply sim_base_lifts_neutrally]. Qed.

(* On the book's own Thiele-complete small machine, one fixed run raises the
   record from EVERY loaded start, for 3: CHECK Ge0 A; COMMIT Ge0 A; CERTIFY.
   So "every raise is a distinction" is false for Thiele-complete machines
   too; what excludes a one-move unconditional raise there is the count. *)
Theorem small_unconditional_certificate : forall a b,
  E.cert (E.run [E.CHECK (E.PGe 0) E.CA; E.COMMIT (E.PGe 0) E.CA; E.CERTIFY] (E.start a b)) = true /\
  E.mu (E.run [E.CHECK (E.PGe 0) E.CA; E.COMMIT (E.PGe 0) E.CA; E.CERTIFY] (E.start a b)) = 3.
Proof. intros a b. split; reflexivity. Qed.

Print Assumptions sim_base_lifts_neutrally.
Print Assumptions fl_macro_lifts_neutrally.
Print Assumptions small_unconditional_certificate.
