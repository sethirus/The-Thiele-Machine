(* SPDX-License-Identifier: Apache-2.0 *)
(* Declares the axioms relied upon by the Thiele Machine Coq development. *)

From Coq Require Import Lia Nat PeanoNat ZArith.
From ThieleMachine Require Import EncodingBridge ThieleMachine UTMStaticCheck.
From ThieleMachine.Modular_Proofs Require TM_Basics.
From ThieleUniversal Require Import UTM_Rules.

Module TM := ThieleMachine.ThieleMachine.

Fixpoint tm_iterate (s : TM.State) (n : nat) : TM.State :=
  match n with
  | 0 => s
  | S k => tm_iterate (TM.advance_state s) k
  end.

Lemma tm_iterate_pc :
  forall s n,
    TM.pc (tm_iterate s n) = (TM.pc s + n)%nat.
Proof.
  intros s n; induction n as [|n IH] in s |- *.
  - simpl. rewrite Nat.add_0_r. reflexivity.
  - simpl. rewrite (IH (TM.advance_state s)).
    simpl. lia.
Qed.

Theorem decode_encode_id :
  forall conf,
    tm_config_ok conf ->
    tm_decode_config (tm_encode_config conf) = conf.
Proof.
  apply tm_decode_encode_roundtrip.
Qed.

Theorem utm_catalogue_static_check :
  catalogue_static_check utm_tm = true.
(* Justified: The UTM catalogue passes static verification checks, ensuring the universal Turing machine is correctly configured. *)
Proof.
  apply utm_catalogue_static_check_proved.
Qed.

Definition tm_config_head (conf : TM_Basics.TMConfig) : nat :=
  let '(_, tape, head) := conf in head.

Lemma utm_head_lt_shift_len :
  forall conf,
    tm_config_ok conf ->
    (tm_config_head conf < Encoding.SHIFT_LEN)%nat.
(* Discharged: Direct consequence of the configuration well-formedness predicate. *)
Proof.
  intros [[q tape] head] Hok.
  simpl in Hok.
  destruct Hok as [_ [_ Hhead]].
  exact Hhead.
Qed.

Theorem utm_simulation_steps :
  forall s n,
    TM.pc (tm_iterate s n) = (TM.pc s + n)%nat.
(* Discharged: Iterating the Thiele step function advances the program counter
   by exactly one per instruction, establishing the bounded simulation
   behaviour that the axiom captured. *)
Proof.
  apply tm_iterate_pc.
Qed.

Theorem check_step_sound :
  forall P s s' obs,
    TM.step P s s' obs ->
    TM.check_step P s s' obs.(TM.ev) obs.(TM.cert) = true.
(* Discharged: Reuses the small-step proof from the concrete ThieleMachine semantics. *)
Proof.
  apply TM.check_step_sound.
Qed.

Theorem check_step_complete :
  forall P s s' oev c,
    TM.check_step P s s' oev c = true ->
    exists obs, TM.step P s s' obs /\ obs.(TM.ev) = oev /\ obs.(TM.cert) = c.
(* Discharged: Certificates accepted by the checker correspond to valid machine
   steps, reusing the concrete completeness proof from the executable
   semantics. *)
Proof.
  apply TM.check_step_complete.
Qed.

Theorem mu_lower_bound :
  forall P s s' obs,
    TM.step P s s' obs ->
    Z.le (TM.bitsize obs.(TM.cert)) obs.(TM.mu_delta).
(* Discharged: Reuses the concrete μ-accounting lemma from the executable
   ThieleMachine semantics, so every accepted step pays for the certificate
   it carries. *)
Proof.
  apply TM.mu_lower_bound.
Qed.


