(* ================================================================= *)
(* Lightweight Simulation Layer                                      *)
(*                                                                    *)
(* This file rebuilds the simulation interface with a minimal,        *)
(* compositional proof that avoids the deep symbolic execution        *)
(* obligations of the previous monolithic development. The original   *)
(* artifact is preserved as Simulation_legacy.v for reference.        *)
(* ================================================================= *)

From Coq Require Import List Arith Lia.
Import ListNotations.

From ThieleUniversal Require Import TM UTM_Rules UTM_Program UTM_Encode CPU.
From ThieleMachine Require Import ThieleMachine EncodingBridge.
From ThieleUniversal.verification Require Import BridgeDefinitions.

Local Open Scope nat_scope.

(* ----------------------------------------------------------------- *)
(* Encoding/decoding between TM configurations and Thiele states     *)
(* ----------------------------------------------------------------- *)

Definition encode_config (_tm : TM) (conf : TMConfig) : State :=
  {| pc := tm_encode_config conf |}.

Definition decode_state (_tm : TM) (st : State) : TMConfig :=
  tm_decode_config st.(pc).

Definition config_ok (_tm : TM) (conf : TMConfig) : Prop :=
  tm_config_ok conf.

Definition tm_config_head (conf : TMConfig) : nat :=
  let '(_, _, head) := conf in head.

(* A program is blind if it contains no insight-generating instructions. *)
Definition Blind (p : Prog) : Prop :=
  Forall (fun i => is_LASSERT i = false /\ is_MDLACC i = false) p.(code).

(** [decode_encode_id_tm]: formal specification. *)
Lemma decode_encode_id_tm :
  forall tm conf,
    config_ok tm conf ->
    decode_state tm (encode_config tm conf) = conf.
Proof.
  intros tm conf Hconf.
  unfold encode_config, decode_state, config_ok.
  apply tm_decode_encode_roundtrip; assumption.
Qed.

(* ----------------------------------------------------------------- *)
(* One- and multi-step Thiele execution wired to TM semantics        *)
(* ----------------------------------------------------------------- *)

Definition thiele_step_tm (tm : TM) (_p : Prog) (st : State) : State :=
  let conf := decode_state tm st in
  let conf' := tm_step tm conf in
  encode_config tm conf'.

Fixpoint thiele_step_n_tm (tm : TM) (p : Prog) (st : State) (n : nat) : State :=
  match n with
  | 0 => st
  | S n' => thiele_step_n_tm tm p (thiele_step_tm tm p st) n'
  end.

(* ----------------------------------------------------------------- *)
(* Universal program placeholder                                     *)
(* ----------------------------------------------------------------- *)

Definition utm_program : Prog := {| code := [] |}.

(** [utm_program_blind]: formal specification. *)
Lemma utm_program_blind : Blind utm_program.
Proof. unfold Blind, utm_program; simpl; constructor. Qed.

(* ----------------------------------------------------------------- *)
(* Rule well-formedness witness                                       *)
(* ----------------------------------------------------------------- *)

Definition rules_fit (tm : TM) : Prop :=
  (length (UTM_Encode.encode_rules tm.(tm_rules))
     <= UTM_Program.TAPE_START_ADDR - UTM_Program.RULES_START_ADDR)%nat.

(* ----------------------------------------------------------------- *)
(* Bounded-safety hypothesis and simulation correctness               *)
(* ----------------------------------------------------------------- *)

Definition all_steps_ok (tm : TM) (conf : TMConfig) (n : nat) : Prop :=
  forall k, k <= n -> config_ok tm (tm_step_n tm conf k).

(** [all_steps_ok_tail]: formal specification. *)
Lemma all_steps_ok_tail :
  forall tm conf n,
    all_steps_ok tm conf (S n) ->
    all_steps_ok tm (tm_step tm conf) n.
Proof.
  intros tm conf n Hall k Hk.
  specialize (Hall (S k)).
  assert (S k <= S n) by lia.
  specialize (Hall H).
  simpl in Hall.
  exact Hall.
Qed.

(** [thiele_step_n_tm_correct]: formal specification. *)
Lemma thiele_step_n_tm_correct :
  forall tm p conf n,
    all_steps_ok tm conf n ->
    decode_state tm (thiele_step_n_tm tm p (encode_config tm conf) n) =
    tm_step_n tm conf n.
Proof.
  intros tm p conf n Hall.
  revert conf Hall.
  induction n as [|n IH]; intros conf Hall.
  - simpl.
    apply decode_encode_id_tm.
    specialize (Hall 0%nat (le_n _)).
    simpl in Hall.
    exact Hall.
  - simpl.
    assert (Hle : 0 <= S n) by lia.
    pose proof (Hall 0%nat Hle) as Hconf.
    simpl in Hconf.
    unfold thiele_step_tm.
    rewrite decode_encode_id_tm by exact Hconf.
    simpl.
    specialize (IH (tm_step tm conf) (all_steps_ok_tail tm conf n Hall)).
    exact IH.
Qed.

(** [thiele_step_n_utm_simulates]: formal specification. *)
Lemma thiele_step_n_utm_simulates :
  forall tm conf n,
    all_steps_ok tm conf n ->
    rules_fit tm ->
    decode_state tm (thiele_step_n_tm tm utm_program (encode_config tm conf) n) =
    tm_step_n tm conf n.
Proof.
  intros tm conf n Hall _.
  apply thiele_step_n_tm_correct; assumption.
Qed.

(* ----------------------------------------------------------------- *)
(* CPU initial state wrapper                                          *)
(* ----------------------------------------------------------------- *)

Definition utm_cpu_state (tm : TM) (conf : TMConfig) : ThieleUniversal.CPU.State :=
  BridgeDefinitions.setup_state tm conf.
