(** SCOPE NOTE: standalone proof scope. These narrow real-system
    countermodels intentionally test information loss without claiming formal
    translations into a Thiele machine.

    Top-five candidate models.  Each captures a narrow
    information-loss or durability condition identified by a real spec. *)

From Coq Require Import Bool Arith.PeanoNat.

Record CTClientState := {
  ct_local_sth : nat;
  ct_world_consistent : bool
}.
Definition ct_local_view (s : CTClientState) : nat := ct_local_sth s.
Definition ct_local_view_cannot_decide_global_consistency : Prop :=
  ~ exists decide : nat -> bool,
      forall s, decide (ct_local_view s) = ct_world_consistent s.

Record TPMSelectionInput := {
  signed_selection : nat;
  supplied_selection : nat;
  composite_digest_matches : bool
}.
Definition incomplete_quote_check (s : TPMSelectionInput) : bool :=
  composite_digest_matches s.
Definition incomplete_quote_check_accepts_selection_mismatch : Prop :=
  exists s, incomplete_quote_check s = true /\
            signed_selection s <> supplied_selection s.

Record WeakSubjectiveState := {
  ws_local_suffix : nat;
  ws_trusted_anchor : bool
}.
Definition ws_suffix_view (s : WeakSubjectiveState) : nat := ws_local_suffix s.
Definition suffix_cannot_decide_trusted_anchor : Prop :=
  ~ exists decide : nat -> bool,
      forall s, decide (ws_suffix_view s) = ws_trusted_anchor s.

Record WALState := {
  wal_client_ack : bool;
  wal_commit_record_durable : bool
}.
Definition crash_recovers_commit (s : WALState) : bool :=
  wal_commit_record_durable s.
Definition ack_without_durable_commit_can_be_lost : Prop :=
  exists s, wal_client_ack s = true /\ crash_recovers_commit s = false.

Record AuditState := {
  audit_current_local_log : bool;
  audit_event_occurred : bool
}.
Definition audit_local_view (s : AuditState) : bool := audit_current_local_log s.
Definition current_local_log_cannot_decide_history : Prop :=
  ~ exists decide : bool -> bool,
      forall s, decide (audit_local_view s) = audit_event_occurred s.
