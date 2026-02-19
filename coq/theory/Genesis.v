(* Genesis.v *)
(* The Final Witness: coherence ≃ Thiele architecture *)
(* Audit by: coqc Genesis.v  — silence means verified. *)

Set Implicit Arguments.
Generalizable All Variables.

Section Universal_Ouroboros.
  Variable S : Type.

  (* Process and auditor. *)
  Definition Process  := S -> S.
  Definition Auditor  := S -> S -> Prop.

  (* A "coherent process": step plus an admissibility proof of its own step. *)
  Record Proc := {
    step    : Process;
    ok      : Auditor;
    ok_step : forall s, ok s (step s)
  }.

  (* Thiele machine (proposer + auditor). *)
  Record Thiele := {
    proposer : Process;
    auditor  : Auditor
  }.

  (* Commit relation: a step occurs exactly when the auditor accepts the proposer’s output. *)
  Inductive ThieleStep (T : Thiele) : S -> S -> Prop :=
  | T_commit s : auditor T s (proposer T s) -> ThieleStep T s (proposer T s).

  (* Every coherent process induces a Thiele machine that realises its step. *)
  Definition proc_to_thiele (P : Proc) : Thiele :=
    {| proposer := step P; auditor := ok P |}.

  (** [proc_realises_thiele]: formal specification. *)
  Theorem proc_realises_thiele (P : Proc) :
    forall s, ThieleStep (proc_to_thiele P) s (step P s).
  Proof. intro s. constructor. apply ok_step. Qed.

  (* Conversely, any Thiele with an admissible proposer yields a coherent process. *)
  Definition thiele_to_proc (T : Thiele)
    (H : forall s, auditor T s (proposer T s)) : Proc :=
    {| step := proposer T; ok := auditor T; ok_step := H |}.

  (* Round-trip identities (isomorphism). *)
  (** [to_from_id]: formal specification. *)
  Theorem to_from_id (P : Proc) :
    thiele_to_proc (proc_to_thiele P) (ok_step P) = P.
  Proof. destruct P; reflexivity. Qed.

  (** [from_to_id]: formal specification. *)
  Theorem from_to_id (T : Thiele) (H : forall s, auditor T s (proposer T s)) :
    proc_to_thiele (thiele_to_proc T H) = T.
  Proof. destruct T; reflexivity. Qed.

End Universal_Ouroboros.

(* Q.E.D. *)
