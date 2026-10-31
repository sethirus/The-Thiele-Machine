(* SCOPE NOTE: standalone proof scope.
   Generic finite-fuel observer theorem over a supplied commuting view.
   It applies to any transition system satisfying those hypotheses; no native
   machine or unrestricted controller is assumed. *)

(* A view-only adaptive controller cannot recover a hidden record. *)
From Coq Require Import List Bool Arith.

Section Adaptive.
Context {State Base Input Memory Record : Type}.
Variable view : State -> Base.
Variable horizontal : Input -> State -> State.
Variable shadow : Input -> Base -> Base.
Hypothesis projects : forall i s, view (horizontal i s) = shadow i (view s).
Variable choose : Memory -> Base -> option (Input * Memory).

Fixpoint probe (fuel : nat) (s : State) (mem : Memory) : State * Memory :=
  match fuel with
  | 0 => (s,mem)
  | S n => match choose mem (view s) with
    | None => (s,mem)
    | Some (i,next_mem) => probe n (horizontal i s) next_mem
    end
  end.
Definition visible (result : State * Memory) := (view (fst result),snd result).

Theorem adaptive_observer_stays_blind : forall fuel s t mem,
  view s = view t -> visible (probe fuel s mem) = visible (probe fuel t mem).
Proof.
  induction fuel as [|n IH]; intros s t mem H.
  - change ((view s,mem) = (view t,mem)); rewrite H; reflexivity.
  - cbn [probe]; rewrite <- H.
    destruct (choose mem (view s)) as [[i next_mem]|].
    + apply IH; rewrite !projects, H; reflexivity.
    + change ((view s,mem) = (view t,mem)); rewrite H; reflexivity.
Qed.

Theorem adaptive_decision_stays_equal : forall fuel s t mem
    (decide : Base * Memory -> bool),
  view s = view t ->
  decide (visible (probe fuel s mem)) = decide (visible (probe fuel t mem)).
Proof. intros; rewrite (adaptive_observer_stays_blind fuel s t mem); auto. Qed.

Variable record : State -> Record.
Hypothesis passive : forall i s, record (horizontal i s) = record s.

Theorem adaptive_probe_preserves_record : forall fuel s mem,
  record (fst (probe fuel s mem)) = record s.
Proof.
  induction fuel as [|n IH]; intros s mem; cbn; [reflexivity|].
  destruct (choose mem (view s)) as [[i next_mem]|]; cbn; [rewrite IH; apply passive|reflexivity].
Qed.

Theorem adaptive_probe_keeps_hidden_distinction : forall fuel s t mem,
  view s = view t -> record s <> record t ->
  visible (probe fuel s mem) = visible (probe fuel t mem) /\
  record (fst (probe fuel s mem)) <> record (fst (probe fuel t mem)).
Proof.
  intros fuel s t mem Hv Hr; split.
  - apply adaptive_observer_stays_blind; exact Hv.
  - rewrite !adaptive_probe_preserves_record; exact Hr.
Qed.
End Adaptive.

(* If the controller may read the hidden bit, it can choose a move that
   signals that bit through the visible workspace, despite passive moves. *)
Definition write_visible (i : bool) (s : bool * bool) := (i,snd s).
Definition privileged_control (s : bool * bool) := write_visible (snd s) s.
Theorem hidden_access_can_signal :
  (forall i s, fst (write_visible i s) = i /\ snd (write_visible i s) = snd s) /\
  fst (false,false) = fst (false,true) /\
  fst (privileged_control (false,false)) <> fst (privileged_control (false,true)).
Proof. split; [intros; split; reflexivity|split; [reflexivity|discriminate]]. Qed.

Print Assumptions adaptive_observer_stays_blind.
Print Assumptions adaptive_decision_stays_equal.
Print Assumptions adaptive_probe_preserves_record.
Print Assumptions adaptive_probe_keeps_hidden_distinction.
Print Assumptions hidden_access_can_signal.
