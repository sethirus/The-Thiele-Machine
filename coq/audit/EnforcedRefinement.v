(* SCOPE NOTE: standalone proof scope.
   Generic all-action refinement theorem over a supplied relation.
   It proves safety for that interface, not unconditional native-machine
   enforcement. ConcreteClosureBridge instantiates it for the original host. *)

(* Simulation of selected guest programs and enforcement of every host action
   have different quantifiers. This is the sufficient all-host-action contract. *)
From Coq Require Import List.
Import ListNotations.

Section Refinement.
Context {Guest Host GuestMove HostMove : Type}.
Variable guest_step : Guest -> GuestMove -> Guest.
Variable host_step : Host -> HostMove -> Host.
Fixpoint guest_run (w : list GuestMove) (s : Guest) :=
  match w with [] => s | i::rest => guest_run rest (guest_step s i) end.
Fixpoint host_run (w : list HostMove) (s : Host) :=
  match w with [] => s | i::rest => host_run rest (host_step s i) end.

Variable related : Guest -> Host -> Prop.
Hypothesis every_host_step_refines : forall g h,
  related g h -> forall i,
  exists w, related (guest_run w g) (host_step h i).

Lemma guest_run_append : forall u v g,
  guest_run (u++v) g = guest_run v (guest_run u g).
Proof. induction u; intros; cbn; [reflexivity|apply IHu]. Qed.

Theorem every_host_trace_refines : forall w g h,
  related g h -> exists v, related (guest_run v g) (host_run w h).
Proof.
  induction w as [|i w IH]; intros g h H; cbn.
  - exists []; exact H.
  - destruct (every_host_step_refines g h H i) as [chunk Hchunk].
    destruct (IH _ _ Hchunk) as [tail Htail].
    exists (chunk++tail); rewrite guest_run_append; exact Htail.
Qed.

Variable guest_invariant : Guest -> Prop.
Variable host_invariant : Host -> Prop.
Hypothesis guest_preserves : forall g i,
  guest_invariant g -> guest_invariant (guest_step g i).
Hypothesis relation_transfers_invariant : forall g h,
  related g h -> guest_invariant g -> host_invariant h.

Lemma guest_trace_preserves : forall w g,
  guest_invariant g -> guest_invariant (guest_run w g).
Proof. induction w; intros; cbn; [assumption|apply IHw, guest_preserves; assumption]. Qed.

Theorem all_host_programs_preserve : forall w g h,
  related g h -> guest_invariant g -> host_invariant (host_run w h).
Proof.
  intros w g h Hr Hi.
  destruct (every_host_trace_refines w g h Hr) as [v Hv].
  eapply relation_transfers_invariant; [exact Hv|apply guest_trace_preserves; exact Hi].
Qed.

Variable guest_accepts : Guest -> bool.
Variable host_accepts : Host -> bool.
Hypothesis acceptance_reflects : forall g h,
  related g h -> host_accepts h = true -> guest_accepts g = true.

(* Evidence is a predicate on a GUEST trace: its earned chain, for example.
   Producing evidence about the HOST trace itself requires a further link. *)
Theorem accepted_host_run_has_guest_evidence : forall g h
    (evidence : list GuestMove -> Prop),
  related g h ->
  (forall v, guest_accepts (guest_run v g) = true -> evidence v) ->
  forall w, host_accepts (host_run w h) = true ->
  exists v, related (guest_run v g) (host_run w h) /\ evidence v.
Proof.
  intros g h evidence Hr He w Ha.
  destruct (every_host_trace_refines w g h Hr) as [v Hv].
  exists v; split; [exact Hv|apply He; eapply acceptance_reflects; eassumption].
Qed.
End Refinement.

Print Assumptions every_host_trace_refines.
Print Assumptions all_host_programs_preserve.
Print Assumptions accepted_host_run_has_guest_evidence.
