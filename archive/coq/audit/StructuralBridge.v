(* Structural lift bridge. No universality, effectivity, or old-cost preservation
   is assumed. The named counterexamples in Audit pin the limits of the claim. *)
From Coq Require Import List Bool Arith Lia.
Import ListNotations.
Require Minimal.ThieleComplete Minimal.NeutralComplete Minimal.SlicedEstablishment.
Module T := Minimal.ThieleComplete.
Module N := Minimal.NeutralComplete.
Module S := Minimal.SlicedEstablishment.

Section Bridge.
Variable M : T.machine.
Variable K : Type.
Variable event : K -> T.m_state M -> bool.

Definition base_view (s : N.nstate M) := fst (fst s).
Definition record_view (s : N.nstate M) := snd (fst s).
Definition embed (x : T.m_state M) : N.nstate M := (x,false,0).

(* No universal_base hypothesis: the very same neutral lift has this interface
   over ANY deterministic base, including a single fixed next-state rule. *)
Definition lift_as_sliced : S.SlicedInterface (N.nstate M) (T.m_state M)
    (T.m_move M) K.
Proof.
  refine {| S.view := base_view; S.verdict := record_view;
    S.horizontal := fun i s => N.nstep M K event s (N.NBase i);
    S.vertical := fun k s => N.nstep M K event s (N.NMark k);
    S.shadow_step := fun i x => T.m_step M x i;
    S.vertical_price := fun _ => 1 |}.
  - intro x; exists (embed x); reflexivity.
  - intros i [[x r] l]; reflexivity.
  - intros i [[x r] l]; reflexivity.
  - intros k [[x r] l]; reflexivity.
  - intros k [[x r] l] H; cbn in *; rewrite H; reflexivity.
  - intros; lia.
Defined.

Theorem projection_is_retraction : forall x, base_view (embed x) = x.
Proof. reflexivity. Qed.

Theorem full_horizontal_embedding : forall w x,
  T.run (N.nlift M K event) (map (@N.NBase M K) w) (embed x)
    = embed (T.run M w x).
Proof.
  induction w as [|i w IH]; intro x; [reflexivity|].
  change (T.run (N.nlift M K event) (map (@N.NBase M K) w)
    (embed (T.m_step M x i)) = embed (T.run M w (T.m_step M x i))).
  apply IH.
Qed.

Theorem mixed_projection_erases_only_marks : forall w x r l,
  base_view (T.run (N.nlift M K event) w (x,r,l)) =
    T.run M (N.nbases M K w) x.
Proof. intros; apply N.nlift_run_base. Qed.

Theorem exact_ledger : forall s i,
  snd (N.nstep M K event s i) = snd s + N.ncost M K i.
Proof. intros [[x r] l] [i|k]; cbn; lia. Qed.

Theorem raised_record_cannot_be_decoded_from_base : forall k x,
  event k x = true ->
  ~ exists decode : T.m_state M -> bool,
      forall s, decode (base_view s) = record_view s.
Proof.
  intros k x He [decode H].
  pose proof (H (embed x)) as H0.
  pose proof (H (N.nstep M K event (embed x) (N.NMark k))) as H1.
  cbn in H0,H1; rewrite He in H1; congruence.
Qed.

(* Infinite full-state room is forced by the exact ledger even if the
   Boolean record never changes: this source of infinity is accounting. *)
Theorem repeated_mark_states_distinct : forall k x r l n m,
  T.run (N.nlift M K event) (repeat (N.NMark k) n) (x,r,l) =
  T.run (N.nlift M K event) (repeat (N.NMark k) m) (x,r,l) -> n=m.
Proof.
  assert (Hcount : forall k n x r l,
    snd (T.run (N.nlift M K event) (repeat (N.NMark k) n) (x,r,l))=l+n).
  { intros k n; induction n; intros x r l; cbn; [lia|rewrite IHn; lia]. }
  intros k x r l n m H.
  pose proof (f_equal (@snd (T.m_state M * bool) nat) H) as E.
  rewrite !Hcount in E; lia.
Qed.
End Bridge.

Print Assumptions lift_as_sliced.
Print Assumptions projection_is_retraction.
Print Assumptions full_horizontal_embedding.
Print Assumptions mixed_projection_erases_only_marks.
Print Assumptions exact_ledger.
Print Assumptions raised_record_cannot_be_decoded_from_base.
Print Assumptions repeated_mark_states_distinct.
