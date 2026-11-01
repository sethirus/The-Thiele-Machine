(* SCOPE NOTE: standalone proof scope.
   Tests whether an orbit-prefix statistic can be represented by the current state alone.
   The stated interface supplies the hypotheses; no concrete native-machine
   implementation is assumed. *)

From Coq Require Import List Arith Lia Bool.
From Minimal Require Import CompleteHost StructuralMeter.
Import ListNotations.

(* Even allowing zero idle charges does not turn an arbitrary prefix
   statistic into a function of the CURRENT state. The first and second
   visits to true have different observed collision counts. *)
Theorem reset_prefix_meter_not_a_state_function :
  ~exists mu : bool -> nat, forall L,
    mu (iter (fun _ : bool => true) L false)=
    structural_mu Bool.bool_dec (fun _ : bool => true) false L.
Proof.
  intros [mu H]; pose proof (H 1) as H1; pose proof (H 2) as H2.
  change (mu true=1) in H1; change (mu true=2) in H2; lia.
Qed.
Theorem reset_prefix_merge_not_a_state_function :
  ~exists m : bool -> nat, forall L,
    m (iter (fun _ : bool => true) L false)=
    merges Bool.bool_dec (fun _ : bool => true) false L.
Proof.
  intros [m H]; pose proof (H 1) as H1; pose proof (H 2) as H2.
  change (m true=0) in H1; change (m true=1) in H2; lia.
Qed.

Section Clock.
  Context {X : Type}.
  Variable eq_dec : forall a b : X, {a=b}+{a<>b}.
  Variable F : X -> X.
  Variable entry : X.
  Definition clock_state := (X*nat)%type.
  Definition clock_step (s : clock_state) := (F (fst s),S (snd s)).
  Definition clock_eq_dec : forall a b : clock_state, {a=b}+{a<>b}.
  Proof. decide equality; auto using Nat.eq_dec. Defined.

  Theorem clock_projects : forall s, fst (clock_step s)=F (fst s).
  Proof. reflexivity. Qed.
  Theorem clock_orbit : forall n,
    iter clock_step n (entry,0)=(iter F n entry,n).
  Proof. induction n; [reflexivity|simpl; rewrite IHn; reflexivity]. Qed.
  Theorem clock_orbit_distinct : forall i j,
    iter clock_step i (entry,0)=iter clock_step j (entry,0) -> i=j.
  Proof.
    intros i j H; rewrite !clock_orbit in H; apply (f_equal snd) in H; exact H.
  Qed.
  Theorem clock_run_retains : forall L, retains clock_step (entry,0) L.
  Proof.
    intros L i j Hi Hj H; rewrite !clock_orbit in *.
    apply (f_equal snd) in H; simpl in H.
    assert (i=j) by lia; subst; reflexivity.
  Qed.
  Theorem clock_run_no_observed_merges : forall L,
    merges clock_eq_dec clock_step (entry,0) L=0.
  Proof. intro L; apply zero_merges_iff_retains,clock_run_retains. Qed.
  Theorem clock_run_room : forall L, room clock_eq_dec clock_step (entry,0) L=L.
  Proof.
    intro L; apply zero_merges_exact_room with (H:=fun s=>0<snd s).
    - simpl; lia.
    - simpl; lia.
    - intros [s n] H; simpl in *; lia.
    - apply clock_run_no_observed_merges.
  Qed.
  Theorem clock_full_meter : forall L,
    structural_mu clock_eq_dec clock_step (entry,0) L=L.
  Proof.
    intro L; unfold structural_mu; rewrite clock_run_no_observed_merges,clock_run_room; reflexivity.
  Qed.
  Definition projected_meter (s : clock_state) := structural_mu eq_dec F entry (snd s).
  Theorem clock_can_represent_original_meter : forall L,
    projected_meter (iter clock_step L (entry,0))=structural_mu eq_dec F entry L.
  Proof. intro L; rewrite clock_orbit; reflexivity. Qed.
End Clock.

(* The original reset meter saturates at 2; the clock-extended FULL graph
   meter is 3 at this horizon. Both statements are about the same projection. *)
Theorem instrumentation_changes_full_graph_meter :
  structural_mu Bool.bool_dec (fun _ : bool=>true) false 3=2 /\
  structural_mu (clock_eq_dec Bool.bool_dec)
    (clock_step (fun _ : bool=>true)) (false,0) 3=3.
Proof. split; [reflexivity|apply clock_full_meter]. Qed.
