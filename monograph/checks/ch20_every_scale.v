(* SCOPE NOTE: standalone proof scope. A short check written beside the book: it states its own
   machine, prices and conditions as hypotheses and uses only the Coq standard library and two lemmas from minimal/, so it
   does not import the foundation chain. *)
(* Chapter twenty, every scale pays the same way, in its finite case: if the fine step merges nothing
   on finitely many fine states, and a coarse description follows it exactly, the coarse rule merges
   nothing either. So a coarse merge forces a fine merge (or, on fenced states, a step out of the fence,
   or endlessly many fine states, which this finite case leaves out).
   Built on Minimal.Recurrence.returns_to_start: a one-to-one step on finitely many states brings
   every run back to its start. *)
From Coq Require Import List Arith Lia.
Require Import Minimal.StepLaw Minimal.Recurrence.
Import ListNotations.

Section EveryScale.
  Variables X C : Type.
  Hypothesis eq_dec : forall a b : X, {a = b} + {a <> b}.
  Variable F : X -> X.
  Hypothesis inj : forall a b, F a = F b -> a = b.
  Variable all : list X.
  Hypothesis all_in : forall x, In x all.
  Variable pi : X -> C.                         (* the fence each fine state sits in *)
  Variable f : C -> C.                          (* the coarse rule *)
  Hypothesis follows : forall x, pi (F x) = f (pi x).

  Fixpoint iterc (n : nat) (s : C) : C := match n with 0 => s | S k => f (iterc k s) end.

  Lemma iterc_shift : forall n s, iterc (S n) s = iterc n (f s).
  Proof. induction n; intro s; simpl; [reflexivity | rewrite <- IHn; reflexivity]. Qed.

  Lemma pi_run : forall n x, pi (StepLaw.run X F x n) = iterc n (pi x).
  Proof. induction n; intro x; simpl; [reflexivity | rewrite follows, IHn; reflexivity]. Qed.

  Lemma run_plus : forall x m n, StepLaw.run X F x (m + n) = StepLaw.run X F (StepLaw.run X F x n) m.
  Proof. intros x m n. induction m; simpl; [reflexivity | rewrite IHm; reflexivity]. Qed.

  Lemma run_multiple : forall x p k, StepLaw.run X F x p = x -> StepLaw.run X F x (k * p) = x.
  Proof.
    intros x p k Hp. induction k as [|k IHk]; [reflexivity|].
    replace (S k * p) with (p + k * p) by lia.
    rewrite run_plus, IHk. exact Hp.
  Qed.

  Theorem coarse_merges_nothing : forall a b, f (pi a) = f (pi b) -> pi a = pi b.
  Proof.
    intros a b E.
    destruct (returns_to_start X eq_dec F inj all all_in a) as [pa [Ha Ra]].
    destruct (returns_to_start X eq_dec F inj all all_in b) as [pb [Hb Rb]].
    set (n := pb * pa).
    assert (An : StepLaw.run X F a n = a) by (apply run_multiple; exact Ra).
    assert (Bn : StepLaw.run X F b n = b).
    { unfold n. rewrite Nat.mul_comm. apply run_multiple; exact Rb. }
    assert (Pos : 0 < n) by (unfold n; nia).
    destruct n as [|m] eqn:En; [lia|].
    rewrite <- An, <- Bn, !pi_run, !iterc_shift, E. reflexivity.
  Qed.
End EveryScale.

(* Chapter twenty, the worst input, over exact rationals: if the K known inputs add to at least K times L,
   some input is at least L. With the average equal to the entropy produced on the even spread plus k ln K, and that
   at least zero by the second law (both assumed physics, named on the page), some input pays k ln K. *)
From Coq Require Import QArith Lqa ZArith.
Local Open Scope Q_scope.
Fixpoint qsum (l : list Q) : Q := match l with [] => 0 | x :: r => x + qsum r end.

Lemma below_all_sum_below : forall (l : list Q) (c : Q),
    l <> [] -> (forall x, In x l -> x < c) -> qsum l < c * inject_Z (Z.of_nat (length l)).
Proof.
  induction l as [|x r IH]; intros c Hne H; [congruence|].
  destruct r as [|y r'].
  - simpl. specialize (H x (or_introl eq_refl)). unfold inject_Z. simpl. lra.
  - assert (Hr : qsum (y :: r') < c * inject_Z (Z.of_nat (length (y :: r')))).
    { apply IH; [discriminate | intros z Hz; apply H; right; exact Hz]. }
    specialize (H x (or_introl eq_refl)).
    change (qsum (x :: y :: r')) with (x + qsum (y :: r')).
    replace (Z.of_nat (length (x :: y :: r'))) with (Z.of_nat (length (y :: r')) + 1)%Z
      by (simpl; lia).
    rewrite inject_Z_plus. unfold inject_Z at 2. lra.
Qed.

Theorem some_input_pays : forall (l : list Q) (L : Q),
    l <> [] -> L * inject_Z (Z.of_nat (length l)) <= qsum l -> exists x, In x l /\ L <= x.
Proof.
  intros l L Hne Hs.
  assert (D : forall x, {L <= x} + {x < L}) by (intro x; destruct (Qlt_le_dec x L); [right|left]; assumption).
  induction l as [|a r IH]; [congruence|].
  destruct (D a) as [Le | Lt]; [exists a; split; [left; reflexivity | exact Le]|].
  destruct (List.Exists_dec (fun x => L <= x) r (fun x => match D x with left p => left p | right q => right (Qlt_not_le _ _ q) end)) as [Ex | Nex].
  - apply Exists_exists in Ex as [x [Hx Lx]]. exists x. split; [right; exact Hx | exact Lx].
  - exfalso. assert (All : forall x, In x (a :: r) -> x < L).
    { intros x [<- | Hx]; [exact Lt|]. destruct (D x) as [Le|Lt']; [|exact Lt'].
      exfalso. apply Nex. apply Exists_exists. exists x. split; assumption. }
    pose proof (below_all_sum_below (a :: r) L Hne All). lra.
Qed.

Print Assumptions coarse_merges_nothing.
Print Assumptions some_input_pays.
