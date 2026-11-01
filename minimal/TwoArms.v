(* SCOPE NOTE: standalone proof scope.
   Constructs commuting finite and infinite implementations of the exclusive-reset interface.
   The stated interface supplies the hypotheses; no concrete native-machine
   implementation is assumed. *)

From Coq Require Import List Arith Lia.
From Minimal Require Import CompleteHost.
Import ListNotations.

Inductive raw := End | A (i:nat) | B (i:nat).
Definition valid T s := match s with End=>True | A i=>i<T | B i=>i<=T end.
Definition carrier T := End :: map A (seq 0 T) ++ map B (seq 0 (S T)).
Definition F T s := match s with
  A i => if S i <? T then A (S i) else End | _=>s end.
Definition G T s := match s with
  B i => if S i <=? T then B (S i) else End | _=>s end.
Definition view s := match s with A 0=>1 | B 0=>2 | _=>0 end.
Definition starts := [A 0;B 0;B 1].
Definition rank T s := match s with End=>0 | A i=>T-i | B i=>S T-i end.
Fixpoint reach T t s := match t with
  0=>In s starts
  | S n=>In s starts \/ exists q, reach T n q /\ (s=F T q \/ s=G T q)
  end.

Theorem commute : forall T s, F T (G T s)=G T (F T s).
Proof.
  intros T s; destruct s; unfold F,G;
    repeat match goal with |-context[if ?b then _ else _]=>destruct b end; reflexivity.
Qed.
Theorem F_projects : forall T s,
  view (F T s)=if view s =? 2 then 2 else 0.
Proof.
  intros T s; destruct s as [|[|i]|[|i]]; unfold F,view; simpl;
    repeat match goal with |-context[if ?b then _ else _]=>destruct b end; reflexivity.
Qed.
Theorem G_projects : forall T s,
  view (G T s)=if view s =? 1 then 1 else 0.
Proof.
  intros T s; destruct s as [|[|i]|[|i]]; unfold G,view; simpl;
    repeat match goal with |-context[if ?b then _ else _]=>destruct b end; reflexivity.
Qed.
Theorem F_closed : forall T s, valid T s -> valid T (F T s).
Proof.
  intros T [|i|i] H; simpl in *; auto.
  unfold F; destruct (S i <? T) eqn:E; simpl; auto; apply Nat.ltb_lt; exact E.
Qed.
Theorem G_closed : forall T s, valid T s -> valid T (G T s).
Proof.
  intros T [|i|i] H; try exact H.
  change (valid T (if S i <=? T then B (S i) else End)).
  destruct (S i <=? T) eqn:E; simpl; auto; apply Nat.leb_le; exact E.
Qed.
Theorem carrier_exact : forall T s, In s (carrier T) <-> valid T s.
Proof.
  intros T s; change ((End=s \/ In s (map A (seq 0 T) ++ map B (seq 0 (S T)))) <-> valid T s).
  rewrite in_app_iff, !in_map_iff.
  split.
  - intros [H|[[i [H E]]|[i [H E]]]]; subst s; simpl; auto;
      apply in_seq in E; lia.
  - destruct s; simpl; intro H.
    + auto.
    + right; left; exists i; split; [reflexivity|apply in_seq; lia].
    + right; right; exists i; split; [reflexivity|].
      change (In i (seq 0 (S T))); apply in_seq; lia.
Qed.
Lemma append_nodup : forall (X:Type) (l r:list X),
  NoDup l -> NoDup r -> (forall s, In s l -> ~In s r) -> NoDup (l++r).
Proof.
  intros X l r Hl Hr Hd; induction Hl; simpl; auto; constructor.
  - rewrite in_app_iff; intros [H'|H']; [contradiction|eapply Hd; simpl; eauto].
  - apply IHHl; intros s Hs; apply Hd; simpl; auto.
Qed.
Theorem carrier_nodup : forall T, NoDup (carrier T).
Proof.
  intro T; unfold carrier; constructor.
  - rewrite in_app_iff; intros [E|E]; apply in_map_iff in E;
      destruct E as [i [E _]]; discriminate.
  - assert (NA:NoDup (map A (seq 0 T))).
    { apply nodup_map_on; [apply seq_NoDup|intros i j _ _ E; inversion E; reflexivity]. }
    assert (NB:NoDup (map B (seq 0 (S T)))).
    { apply nodup_map_on; [apply seq_NoDup|intros i j _ _ E; inversion E; reflexivity]. }
    apply append_nodup; auto.
    intros s H1 H2; apply in_map_iff in H1; apply in_map_iff in H2.
    destruct H1 as [i [E1 _]], H2 as [j [E2 _]]; subst s; discriminate.
Qed.
Theorem carrier_size : forall T, length (carrier T)=2*T+2.
Proof.
  intro T; change (S (length (map A (seq 0 T) ++ map B (seq 0 (S T))))=2*T+2).
  rewrite app_length,!map_length,!seq_length; lia.
Qed.

Theorem F_rank : forall T s, rank T s<=S (rank T (F T s)).
Proof.
  intros T [|i|i]; unfold F,rank; try lia.
  destruct (S i <? T) eqn:E; simpl; [apply Nat.ltb_lt in E|apply Nat.ltb_ge in E]; lia.
Qed.
Theorem G_rank : forall T s, rank T s<=S (rank T (G T s)).
Proof.
  intros T [|i|i]; unfold G,rank; try lia.
  destruct (S i <=? T) eqn:E; simpl; [apply Nat.leb_le in E|apply Nat.leb_gt in E];
    destruct i; simpl in *; lia.
Qed.
Lemma initial_valid_rank : forall T s, 1<=T -> In s starts -> valid T s /\ T<=rank T s.
Proof.
  intros T s HT H; unfold starts in H; simpl in H;
  destruct H as [H|[H|[H|H]]]; try contradiction; subst s; simpl; lia.
Qed.
Theorem reach_valid_rank : forall T t s, 1<=T -> reach T t s ->
  valid T s /\ T<=rank T s+t.
Proof.
  intros T t; induction t; intros s HT H.
  - destruct (initial_valid_rank T s HT H) as [V R]; split; [exact V|lia].
  - destruct H as [H|[q [H [E|E]]]].
    + destruct (initial_valid_rank T s HT H) as [V R]; split; [exact V|lia].
    + subst s; destruct (IHt q HT H) as [V R]; split; [apply F_closed;auto|].
      pose proof (F_rank T q); lia.
    + subst s; destruct (IHt q HT H) as [V R]; split; [apply G_closed;auto|].
      pose proof (G_rank T q); lia.
Qed.

Theorem F_injective_before_end : forall T x y,
  valid T x -> valid T y -> x<>End -> y<>End -> F T x=F T y -> x=y.
Proof.
  intros T x y Hx Hy Nx Ny E; destruct x as [|i|i],y as [|j|j];
    simpl in *; try contradiction;
    repeat match goal with H:context[if ?b then _ else _] |- _=>destruct b eqn:? end;
    try discriminate; try (inversion E; reflexivity).
  repeat match goal with H:(_ <? _)=false |- _=>apply Nat.ltb_ge in H end.
  f_equal; lia.
Qed.
Theorem G_injective_before_end : forall T x y,
  valid T x -> valid T y -> x<>End -> y<>End -> G T x=G T y -> x=y.
Proof.
  intros T x y Hx Hy Nx Ny E; destruct x as [|i|i],y as [|j|j];
    cbn [valid] in Hx,Hy; unfold G in E; try contradiction;
    repeat match goal with H:context[if ?b then _ else _] |- _=>destruct b eqn:? end;
    try discriminate; try (inversion E; reflexivity).
  repeat match goal with H:(_ <=? _)=false |- _=>apply Nat.leb_gt in H end.
  f_equal; lia.
Qed.
Theorem retains_through_horizon : forall T t x y,
  1<=T -> t<T -> reach T t x -> reach T t y ->
  (F T x=F T y -> x=y) /\ (G T x=G T y -> x=y).
Proof.
  intros T t x y HT Ht Hx Hy.
  destruct (reach_valid_rank T t x HT Hx) as [Vx Rx].
  destruct (reach_valid_rank T t y HT Hy) as [Vy Ry].
  assert (Nx:x<>End) by (intro E; subst x; simpl in Rx; lia).
  assert (Ny:y<>End) by (intro E; subst y; simpl in Ry; lia).
  split; intro E; [eapply F_injective_before_end|eapply G_injective_before_end]; eauto.
Qed.

Definition IF s := match s with A i=>A (S i) | _=>s end.
Definition IG s := match s with B i=>B (S i) | _=>s end.
Theorem infinite_commute : forall s, IF (IG s)=IG (IF s).
Proof. destruct s; reflexivity. Qed.
Theorem infinite_F_injective : forall x y, IF x=IF y -> x=y.
Proof. destruct x,y; simpl; intro E; inversion E; reflexivity. Qed.
Theorem infinite_G_injective : forall x y, IG x=IG y -> x=y.
Proof. destruct x,y; simpl; intro E; inversion E; reflexivity. Qed.
Theorem infinite_F_projects : forall s, view (IF s)=if view s =? 2 then 2 else 0.
Proof. destruct s as [|[|i]|[|i]]; reflexivity. Qed.
Theorem infinite_G_projects : forall s, view (IG s)=if view s =? 1 then 1 else 0.
Proof. destruct s as [|[|i]|[|i]]; reflexivity. Qed.
