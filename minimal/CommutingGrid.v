(* SCOPE NOTE: standalone proof scope.
   Constructs a commuting grid of hidden states for the two-coordinate reset interface.
   The stated interface supplies the hypotheses; no concrete native-machine
   implementation is assumed. *)

From Coq Require Import List Arith Lia.
Import ListNotations.

Inductive state := Blank | Grid (x y : nat).
Definition left (s : state) :=
  match s with Blank => Blank | Grid x y => Grid (S x) y end.
Definition right (s : state) :=
  match s with Blank => Blank | Grid x y => Grid x (S y) end.
Definition view (s : state) : bool * bool :=
  match s with Blank => (false,false)
  | Grid x y => (Nat.eqb x 0, Nat.eqb y 0) end.
Definition initial := [Blank; Grid 0 0; Grid 1 0; Grid 0 1].
Fixpoint reachable (t : nat) (s : state) : Prop :=
  match t with
  | 0 => In s initial
  | S n => In s initial \/ exists a, reachable n a /\ (s=left a \/ s=right a)
  end.

Theorem steps_commute : forall s, left (right s)=right (left s).
Proof. destruct s; reflexivity. Qed.
Theorem left_injective : forall a b, left a=left b -> a=b.
Proof. destruct a,b; simpl; intro H; inversion H; reflexivity. Qed.
Theorem right_injective : forall a b, right a=right b -> a=b.
Proof. destruct a,b; simpl; intro H; inversion H; reflexivity. Qed.
Theorem left_projects : forall s, view (left s)=(false,snd (view s)).
Proof. destruct s; reflexivity. Qed.
Theorem right_projects : forall s, view (right s)=(fst (view s),false).
Proof. destruct s; reflexivity. Qed.

Lemma initial_grid : forall x y, In (Grid x y) initial <-> x+y<=1.
Proof.
  intros x y; unfold initial; simpl; split.
  - intros [H|[H|[H|[H|H]]]]; try discriminate; try contradiction;
      inversion H; lia.
  - intro H; destruct x as [|[|x]], y as [|[|y]]; simpl in *;
      try lia; auto.
Qed.

Theorem reachable_exact : forall t s, reachable t s <->
  match s with Blank => True | Grid x y => x+y<=S t end.
Proof.
  induction t as [|t IH]; intro s.
  - destruct s; simpl; [unfold initial; simpl; tauto|apply initial_grid].
  - destruct s as [|x y].
    + simpl; unfold initial; simpl; tauto.
    + change ((In (Grid x y) initial \/
        exists a, reachable t a /\ (Grid x y=left a \/ Grid x y=right a))
        <-> x+y<=S (S t)).
      split.
      * intros [H|[a [Ha [H|H]]]].
        -- apply initial_grid in H; lia.
        -- destruct a; simpl in H; [discriminate|].
           inversion H; subst; apply IH in Ha; simpl in Ha; lia.
        -- destruct a; simpl in H; [discriminate|].
           inversion H; subst; apply IH in Ha; simpl in Ha; lia.
      * intro H; destruct x as [|x].
        -- destruct y as [|y].
           ++ left; apply initial_grid; lia.
           ++ right; exists (Grid 0 y); split; [apply IH; simpl; lia|right; reflexivity].
        -- right; exists (Grid x y); split; [apply IH; simpl; lia|left; reflexivity].
Qed.

Definition diagonal n := map (fun x => Grid x (n-x)) (seq 0 (S n)).
Fixpoint triangle n :=
  match n with 0 => diagonal 0 | S m => diagonal (S m) ++ triangle m end.
Definition prefix t := Blank :: triangle (S t).

Lemma diagonal_exact : forall n s, In s (diagonal n) <->
  exists x y, s=Grid x y /\ x+y=n.
Proof.
  intros n s; unfold diagonal; rewrite in_map_iff; split.
  - intros [x [E H]]; apply in_seq in H; exists x,(n-x); split; [symmetry; exact E|lia].
  - intros [x [y [E H]]]; subst s; exists x; split.
    + f_equal; lia.
    + apply in_seq; lia.
Qed.
Lemma triangle_exact : forall n s, In s (triangle n) <->
  exists x y, s=Grid x y /\ x+y<=n.
Proof.
  induction n as [|n IH]; intro s.
  - change (In s (diagonal 0) <-> exists x y, s=Grid x y /\ x+y<=0).
    rewrite diagonal_exact; split; intros [x [y [E H]]];
      exists x,y; split; auto; lia.
  - change (In s (diagonal (S n) ++ triangle n) <-> exists x y, s=Grid x y /\ x+y<=S n).
    rewrite in_app_iff, diagonal_exact, IH; split.
    + intros [[x [y [E H]]]|[x [y [E H]]]]; exists x,y; split; auto; lia.
    + intros [x [y [E H]]]; destruct (Nat.eq_dec (x+y) (S n)).
      * left; exists x,y; auto.
      * right; exists x,y; split; auto; lia.
Qed.
Theorem prefix_exact : forall t s, In s (prefix t) <-> reachable t s.
Proof.
  intros t s; rewrite reachable_exact; unfold prefix.
  change ((Blank=s \/ In s (triangle (S t))) <->
    match s with Blank=>True | Grid x y=>x+y<=S t end).
  rewrite triangle_exact; destruct s.
  - tauto.
  - split.
    + intros [H|[a [b [H E]]]]; [discriminate|inversion H; subst; assumption].
    + intro H; right; exists x,y; auto.
Qed.

Lemma map_injective_nodup : forall (A B:Type) (f:A->B) l,
  (forall x y, f x=f y -> x=y) -> NoDup l -> NoDup (map f l).
Proof.
  intros A B f l Hinj H; induction H; simpl; constructor; auto.
  intro E; apply in_map_iff in E; destruct E as [y [E Hy]].
  apply H; apply Hinj in E; subst; exact Hy.
Qed.
Lemma diagonal_nodup : forall n, NoDup (diagonal n).
Proof.
  intro n; unfold diagonal; apply map_injective_nodup.
  - intros x y H; inversion H; reflexivity.
  - apply seq_NoDup.
Qed.
Lemma append_disjoint_nodup : forall (A:Type) (l r:list A),
  NoDup l -> NoDup r -> (forall x, In x l -> ~ In x r) -> NoDup (l++r).
Proof.
  intros A l r Hl Hr Hd; induction Hl; simpl; auto.
  constructor.
  - rewrite in_app_iff; intros [H'|H']; [contradiction|eapply Hd; simpl; eauto].
  - apply IHHl; intros y Hy; apply Hd; simpl; auto.
Qed.
Lemma triangle_nodup : forall n, NoDup (triangle n).
Proof.
  induction n; change (NoDup (diagonal 0)) || change (NoDup (diagonal (S n) ++ triangle n)).
  - apply diagonal_nodup.
  -
  apply append_disjoint_nodup; auto using diagonal_nodup.
  intros s H1 H2; apply diagonal_exact in H1; apply triangle_exact in H2.
  destruct H1 as [x [y [E H1]]], H2 as [u [v [E' H2]]].
  subst s; inversion E'; subst; lia.
Qed.
Theorem prefix_nodup : forall t, NoDup (prefix t).
Proof.
  intro t; constructor; [|apply triangle_nodup].
  rewrite triangle_exact; intros [x [y [H _]]]; discriminate.
Qed.
Lemma diagonal_length : forall n, length (diagonal n)=S n.
Proof. intro n; unfold diagonal; rewrite map_length,seq_length; reflexivity. Qed.
Lemma triangle_length : forall n, 2 * length (triangle n)=(n+1)*(n+2).
Proof.
  induction n.
  - reflexivity.
  - change (2 * length (diagonal (S n) ++ triangle n)=(S n+1)*(S n+2)).
    rewrite app_length,diagonal_length; nia.
Qed.
Theorem exact_reachable_capacity : forall t,
  2*length (prefix t)=8+4*t+t*(t+1).
Proof.
  intro t; change (2*S (length (triangle (S t)))=8+4*t+t*(t+1)).
  pose proof (triangle_length (S t)); nia.
Qed.
