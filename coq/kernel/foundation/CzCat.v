(** CzCat: machines and record-preserving simulations form a category, and
    the interleaved product is its categorical product.

    An object is an axis machine: a preorder of records, states, moves, a
    step, a cost per move and a reading of the record.  A morphism from X to
    Y is a simulation of X by Y that keeps the record:

      a map of states and a monotone map of records, such that the record of
      the image state is the image of the record, and every move of X is
      simulated by some run of Y: the image of the state after the move is
      the state Y reaches by that run from the image of the state before.

    Two morphisms are equal when they agree on every state (the record map is
    then determined on every record that occurs).  Under this equality:

      cmpz_hom_id_left, cmpz_hom_id_right, cmpz_hom_assoc
                      identities and composition satisfy the laws of a
                      category (the equations hold on the nose, since a
                      morphism is determined by its state map);
      cmpz_prod_universal
                      the interleaved product of CzProd is the categorical
                      product: the two projections are morphisms, a pair of
                      morphisms has a pairing, and the pairing is the unique
                      morphism with those two components.  This is the
                      justification for the pair as the record of the product:
                      it is the record that makes the parts' certifications
                      both visible and no more than visible;
      cmpz_unit_terminal
                      the machine with one state and no move is a terminal
                      object (and is not Thiele-complete, so Thiele-complete
                      machines have binary products and no terminal object);
      cmpz_tensor     on morphisms that never lower the cost (the host pays
                      at least what the guest paid) the product is a
                      functorial tensor, with the swap, the associator and
                      the unit isomorphisms, each cost-exact;
      cmpz_sim_exit_cost, cmpz_sim_cost_ge_exits
                      a simulation that reflects the order of records, into a
                      machine that pays the toll, pays at least 1 for every
                      move of the guest that leaves the down-set of its
                      record, and over a run at least the guest's number of
                      exits: the floor is scale-invariant. *)

From Coq Require Import List Bool Arith.PeanoNat Lia.
Import ListNotations.
From Kernel Require Import AxCore.
From Kernel Require Import AxLatch.
From Kernel Require Import AxComplete.
From Kernel Require Import CzProd CzProdTC.
Require Minimal.ThieleComplete.
Module T := Minimal.ThieleComplete.

Record cmpz_obj : Type := mk_obj {
  ob_A : Type;
  ob_P : BPre ob_A;
  ob_M : amachine ob_A ob_P
}.

Record cmpz_hom (X Y : cmpz_obj) : Type := mk_hom {
  h_state : am_state (ob_M X) -> am_state (ob_M Y);
  h_rec : ob_A X -> ob_A Y;
  h_mono : forall a b, bp_le (ob_P X) a b -> bp_le (ob_P Y) (h_rec a) (h_rec b);
  h_rec_nat : forall s, am_rec (ob_M Y) (h_state s) = h_rec (am_rec (ob_M X) s);
  h_sim : forall s m, exists tr : list (am_move (ob_M Y)),
            h_state (am_step (ob_M X) s m) = am_run (ob_M Y) tr (h_state s)
}.

Arguments h_state {X Y} _ _.
Arguments h_rec {X Y} _ _.
Arguments h_mono {X Y} _ _ _ _.
Arguments h_rec_nat {X Y} _ _.
Arguments h_sim {X Y} _ _ _.

(** Two morphisms are equal when they agree on states. *)
Definition cmpz_hom_eq {X Y} (f g : cmpz_hom X Y) : Prop :=
  forall s, h_state f s = h_state g s.

Lemma cmpz_hom_eq_refl : forall {X Y} (f : cmpz_hom X Y), cmpz_hom_eq f f.
Proof. intros X Y f s. reflexivity. Qed.
Lemma cmpz_hom_eq_sym : forall {X Y} (f g : cmpz_hom X Y), cmpz_hom_eq f g -> cmpz_hom_eq g f.
Proof. intros X Y f g H s. symmetry. apply H. Qed.
Lemma cmpz_hom_eq_trans : forall {X Y} (f g k : cmpz_hom X Y),
  cmpz_hom_eq f g -> cmpz_hom_eq g k -> cmpz_hom_eq f k.
Proof. intros X Y f g k H1 H2 s. rewrite (H1 s). apply H2. Qed.

(** The record map agrees on every record that occurs. *)
Lemma cmpz_hom_eq_rec : forall {X Y} (f g : cmpz_hom X Y), cmpz_hom_eq f g ->
  forall s, h_rec f (am_rec (ob_M X) s) = h_rec g (am_rec (ob_M X) s).
Proof.
  intros X Y f g H s. rewrite <- (h_rec_nat f), <- (h_rec_nat g), (H s). reflexivity.
Qed.

(** * Identity and composition *)

Definition cmpz_hom_id (X : cmpz_obj) : cmpz_hom X X.
Proof.
  refine (mk_hom X X (fun s => s) (fun a => a) _ _ _).
  - intros a b H. exact H.
  - intro s. reflexivity.
  - intros s m. exists [m]. reflexivity.
Defined.

(** A simulation lifts from moves to runs. *)
Lemma cmpz_hom_trace : forall {X Y} (f : cmpz_hom X Y) (tr : list (am_move (ob_M X))) s,
  exists tr' : list (am_move (ob_M Y)),
    h_state f (am_run (ob_M X) tr s) = am_run (ob_M Y) tr' (h_state f s).
Proof.
  intros X Y f. induction tr as [| m tr IH]; intro s.
  - exists []. reflexivity.
  - rewrite am_run_cons. destruct (IH (am_step (ob_M X) s m)) as [tr1 H1].
    destruct (h_sim f s m) as [tr2 H2].
    exists (tr2 ++ tr1). rewrite am_run_app, <- H2. exact H1.
Qed.

Definition cmpz_hom_comp {X Y Z} (g : cmpz_hom Y Z) (f : cmpz_hom X Y) : cmpz_hom X Z.
Proof.
  refine (mk_hom X Z (fun s => h_state g (h_state f s)) (fun a => h_rec g (h_rec f a)) _ _ _).
  - intros a b H. apply (h_mono g), (h_mono f), H.
  - intro s. rewrite (h_rec_nat g), (h_rec_nat f). reflexivity.
  - intros s m. destruct (h_sim f s m) as [tr H1].
    destruct (cmpz_hom_trace g tr (h_state f s)) as [tr' H2].
    exists tr'. rewrite H1. exact H2.
Defined.

Theorem cmpz_hom_id_left : forall {X Y} (f : cmpz_hom X Y),
  cmpz_hom_eq (cmpz_hom_comp (cmpz_hom_id Y) f) f.
Proof. intros X Y f s. reflexivity. Qed.

Theorem cmpz_hom_id_right : forall {X Y} (f : cmpz_hom X Y),
  cmpz_hom_eq (cmpz_hom_comp f (cmpz_hom_id X)) f.
Proof. intros X Y f s. reflexivity. Qed.

Theorem cmpz_hom_assoc : forall {W X Y Z} (f : cmpz_hom W X) (g : cmpz_hom X Y) (h : cmpz_hom Y Z),
  cmpz_hom_eq (cmpz_hom_comp h (cmpz_hom_comp g f)) (cmpz_hom_comp (cmpz_hom_comp h g) f).
Proof. intros W X Y Z f g h s. reflexivity. Qed.

Theorem cmpz_hom_comp_cong : forall {X Y Z} (f f' : cmpz_hom X Y) (g g' : cmpz_hom Y Z),
  cmpz_hom_eq f f' -> cmpz_hom_eq g g' ->
  cmpz_hom_eq (cmpz_hom_comp g f) (cmpz_hom_comp g' f').
Proof. intros X Y Z f f' g g' H1 H2 s. cbn. rewrite (H1 s). apply H2. Qed.

(** * The product *)

Definition cmpz_obj_prod (X Y : cmpz_obj) : cmpz_obj :=
  mk_obj (ob_A X * ob_A Y) (cmpz_pair_pre (ob_P X) (ob_P Y)) (cmpz_prod (ob_M X) (ob_M Y)).

Definition cmpz_pi1 (X Y : cmpz_obj) : cmpz_hom (cmpz_obj_prod X Y) X.
Proof.
  refine (mk_hom (cmpz_obj_prod X Y) X (fun s => fst s) (fun a => fst a) _ _ _).
  - intros a b H. apply cmpz_pair_le in H. exact (proj1 H).
  - intro s. reflexivity.
  - intros s [x | y]; [exists [x] | exists []]; reflexivity.
Defined.

Definition cmpz_pi2 (X Y : cmpz_obj) : cmpz_hom (cmpz_obj_prod X Y) Y.
Proof.
  refine (mk_hom (cmpz_obj_prod X Y) Y (fun s => snd s) (fun a => snd a) _ _ _).
  - intros a b H. apply cmpz_pair_le in H. exact (proj2 H).
  - intro s. reflexivity.
  - intros s [x | y]; [exists [] | exists [y]]; reflexivity.
Defined.

Definition cmpz_pairing {Z X Y} (f : cmpz_hom Z X) (g : cmpz_hom Z Y) : cmpz_hom Z (cmpz_obj_prod X Y).
Proof.
  refine (mk_hom Z (cmpz_obj_prod X Y) (fun z => (h_state f z, h_state g z))
            (fun a => (h_rec f a, h_rec g a)) _ _ _).
  - intros a b H. apply cmpz_pair_le. cbn. split; [apply (h_mono f) | apply (h_mono g)]; exact H.
  - intro s. cbn. rewrite (h_rec_nat f), (h_rec_nat g). reflexivity.
  - intros s m. destruct (h_sim f s m) as [tr1 H1]. destruct (h_sim g s m) as [tr2 H2].
    exists (map inl tr1 ++ map inr tr2). cbn.
    rewrite cmpz_run_prod. cbn [fst snd].
    rewrite cmpz_lefts_app, cmpz_rights_app.
    rewrite (cmpz_lefts_map_inl (Y := am_move (ob_M Y))), (cmpz_rights_map_inl (Y := am_move (ob_M Y))),
            (cmpz_lefts_map_inr (X := am_move (ob_M X))), (cmpz_rights_map_inr (X := am_move (ob_M X))).
    rewrite app_nil_r, app_nil_l. rewrite H1, H2. reflexivity.
Defined.

Theorem cmpz_prod_universal : forall {Z X Y} (f : cmpz_hom Z X) (g : cmpz_hom Z Y),
  cmpz_hom_eq (cmpz_hom_comp (cmpz_pi1 X Y) (cmpz_pairing f g)) f /\
  cmpz_hom_eq (cmpz_hom_comp (cmpz_pi2 X Y) (cmpz_pairing f g)) g /\
  forall h : cmpz_hom Z (cmpz_obj_prod X Y),
    cmpz_hom_eq (cmpz_hom_comp (cmpz_pi1 X Y) h) f ->
    cmpz_hom_eq (cmpz_hom_comp (cmpz_pi2 X Y) h) g ->
    cmpz_hom_eq h (cmpz_pairing f g).
Proof.
  intros Z X Y f g. split; [| split].
  - intro s. reflexivity.
  - intro s. reflexivity.
  - intros h H1 H2 s. cbn in *. rewrite (surjective_pairing (h_state h s)).
    f_equal; [apply H1 | apply H2].
Qed.

(** * The terminal object *)

Definition cmpz_unit_machine : amachine unit (disc_pre (fun _ _ => true) (fun _ => eq_refl) (fun _ _ _ _ _ => eq_refl)) :=
  mk_am unit (disc_pre (fun _ _ => true) (fun _ => eq_refl) (fun _ _ _ _ _ => eq_refl))
    unit Empty_set (fun s m => match m with end) (fun m => match m with end) (fun _ => tt).

Definition cmpz_unit : cmpz_obj :=
  mk_obj unit (disc_pre (fun _ _ => true) (fun _ => eq_refl) (fun _ _ _ _ _ => eq_refl)) cmpz_unit_machine.

Definition cmpz_bang (X : cmpz_obj) : cmpz_hom X cmpz_unit.
Proof.
  refine (mk_hom X cmpz_unit (fun _ => tt) (fun _ => tt) _ _ _).
  - intros a b H. cbn. reflexivity.
  - intro s. reflexivity.
  - intros s m. exists []. reflexivity.
Defined.

Theorem cmpz_unit_terminal : forall X (h : cmpz_hom X cmpz_unit),
  cmpz_hom_eq h (cmpz_bang X).
Proof. intros X h s. destruct (h_state h s). reflexivity. Qed.

(** The terminal machine is not Thiele-complete: it has no move, and a
    Thiele-complete machine has the compiled counter instructions. *)
Theorem cmpz_unit_not_tc : ~ ax_thiele_complete cmpz_unit_machine.
Proof.
  intros [I [[Hk _] _]].
  exact (match T.ub_compile (axi_base I) (T.CINC T.RA) with end).
Qed.

(** * Costs *)

Definition cmpz_hom_cost_ge {X Y} (f : cmpz_hom X Y) : Prop :=
  forall s m, exists tr : list (am_move (ob_M Y)),
    h_state f (am_step (ob_M X) s m) = am_run (ob_M Y) tr (h_state f s) /\
    cmpz_cost (ob_M Y) tr >= am_cost (ob_M X) m.

Definition cmpz_hom_cost_exact {X Y} (f : cmpz_hom X Y) : Prop :=
  forall s m, exists tr : list (am_move (ob_M Y)),
    h_state f (am_step (ob_M X) s m) = am_run (ob_M Y) tr (h_state f s) /\
    cmpz_cost (ob_M Y) tr = am_cost (ob_M X) m.

Lemma cmpz_id_cost_exact : forall X, cmpz_hom_cost_exact (cmpz_hom_id X).
Proof. intros X s m. exists [m]. split; [reflexivity |]. cbn. unfold cmpz_cost. simpl. lia. Qed.

Lemma cmpz_id_cost_ge : forall X, cmpz_hom_cost_ge (cmpz_hom_id X).
Proof. intros X s m. exists [m]. split; [reflexivity |]. cbn. unfold cmpz_cost. simpl. lia. Qed.

Lemma cmpz_hom_trace_cost_ge : forall {X Y} (f : cmpz_hom X Y), cmpz_hom_cost_ge f ->
  forall (tr : list (am_move (ob_M X))) s, exists tr' : list (am_move (ob_M Y)),
    h_state f (am_run (ob_M X) tr s) = am_run (ob_M Y) tr' (h_state f s) /\
    cmpz_cost (ob_M Y) tr' >= cmpz_cost (ob_M X) tr.
Proof.
  intros X Y f Hf. induction tr as [| m tr IH]; intro s.
  - exists []. split; [reflexivity | unfold cmpz_cost; simpl; lia].
  - rewrite am_run_cons. destruct (IH (am_step (ob_M X) s m)) as [tr1 [H1 C1]].
    destruct (Hf s m) as [tr2 [H2 C2]].
    exists (tr2 ++ tr1). split.
    + rewrite am_run_app, <- H2. exact H1.
    + rewrite cmpz_cost_app. unfold cmpz_cost in *. simpl in *. lia.
Qed.

Lemma cmpz_hom_trace_cost_exact : forall {X Y} (f : cmpz_hom X Y), cmpz_hom_cost_exact f ->
  forall (tr : list (am_move (ob_M X))) s, exists tr' : list (am_move (ob_M Y)),
    h_state f (am_run (ob_M X) tr s) = am_run (ob_M Y) tr' (h_state f s) /\
    cmpz_cost (ob_M Y) tr' = cmpz_cost (ob_M X) tr.
Proof.
  intros X Y f Hf. induction tr as [| m tr IH]; intro s.
  - exists []. split; reflexivity.
  - rewrite am_run_cons. destruct (IH (am_step (ob_M X) s m)) as [tr1 [H1 C1]].
    destruct (Hf s m) as [tr2 [H2 C2]].
    exists (tr2 ++ tr1). split.
    + rewrite am_run_app, <- H2. exact H1.
    + rewrite cmpz_cost_app. unfold cmpz_cost in *. simpl in *. lia.
Qed.

Theorem cmpz_comp_cost_ge : forall {X Y Z} (f : cmpz_hom X Y) (g : cmpz_hom Y Z),
  cmpz_hom_cost_ge f -> cmpz_hom_cost_ge g -> cmpz_hom_cost_ge (cmpz_hom_comp g f).
Proof.
  intros X Y Z f g Hf Hg s m. destruct (Hf s m) as [tr [H1 C1]].
  destruct (cmpz_hom_trace_cost_ge g Hg tr (h_state f s)) as [tr' [H2 C2]].
  exists tr'. split; [cbn; rewrite H1; exact H2 | lia].
Qed.

Theorem cmpz_comp_cost_exact : forall {X Y Z} (f : cmpz_hom X Y) (g : cmpz_hom Y Z),
  cmpz_hom_cost_exact f -> cmpz_hom_cost_exact g -> cmpz_hom_cost_exact (cmpz_hom_comp g f).
Proof.
  intros X Y Z f g Hf Hg s m. destruct (Hf s m) as [tr [H1 C1]].
  destruct (cmpz_hom_trace_cost_exact g Hg tr (h_state f s)) as [tr' [H2 C2]].
  exists tr'. split; [cbn; rewrite H1; exact H2 | lia].
Qed.

(** * The tensor: the product on morphisms that never lower the cost *)

Definition cmpz_tensor {X X' Y Y'} (f : cmpz_hom X Y) (g : cmpz_hom X' Y') :
  cmpz_hom (cmpz_obj_prod X X') (cmpz_obj_prod Y Y').
Proof.
  refine (mk_hom (cmpz_obj_prod X X') (cmpz_obj_prod Y Y')
            (fun s => (h_state f (fst s), h_state g (snd s)))
            (fun a => (h_rec f (fst a), h_rec g (snd a))) _ _ _).
  - intros a b H. apply cmpz_pair_le in H. destruct H as [H1 H2].
    apply cmpz_pair_le. cbn. split; [apply (h_mono f) | apply (h_mono g)]; assumption.
  - intro s. cbn. rewrite (h_rec_nat f), (h_rec_nat g). reflexivity.
  - intros s [x | y].
    + destruct (h_sim f (fst s) x) as [tr H1]. exists (map inl tr). cbn.
      rewrite cmpz_run_prod. cbn [fst snd].
      rewrite (cmpz_lefts_map_inl (Y := am_move (ob_M Y'))), (cmpz_rights_map_inl (Y := am_move (ob_M Y'))).
      cbn. rewrite H1. reflexivity.
    + destruct (h_sim g (snd s) y) as [tr H1]. exists (map inr tr). cbn.
      rewrite cmpz_run_prod. cbn [fst snd].
      rewrite (cmpz_lefts_map_inr (X := am_move (ob_M Y))), (cmpz_rights_map_inr (X := am_move (ob_M Y))).
      cbn. rewrite H1. reflexivity.
Defined.

Theorem cmpz_tensor_id : forall X Y,
  cmpz_hom_eq (cmpz_tensor (cmpz_hom_id X) (cmpz_hom_id Y)) (cmpz_hom_id (cmpz_obj_prod X Y)).
Proof. intros X Y [s t] . reflexivity. Qed.

Theorem cmpz_tensor_comp : forall {X X' Y Y' Z Z'}
    (f : cmpz_hom X Y) (g : cmpz_hom Y Z) (f' : cmpz_hom X' Y') (g' : cmpz_hom Y' Z'),
  cmpz_hom_eq (cmpz_tensor (cmpz_hom_comp g f) (cmpz_hom_comp g' f'))
              (cmpz_hom_comp (cmpz_tensor g g') (cmpz_tensor f f')).
Proof. intros X X' Y Y' Z Z' f g f' g' [s t]. reflexivity. Qed.

Theorem cmpz_tensor_cost_ge : forall {X X' Y Y'} (f : cmpz_hom X Y) (g : cmpz_hom X' Y'),
  cmpz_hom_cost_ge f -> cmpz_hom_cost_ge g -> cmpz_hom_cost_ge (cmpz_tensor f g).
Proof.
  intros X X' Y Y' f g Hf Hg s [x | y].
  - destruct (Hf (fst s) x) as [tr [H1 C1]]. exists (map inl tr). split.
    + cbn. rewrite cmpz_run_prod. cbn [fst snd].
      rewrite (cmpz_lefts_map_inl (Y := am_move (ob_M Y'))), (cmpz_rights_map_inl (Y := am_move (ob_M Y'))).
      cbn. rewrite H1. reflexivity.
    + cbn. rewrite cmpz_cost_prod.
      rewrite (cmpz_lefts_map_inl (Y := am_move (ob_M Y'))), (cmpz_rights_map_inl (Y := am_move (ob_M Y'))).
      unfold cmpz_cost at 2. simpl. lia.
  - destruct (Hg (snd s) y) as [tr [H1 C1]]. exists (map inr tr). split.
    + cbn. rewrite cmpz_run_prod. cbn [fst snd].
      rewrite (cmpz_lefts_map_inr (X := am_move (ob_M Y))), (cmpz_rights_map_inr (X := am_move (ob_M Y))).
      cbn. rewrite H1. reflexivity.
    + cbn. rewrite cmpz_cost_prod.
      rewrite (cmpz_lefts_map_inr (X := am_move (ob_M Y))), (cmpz_rights_map_inr (X := am_move (ob_M Y))).
      unfold cmpz_cost at 1. simpl. lia.
Qed.

(** The swap, the associator and the unit isomorphisms, with inverses. *)
Definition cmpz_swap (X Y : cmpz_obj) : cmpz_hom (cmpz_obj_prod X Y) (cmpz_obj_prod Y X) :=
  cmpz_pairing (cmpz_pi2 X Y) (cmpz_pi1 X Y).

Theorem cmpz_swap_inv : forall X Y,
  cmpz_hom_eq (cmpz_hom_comp (cmpz_swap Y X) (cmpz_swap X Y)) (cmpz_hom_id (cmpz_obj_prod X Y)).
Proof. intros X Y [s t]. reflexivity. Qed.

Definition cmpz_assoc (X Y Z : cmpz_obj) :
  cmpz_hom (cmpz_obj_prod (cmpz_obj_prod X Y) Z) (cmpz_obj_prod X (cmpz_obj_prod Y Z)) :=
  cmpz_pairing
    (cmpz_hom_comp (cmpz_pi1 X Y) (cmpz_pi1 (cmpz_obj_prod X Y) Z))
    (cmpz_pairing
       (cmpz_hom_comp (cmpz_pi2 X Y) (cmpz_pi1 (cmpz_obj_prod X Y) Z))
       (cmpz_pi2 (cmpz_obj_prod X Y) Z)).

Definition cmpz_assoc_inv (X Y Z : cmpz_obj) :
  cmpz_hom (cmpz_obj_prod X (cmpz_obj_prod Y Z)) (cmpz_obj_prod (cmpz_obj_prod X Y) Z) :=
  cmpz_pairing
    (cmpz_pairing (cmpz_pi1 X (cmpz_obj_prod Y Z))
                  (cmpz_hom_comp (cmpz_pi1 Y Z) (cmpz_pi2 X (cmpz_obj_prod Y Z))))
    (cmpz_hom_comp (cmpz_pi2 Y Z) (cmpz_pi2 X (cmpz_obj_prod Y Z))).

Theorem cmpz_assoc_iso : forall X Y Z,
  cmpz_hom_eq (cmpz_hom_comp (cmpz_assoc_inv X Y Z) (cmpz_assoc X Y Z))
              (cmpz_hom_id (cmpz_obj_prod (cmpz_obj_prod X Y) Z)) /\
  cmpz_hom_eq (cmpz_hom_comp (cmpz_assoc X Y Z) (cmpz_assoc_inv X Y Z))
              (cmpz_hom_id (cmpz_obj_prod X (cmpz_obj_prod Y Z))).
Proof.
  intros X Y Z. split; [intros [[s t] u] | intros [s [t u]]]; reflexivity.
Qed.

(** The unit isomorphism: a product with the terminal machine is the machine. *)
Definition cmpz_unit_r (X : cmpz_obj) : cmpz_hom (cmpz_obj_prod X cmpz_unit) X := cmpz_pi1 X cmpz_unit.
Definition cmpz_unit_r_inv (X : cmpz_obj) : cmpz_hom X (cmpz_obj_prod X cmpz_unit) :=
  cmpz_pairing (cmpz_hom_id X) (cmpz_bang X).

Theorem cmpz_unit_r_iso : forall X,
  cmpz_hom_eq (cmpz_hom_comp (cmpz_unit_r_inv X) (cmpz_unit_r X)) (cmpz_hom_id (cmpz_obj_prod X cmpz_unit)) /\
  cmpz_hom_eq (cmpz_hom_comp (cmpz_unit_r X) (cmpz_unit_r_inv X)) (cmpz_hom_id X).
Proof.
  intros X. split; [intros [s t]; destruct t; reflexivity | intro s; reflexivity].
Qed.

(** Coherence.  A morphism is determined by its state map, so the pentagon,
    the triangle and the hexagon are equations between re-bracketings of
    tuples. *)
Theorem cmpz_pentagon : forall W X Y Z,
  cmpz_hom_eq
    (cmpz_hom_comp (cmpz_assoc W X (cmpz_obj_prod Y Z)) (cmpz_assoc (cmpz_obj_prod W X) Y Z))
    (cmpz_hom_comp (cmpz_tensor (cmpz_hom_id W) (cmpz_assoc X Y Z))
       (cmpz_hom_comp (cmpz_assoc W (cmpz_obj_prod X Y) Z)
                      (cmpz_tensor (cmpz_assoc W X Y) (cmpz_hom_id Z)))).
Proof. intros W X Y Z [[[w x] y] z]. reflexivity. Qed.

Theorem cmpz_triangle : forall X Y,
  cmpz_hom_eq
    (cmpz_hom_comp (cmpz_tensor (cmpz_hom_id X) (cmpz_pi2 cmpz_unit Y)) (cmpz_assoc X cmpz_unit Y))
    (cmpz_tensor (cmpz_pi1 X cmpz_unit) (cmpz_hom_id Y)).
Proof. intros X Y [[x u] y]. reflexivity. Qed.

Theorem cmpz_hexagon : forall X Y Z,
  cmpz_hom_eq
    (cmpz_hom_comp (cmpz_assoc Y Z X)
       (cmpz_hom_comp (cmpz_swap X (cmpz_obj_prod Y Z)) (cmpz_assoc X Y Z)))
    (cmpz_hom_comp (cmpz_tensor (cmpz_hom_id Y) (cmpz_swap X Z))
       (cmpz_hom_comp (cmpz_assoc Y X Z) (cmpz_tensor (cmpz_swap X Y) (cmpz_hom_id Z)))).
Proof. intros X Y Z [[x y] z]. reflexivity. Qed.

(** The swap, the associator and the unit isomorphism are cost-exact, so the
    tensor is a symmetric monoidal structure on cost-exact morphisms. *)
Theorem cmpz_swap_cost_exact : forall X Y, cmpz_hom_cost_exact (cmpz_swap X Y).
Proof.
  intros X Y [s t] [x | y].
  - exists [inr x]. split; [reflexivity |]. cbn. unfold cmpz_cost. simpl. lia.
  - exists [inl y]. split; [reflexivity |]. cbn. unfold cmpz_cost. simpl. lia.
Qed.

Theorem cmpz_assoc_cost_exact : forall X Y Z, cmpz_hom_cost_exact (cmpz_assoc X Y Z).
Proof.
  intros X Y Z [[s t] u] [[x | y] | z].
  - exists [inl x]. split; [reflexivity |]. cbn. unfold cmpz_cost. simpl. lia.
  - exists [inr (inl y)]. split; [reflexivity |]. cbn. unfold cmpz_cost. simpl. lia.
  - exists [inr (inr z)]. split; [reflexivity |]. cbn. unfold cmpz_cost. simpl. lia.
Qed.

Theorem cmpz_unit_r_cost_exact : forall X, cmpz_hom_cost_exact (cmpz_unit_r X).
Proof.
  intros X [s t] [x | y].
  - exists [x]. split; [reflexivity |]. cbn. unfold cmpz_cost. simpl. lia.
  - destruct y.
Qed.

(** * The floor is scale-invariant *)

Lemma cmpz_cost_total : forall {A' P'} (X : amachine A' P') tr,
  cmpz_cost X tr = ax_total (X := am_axsys X) tr.
Proof. intros A' P' X. induction tr as [| m tr IH]; simpl; [reflexivity |]. unfold cmpz_cost in *. simpl. rewrite IH. reflexivity. Qed.

(** A simulation that reflects the order of records, into a machine that pays
    the toll, charges at least 1 for every move of the guest that leaves the
    down-set of its record. *)
Theorem cmpz_sim_exit_cost : forall {X Y} (f : cmpz_hom X Y),
  (forall a b, bp_le (ob_P Y) (h_rec f a) (h_rec f b) -> bp_le (ob_P X) a b) ->
  ax_a2 (X := am_axsys (ob_M Y)) ->
  forall s m (tr : list (am_move (ob_M Y))),
    h_state f (am_step (ob_M X) s m) = am_run (ob_M Y) tr (h_state f s) ->
    ax_exits (X := am_axsys (ob_M X)) s m -> cmpz_cost (ob_M Y) tr >= 1.
Proof.
  intros X Y f Hemb Ha s m tr Hsim Hex.
  rewrite cmpz_cost_total.
  apply (proj2 (ax_floor_iff_a2 (am_axsys (ob_M Y))) Ha tr (h_state f s)).
  rewrite am_axsys_run. simpl. rewrite <- Hsim, (h_rec_nat f), (h_rec_nat f).
  intro Hle. apply Hex. unfold ax_exits. simpl. apply Hemb. exact Hle.
Qed.

(** Over a run, the host pays at least as many tolls as the guest's record
    leaves its down-set. *)
Theorem cmpz_sim_cost_ge_exits : forall {X Y} (f : cmpz_hom X Y),
  (forall a b, bp_le (ob_P Y) (h_rec f a) (h_rec f b) -> bp_le (ob_P X) a b) ->
  ax_a2 (X := am_axsys (ob_M Y)) ->
  forall (tr : list (am_move (ob_M X))) s, exists tr' : list (am_move (ob_M Y)),
    h_state f (am_run (ob_M X) tr s) = am_run (ob_M Y) tr' (h_state f s) /\
    cmpz_cost (ob_M Y) tr' >= cmpz_exit_count (ob_M X) tr s.
Proof.
  intros X Y f Hemb Ha. induction tr as [| m tr IH]; intro s.
  - exists []. split; [reflexivity | unfold cmpz_exit_count; simpl; lia].
  - rewrite am_run_cons. destruct (IH (am_step (ob_M X) s m)) as [tr1 [H1 C1]].
    destruct (h_sim f s m) as [tr2 H2].
    exists (tr2 ++ tr1). split.
    + rewrite am_run_app, <- H2. exact H1.
    + rewrite cmpz_cost_app. unfold cmpz_exit_count in *. simpl.
      destruct (bp_leb (ob_A X) (ob_P X) (am_rec (ob_M X) (am_step (ob_M X) s m)) (am_rec (ob_M X) s)) eqn:E.
      * lia.
      * assert (Hex : ax_exits (X := am_axsys (ob_M X)) s m)
          by (unfold ax_exits, bp_le; simpl; rewrite E; discriminate).
        pose proof (cmpz_sim_exit_cost f Hemb Ha s m tr2 H2 Hex). lia.
Qed.

Print Assumptions cmpz_hom_assoc.
Print Assumptions cmpz_prod_universal.
Print Assumptions cmpz_unit_terminal.
Print Assumptions cmpz_unit_not_tc.
Print Assumptions cmpz_comp_cost_ge.
Print Assumptions cmpz_comp_cost_exact.
Print Assumptions cmpz_tensor_cost_ge.
Print Assumptions cmpz_pentagon.
Print Assumptions cmpz_hexagon.
Print Assumptions cmpz_assoc_iso.
Print Assumptions cmpz_sim_exit_cost.
Print Assumptions cmpz_sim_cost_ge_exits.
