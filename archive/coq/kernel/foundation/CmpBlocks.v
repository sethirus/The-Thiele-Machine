(** CmpBlocks.v: counter-machine code blocks and what they do.

    The machine is the one of the vendored library (MinskyMachines/MMenv):
    registers are natural numbers, INC x adds 1 to register x, DEC x j
    subtracts 1 from register x and goes on when x is positive, and goes to
    address j when x is 0. The compiler keeps register 0 at 0 for the whole
    run and uses DEC 0 j as the jump to j.

    Every block is a list of instructions placed at an address a; its jump
    targets are absolute and a block does not depend on anything but its own
    address. The statements are written with cmp_reach: the run from the
    state (a, m) ends at the state (b, w) where the final registers equal w
    at every register (the vendored relation compares environments as
    functions, which are not equal as terms after different update orders;
    cmp_mmc_ext shows that nothing else depends on the term).

      cmp_clear a r        r := 0                              (2 instructions)
      cmp_addmv a s d      d := d + s, s := 0                  (3)
      cmp_copy a s d t     d := d + s, s kept, t used as a 0   (7)
      cmp_sub a t u        t := t - u (truncated), u := 0      (3)
      cmp_fin a t u j      t := 0, u := 0, go to j             (5)
      cmp_eqblk a t u lt lf  go to lt if t = u, else lf, with t, u cleared (14)
      cmp_ltblk a t u lt lf  go to lt if t < u, else lf, with t, u cleared (14)

    Dependencies: Coq standard library, the vendored coq-undecidability
    library and CmpLang.v. No axioms and no unfinished proofs.                         *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is one stage of the verified compiler pipeline of CmpPipeline.v and
   imports only the Coq standard library, the vendored coq-undecidability
   library and CmpLang.v. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Undecidability.Shared.Libs.DLW Require Import utils pos vec subcode sss.
From Undecidability.MinskyMachines Require Import MM.
From Undecidability.MinskyMachines.MMenv Require Import env mme_defs.
Require Import Kernel.CmpLang.

Definition cmp_mi : Set := mm_instr nat.

Local Notation mmstep := (@mm_sss_env nat eq_nat_dec).

(* A run of the vendored semantics, with the environments as functions. *)
Definition cmp_mmc (P : nat * list cmp_mi) (i : nat) (v : nat -> nat) (j : nat) (w : nat -> nat) : Prop :=
  sss_compute mmstep P (i, v) (j, w).

Lemma cmp_get_env : forall (e : env nat nat) x, get_env e x = e x.
Proof. intros. unfold get_env. reflexivity. Qed.

Lemma cmp_set_env : forall (e : env nat nat) x v y,
  set_env eq_nat_dec e x v y = if Nat.eqb y x then v else e y.
Proof.
  intros. unfold set_env. destruct (eq_nat_dec x y) as [<- | Hne].
  - rewrite Nat.eqb_refl. reflexivity.
  - destruct (Nat.eqb_spec y x); [congruence | reflexivity].
Qed.

(* ================================================================= *)
(* Runs do not depend on how the registers are stored.                *)
(* ================================================================= *)

Lemma cmp_mmstep_ext : forall I i v j w v', mmstep I (i, v) (j, w) -> (forall y, v y = v' y) ->
  exists w', (forall y, w y = w' y) /\ mmstep I (i, v') (j, w').
Proof.
  intros I i v j w v' H Hv. inversion H; subst.
  - eexists. split; [| apply in_mm_sss_env_inc].
    intros y. rewrite !cmp_set_env, !cmp_get_env. destruct (Nat.eqb y x); [rewrite Hv; reflexivity | apply Hv].
  - exists v'. split; [exact Hv |]. apply in_mm_sss_env_dec_0. rewrite cmp_get_env in *. rewrite <- Hv. assumption.
  - eexists. split; [| apply in_mm_sss_env_dec_1 with (u := u)].
    + intros y. rewrite !cmp_set_env. destruct (Nat.eqb y x); [reflexivity | apply Hv].
    + rewrite cmp_get_env in *. rewrite <- Hv. assumption.
Qed.

Lemma cmp_mmc_ext : forall P k i v j w v', sss_steps mmstep P k (i, v) (j, w) -> (forall y, v y = v' y) ->
  exists w', (forall y, w y = w' y) /\ sss_steps mmstep P k (i, v') (j, w').
Proof.
  intros P k. induction k as [| k IH]; intros i v j w v' H Hv.
  - apply sss_steps_0_inv in H. inversion H; subst. exists v'. split; [exact Hv | constructor].
  - destruct (sss_steps_S_inv' H) as ((i2 & v2) & H1 & H2).
    destruct H1 as (k0 & l & I & r & d & HP & Hst & Hs). inversion Hst; subst.
    destruct (cmp_mmstep_ext _ _ _ _ _ v' Hs Hv) as (v3 & Q3 & S3).
    destruct (IH _ _ _ _ v3 H2 Q3) as (w' & Qw & Sw). exists w'. split; [exact Qw |].
    econstructor 2; [| exact Sw]. exists k0, l, I, r, v'. split; [reflexivity | split; [reflexivity | exact S3]].
Qed.

(* The run ends at (j, w) up to the values of the registers: after any number
   of steps (cmp_reach0) or after at least one step (cmp_reach). *)
Definition cmp_reach0 (P : nat * list cmp_mi) (i : nat) (v : nat -> nat) (j : nat) (w : nat -> nat) : Prop :=
  exists w', (forall y, w' y = w y) /\ cmp_mmc P i v j w'.

Definition cmp_reach (P : nat * list cmp_mi) (i : nat) (v : nat -> nat) (j : nat) (w : nat -> nat) : Prop :=
  exists w', (forall y, w' y = w y) /\ sss_progress mmstep P (i, v) (j, w').

Lemma cmp_reach0_refl : forall P i v w, (forall y, v y = w y) -> cmp_reach0 P i v i w.
Proof. intros. exists v. split; [exact H | exists 0; constructor]. Qed.

Lemma cmp_reach0_eq : forall P i v j w w2, cmp_reach0 P i v j w -> (forall y, w y = w2 y) -> cmp_reach0 P i v j w2.
Proof. intros P i v j w w2 (w' & H1 & H2) H. exists w'. split; [| exact H2]. intros y. rewrite H1. apply H. Qed.

Lemma cmp_reach0_at : forall P i v j w j2, cmp_reach0 P i v j w -> j = j2 -> cmp_reach0 P i v j2 w.
Proof. intros. subst. assumption. Qed.

Lemma cmp_reach0_trans : forall P i v j w k u, cmp_reach0 P i v j w -> cmp_reach0 P j w k u -> cmp_reach0 P i v k u.
Proof.
  intros P i v j w k u (w1 & H1 & n1 & S1) (u2 & H2 & n2 & S2).
  destruct (cmp_mmc_ext _ _ _ _ _ _ w1 S2 (fun y => eq_sym (H1 y))) as (u3 & Q3 & S3).
  exists u3. split.
  - intros y. rewrite <- Q3. apply H2.
  - exists (n1 + n2). eapply sss_steps_trans; eassumption.
Qed.

Lemma cmp_reach_eq : forall P i v j w w2, cmp_reach P i v j w -> (forall y, w y = w2 y) -> cmp_reach P i v j w2.
Proof. intros P i v j w w2 (w' & H1 & H2) H. exists w'. split; [| exact H2]. intros y. rewrite H1. apply H. Qed.

Lemma cmp_reach_at : forall P i v j w j2, cmp_reach P i v j w -> j = j2 -> cmp_reach P i v j2 w.
Proof. intros. subst. assumption. Qed.

Lemma cmp_reach_reach0 : forall P i v j w, cmp_reach P i v j w -> cmp_reach0 P i v j w.
Proof. intros P i v j w (w' & H1 & k & _ & H2). exists w'. split; [exact H1 | exists k; exact H2]. Qed.

(* Progress then anything, or anything then progress. *)
Lemma cmp_reach_trans0 : forall P i v j w k u, cmp_reach P i v j w -> cmp_reach0 P j w k u -> cmp_reach P i v k u.
Proof.
  intros P i v j w k u (w1 & H1 & n1 & Hn1 & S1) (u2 & H2 & n2 & S2).
  destruct (cmp_mmc_ext _ _ _ _ _ _ w1 S2 (fun y => eq_sym (H1 y))) as (u3 & Q3 & S3).
  exists u3. split.
  - intros y. rewrite <- Q3. apply H2.
  - exists (n1 + n2). split; [lia |]. eapply sss_steps_trans; eassumption.
Qed.

Lemma cmp_reach0_trans_reach : forall P i v j w k u, cmp_reach0 P i v j w -> cmp_reach P j w k u -> cmp_reach P i v k u.
Proof.
  intros P i v j w k u (w1 & H1 & n1 & S1) (u2 & H2 & n2 & Hn2 & S2).
  destruct (cmp_mmc_ext _ _ _ _ _ _ w1 S2 (fun y => eq_sym (H1 y))) as (u3 & Q3 & S3).
  exists u3. split.
  - intros y. rewrite <- Q3. apply H2.
  - exists (n1 + n2). split; [lia |]. eapply sss_steps_trans; eassumption.
Qed.

Lemma cmp_reach_trans : forall P i v j w k u, cmp_reach P i v j w -> cmp_reach P j w k u -> cmp_reach P i v k u.
Proof. intros. eapply cmp_reach_trans0; [eassumption | apply cmp_reach_reach0; assumption]. Qed.

(* ================================================================= *)
(* One instruction.                                                   *)
(* ================================================================= *)

Lemma cmp_stp_inc : forall P i x v w, (i, [mm_inc x]) <sc P ->
  (forall y, w y = if Nat.eqb y x then S (v x) else v y) -> cmp_reach P i v (S i) w.
Proof.
  intros P i x v w Hs Hw. exists (set_env eq_nat_dec v x (S (v x))). split.
  - intros y. rewrite cmp_set_env. symmetry. apply Hw.
  - eapply mm_env_progress_INC with (st := (1 + i, set_env eq_nat_dec v x (S (v x)))); [exact Hs |].
    rewrite cmp_get_env. exists 0. constructor.
Qed.

Lemma cmp_stp_dec0 : forall P i x j v, (i, [mm_dec x j]) <sc P -> v x = 0 -> cmp_reach P i v j v.
Proof.
  intros P i x j v Hs Hz. exists v. split; [intros; reflexivity |].
  eapply mm_env_progress_DEC_0 with (st := (j, v)); [exact Hs | rewrite cmp_get_env; exact Hz | exists 0; constructor].
Qed.

Lemma cmp_stp_decS : forall P i x j u v w, (i, [mm_dec x j]) <sc P -> v x = S u ->
  (forall y, w y = if Nat.eqb y x then u else v y) -> cmp_reach P i v (S i) w.
Proof.
  intros P i x j u v w Hs Hx Hw. exists (set_env eq_nat_dec v x u). split.
  - intros y. rewrite cmp_set_env. symmetry. apply Hw.
  - eapply mm_env_progress_DEC_S with (st := (1 + i, set_env eq_nat_dec v x u)) (u := u);
      [exact Hs | rewrite cmp_get_env; exact Hx | exists 0; constructor].
Qed.

(* The instruction at position k of a placed block. *)
Lemma cmp_ins_at : forall {X : Type} (l : list X) a P k I b, (a, l) <sc P -> nth_error l k = Some I -> b = a + k ->
  (b, [I]) <sc P.
Proof.
  induction l as [| I0 l IH]; intros a P k I b Hs Hn Hb; [destruct k; discriminate |].
  apply subcode_cons_invert_left in Hs. destruct Hs as [H0 H1].
  destruct k as [| k].
  - simpl in Hn. injection Hn as <-. replace b with a by lia. exact H0.
  - simpl in Hn. apply (IH (S a) P k I b H1 Hn). lia.
Qed.

Lemma cmp_sc_l : forall (l r : list cmp_mi) a P, (a, l ++ r) <sc P -> (a, l) <sc P.
Proof. intros l r a P H. apply subcode_trans with (Q := (a, l ++ r)); [apply subcode_left; reflexivity | exact H]. Qed.

Lemma cmp_sc_r : forall (l r : list cmp_mi) a b P, b = a + length l -> (a, l ++ r) <sc P -> (b, r) <sc P.
Proof. intros l r a b P Hb H. apply subcode_trans with (Q := (a, l ++ r)); [apply subcode_right; exact Hb | exact H]. Qed.

Ltac cmp_ins Hs k := eapply (cmp_ins_at _ _ _ k _ _ Hs eq_refl); lia.

(* Decide every equality test of the goal, then close by arithmetic. *)
Ltac eqb_subst := repeat match goal with H : ?x = ?y |- _ => first [ subst x | subst y | fail ] end.
Ltac eqb_all := repeat match goal with |- context[Nat.eqb ?x ?y] => destruct (Nat.eqb_spec x y) end;
  eqb_subst; try lia; try reflexivity.

(* ================================================================= *)
(* The blocks.                                                        *)
(* ================================================================= *)

Definition cmp_clear (a r : nat) : list cmp_mi := [mm_dec r (a + 2); mm_dec 0 a].
Definition cmp_addmv (a s d : nat) : list cmp_mi := [mm_dec s (a + 3); mm_inc d; mm_dec 0 a].
Definition cmp_copy (a s d t : nat) : list cmp_mi :=
  [mm_dec s (a + 4); mm_inc d; mm_inc t; mm_dec 0 a] ++ cmp_addmv (a + 4) t s.
Definition cmp_sub (a t u : nat) : list cmp_mi := [mm_dec u (a + 3); mm_dec t a; mm_dec 0 a].
Definition cmp_fin (a t u j : nat) : list cmp_mi := cmp_clear a u ++ cmp_clear (a + 2) t ++ [mm_dec 0 j].
Definition cmp_eqblk (a t u lt lf : nat) : list cmp_mi :=
  [mm_dec t (a + 3); mm_dec u (a + 4); mm_dec 0 a; mm_dec u (a + 9)] ++
  cmp_fin (a + 4) t u lf ++ cmp_fin (a + 9) t u lt.
Definition cmp_ltblk (a t u lt lf : nat) : list cmp_mi :=
  [mm_dec t (a + 3); mm_dec u (a + 9); mm_dec 0 a; mm_dec u (a + 9)] ++
  cmp_fin (a + 4) t u lt ++ cmp_fin (a + 9) t u lf.

Lemma cmp_clear_len : forall a r, length (cmp_clear a r) = 2. Proof. reflexivity. Qed.
Lemma cmp_addmv_len : forall a s d, length (cmp_addmv a s d) = 3. Proof. reflexivity. Qed.
Lemma cmp_copy_len : forall a s d t, length (cmp_copy a s d t) = 7. Proof. reflexivity. Qed.
Lemma cmp_sub_len : forall a t u, length (cmp_sub a t u) = 3. Proof. reflexivity. Qed.
Lemma cmp_fin_len : forall a t u j, length (cmp_fin a t u j) = 5. Proof. reflexivity. Qed.
Lemma cmp_eqblk_len : forall a t u lt lf, length (cmp_eqblk a t u lt lf) = 14. Proof. reflexivity. Qed.
Lemma cmp_ltblk_len : forall a t u lt lf, length (cmp_ltblk a t u lt lf) = 14. Proof. reflexivity. Qed.

Lemma cmp_blk_clear : forall P a r m, (a, cmp_clear a r) <sc P -> r <> 0 -> m 0 = 0 ->
  cmp_reach P a m (a + 2) (cmp_upd m r 0).
Proof.
  intros P a r m Hs Hr H0.
  remember (m r) as n eqn:En. revert m En H0. induction n as [| n IH]; intros m En H0.
  - eapply cmp_reach_eq.
    + apply cmp_stp_dec0 with (x := r); [cmp_ins Hs 0 | symmetry; exact En].
    + intros y. unfold cmp_upd. destruct (Nat.eqb_spec y r) as [-> | Hne]; [symmetry; exact En | reflexivity].
  - set (m1 := cmp_upd m r n).
    assert (E1 : m1 r = n) by (unfold m1; apply cmp_upd_same).
    assert (E0 : m1 0 = 0) by (unfold m1; rewrite cmp_upd_other by lia; exact H0).
    eapply cmp_reach_trans.
    + apply cmp_stp_decS with (x := r) (j := a + 2) (u := n) (w := m1); [cmp_ins Hs 0 | symmetry; exact En | intros y; reflexivity].
    + eapply cmp_reach_trans.
      * apply cmp_stp_dec0 with (x := 0) (j := a); [cmp_ins Hs 1 | exact E0].
      * eapply cmp_reach_eq; [apply (IH m1 (eq_sym E1) E0) |].
        intros y. unfold m1, cmp_upd. destruct (Nat.eqb y r); reflexivity.
Qed.

Lemma cmp_loop_addmv : forall P a s d, (a, cmp_addmv a s d) <sc P -> s <> 0 -> d <> 0 -> s <> d ->
  forall n m, m s = n -> m 0 = 0 ->
  cmp_reach P a m (a + 3) (fun y => if Nat.eqb y s then 0 else if Nat.eqb y d then m d + m s else m y).
Proof.
  intros P a s d Hs Hs0 Hd0 Hsd. induction n as [| n IH]; intros m En H0.
  - eapply cmp_reach_eq.
    + apply cmp_stp_dec0 with (x := s); [cmp_ins Hs 0 | exact En].
    + intros y. destruct (Nat.eqb_spec y s) as [-> | N1]; [exact En |].
      destruct (Nat.eqb_spec y d); [subst; rewrite En; lia | reflexivity].
  - set (m1 := cmp_upd m s n).
    set (m2 := cmp_upd m1 d (S (m d))).
    assert (E1 : m1 d = m d) by (unfold m1; apply cmp_upd_other; lia).
    assert (E2 : m2 s = n) by (unfold m2; rewrite cmp_upd_other by lia; unfold m1; apply cmp_upd_same).
    assert (E20 : m2 0 = 0) by (unfold m2, m1; rewrite !cmp_upd_other by lia; exact H0).
    eapply cmp_reach_trans.
    + apply cmp_stp_decS with (x := s) (j := a + 3) (u := n) (w := m1); [cmp_ins Hs 0 | exact En | intros y; reflexivity].
    + eapply cmp_reach_trans.
      * apply cmp_stp_inc with (x := d) (w := m2); [cmp_ins Hs 1 |]. intros y. unfold m2, cmp_upd. rewrite E1. reflexivity.
      * eapply cmp_reach_trans.
        -- apply cmp_stp_dec0 with (x := 0) (j := a); [cmp_ins Hs 2 | exact E20].
        -- eapply cmp_reach_eq; [apply (IH m2 E2 E20) |].
           intros y. unfold m2, m1, cmp_upd.
           destruct (Nat.eqb_spec y s) as [-> | N1]; [reflexivity |].
           destruct (Nat.eqb_spec y d) as [-> | N2]; [| reflexivity].
           destruct (Nat.eqb_spec s d); [lia |].
           destruct (Nat.eqb_spec d s); [lia |].
           rewrite !Nat.eqb_refl, En. lia.
Qed.

Lemma cmp_blk_addmv : forall P a s d m, (a, cmp_addmv a s d) <sc P -> s <> 0 -> d <> 0 -> s <> d -> m 0 = 0 ->
  cmp_reach P a m (a + 3) (fun y => if Nat.eqb y s then 0 else if Nat.eqb y d then m d + m s else m y).
Proof. intros. eapply cmp_loop_addmv; eauto. Qed.



Lemma cmp_loop_copy1 : forall P a s d t, (a, cmp_copy a s d t) <sc P -> s <> 0 -> d <> 0 -> t <> 0 ->
  s <> d -> s <> t -> d <> t ->
  forall n m, m s = n -> m 0 = 0 ->
  cmp_reach P a m (a + 4) (fun y => if Nat.eqb y s then 0 else if Nat.eqb y d then m d + m s
                                    else if Nat.eqb y t then m t + m s else m y).
Proof.
  intros P a s d t Hs Hs0 Hd0 Ht0 Hsd Hst Hdt. induction n as [| n IH]; intros m En H0.
  - eapply cmp_reach_eq.
    + apply cmp_stp_dec0 with (x := s); [cmp_ins Hs 0 | exact En].
    + intros y. destruct (Nat.eqb_spec y s) as [-> | N1]; [exact En |].
      destruct (Nat.eqb_spec y d); [subst; rewrite En; lia |].
      destruct (Nat.eqb_spec y t); [subst; rewrite En; lia | reflexivity].
  - set (m1 := cmp_upd m s n).
    set (m2 := cmp_upd m1 d (S (m d))).
    set (m3 := cmp_upd m2 t (S (m t))).
    assert (E1 : m1 d = m d) by (unfold m1; apply cmp_upd_other; lia).
    assert (E2 : m2 t = m t) by (unfold m2, m1; rewrite !cmp_upd_other by lia; reflexivity).
    assert (E3 : m3 s = n) by (unfold m3, m2, m1; rewrite !cmp_upd_other by lia; apply cmp_upd_same).
    assert (E30 : m3 0 = 0) by (unfold m3, m2, m1; rewrite !cmp_upd_other by lia; exact H0).
    eapply cmp_reach_trans.
    + apply cmp_stp_decS with (x := s) (j := a + 4) (u := n) (w := m1); [cmp_ins Hs 0 | exact En | intros y; reflexivity].
    + eapply cmp_reach_trans.
      * apply cmp_stp_inc with (x := d) (w := m2); [cmp_ins Hs 1 |]. intros y. unfold m2, cmp_upd. rewrite E1. reflexivity.
      * eapply cmp_reach_trans.
        -- apply cmp_stp_inc with (x := t) (w := m3); [cmp_ins Hs 2 |]. intros y. unfold m3, cmp_upd. rewrite E2. reflexivity.
        -- eapply cmp_reach_trans.
           ++ apply cmp_stp_dec0 with (x := 0) (j := a); [cmp_ins Hs 3 | exact E30].
           ++ eapply cmp_reach_eq; [apply (IH m3 E3 E30) |].
              intros y. unfold m3, m2, m1, cmp_upd. eqb_all.
Qed.

Lemma cmp_blk_copy : forall P a s d t m, (a, cmp_copy a s d t) <sc P -> s <> 0 -> d <> 0 -> t <> 0 ->
  s <> d -> s <> t -> d <> t -> m 0 = 0 -> m t = 0 ->
  cmp_reach P a m (a + 7) (cmp_upd m d (m d + m s)).
Proof.
  intros P a s d t m Hs Hs0 Hd0 Ht0 Hsd Hst Hdt H0 Ht.
  eapply cmp_reach_trans.
  - eapply cmp_loop_copy1; [exact Hs | assumption.. | exact eq_refl | exact H0].
  - set (w1 := fun y => if Nat.eqb y s then 0 else if Nat.eqb y d then m d + m s
                        else if Nat.eqb y t then m t + m s else m y).
    assert (Hw0 : w1 0 = 0).
    { unfold w1. destruct (Nat.eqb_spec 0 s); [lia |]. destruct (Nat.eqb_spec 0 d); [lia |].
      destruct (Nat.eqb_spec 0 t); [lia |]. exact H0. }
    assert (Hs2 : (a + 4, cmp_addmv (a + 4) t s) <sc P).
    { apply cmp_sc_r with (l := [mm_dec s (a + 4); mm_inc d; mm_inc t; mm_dec 0 a]) (a := a); [reflexivity | exact Hs]. }
    replace (a + 7) with (a + 4 + 3) by lia.
    eapply cmp_reach_eq; [apply (cmp_blk_addmv P (a + 4) t s w1 Hs2 Ht0 Hs0 ltac:(auto) Hw0) |].
    intros y. unfold w1, cmp_upd. eqb_all.
Qed.

Lemma cmp_loop_sub : forall P a t u, (a, cmp_sub a t u) <sc P -> t <> 0 -> u <> 0 -> t <> u ->
  forall n m, m u = n -> m 0 = 0 ->
  cmp_reach P a m (a + 3) (fun y => if Nat.eqb y t then m t - m u else if Nat.eqb y u then 0 else m y).
Proof.
  intros P a t u Hs Ht0 Hu0 Htu. induction n as [| n IH]; intros m En H0.
  - eapply cmp_reach_eq.
    + apply cmp_stp_dec0 with (x := u); [cmp_ins Hs 0 | exact En].
    + intros y. destruct (Nat.eqb_spec y t) as [-> | N1]; [rewrite En; lia |].
      destruct (Nat.eqb_spec y u) as [-> | N2]; [exact En | reflexivity].
  - set (m1 := cmp_upd m u n).
    assert (E1 : m1 t = m t) by (unfold m1; apply cmp_upd_other; lia).
    assert (E10 : m1 0 = 0) by (unfold m1; rewrite cmp_upd_other by lia; exact H0).
    assert (E1u : m1 u = n) by (unfold m1; apply cmp_upd_same).
    eapply cmp_reach_trans.
    + apply cmp_stp_decS with (x := u) (j := a + 3) (u := n) (w := m1); [cmp_ins Hs 0 | exact En | intros y; reflexivity].
    + destruct (m t) as [| t1] eqn:Et.
      * eapply cmp_reach_trans.
        -- apply cmp_stp_dec0 with (x := t) (j := a); [cmp_ins Hs 1 | exact E1].
        -- eapply cmp_reach_eq; [apply (IH m1 E1u E10) |].
           intros y. unfold m1, cmp_upd. eqb_all.
      * set (m2 := cmp_upd m1 t t1).
        assert (E2 : m2 u = n) by (unfold m2; rewrite cmp_upd_other by lia; exact E1u).
        assert (E20 : m2 0 = 0) by (unfold m2; rewrite cmp_upd_other by lia; exact E10).
        eapply cmp_reach_trans.
        -- apply cmp_stp_decS with (x := t) (j := a) (u := t1) (w := m2); [cmp_ins Hs 1 | exact E1 | intros y; reflexivity].
        -- eapply cmp_reach_trans.
           ++ apply cmp_stp_dec0 with (x := 0) (j := a); [cmp_ins Hs 2 | exact E20].
           ++ eapply cmp_reach_eq; [apply (IH m2 E2 E20) |].
              intros y. unfold m2, m1, cmp_upd. eqb_all.
Qed.

Lemma cmp_blk_sub : forall P a t u m, (a, cmp_sub a t u) <sc P -> t <> 0 -> u <> 0 -> t <> u -> m 0 = 0 ->
  cmp_reach P a m (a + 3) (fun y => if Nat.eqb y t then m t - m u else if Nat.eqb y u then 0 else m y).
Proof. intros. eapply cmp_loop_sub; eauto. Qed.

Lemma cmp_blk_fin : forall P a t u j m, (a, cmp_fin a t u j) <sc P -> t <> 0 -> u <> 0 -> m 0 = 0 ->
  cmp_reach P a m j (cmp_upd (cmp_upd m u 0) t 0).
Proof.
  intros P a t u j m Hs Ht0 Hu0 H0.
  assert (Hc1 : (a, cmp_clear a u) <sc P) by (apply cmp_sc_l with (r := cmp_clear (a + 2) t ++ [mm_dec 0 j]); exact Hs).
  assert (Hc2 : (a + 2, cmp_clear (a + 2) t) <sc P).
  { apply cmp_sc_l with (r := [mm_dec 0 j]). apply cmp_sc_r with (l := cmp_clear a u) (a := a); [reflexivity | exact Hs]. }
  assert (Hj : (a + 4, [mm_dec 0 j]) <sc P).
  { apply cmp_sc_r with (l := cmp_clear a u ++ cmp_clear (a + 2) t) (a := a); [reflexivity | ].
    rewrite <- app_assoc. exact Hs. }
  eapply cmp_reach_trans; [apply cmp_blk_clear; [exact Hc1 | assumption | exact H0] |].
  eapply cmp_reach_trans.
  - apply cmp_blk_clear; [exact Hc2 | assumption |].
    unfold cmp_upd. destruct (Nat.eqb_spec 0 u); [lia | exact H0].
  - replace (a + 2 + 2) with (a + 4) by lia.
    eapply cmp_reach_eq.
    + apply cmp_stp_dec0 with (x := 0) (j := j); [exact Hj |].
      unfold cmp_upd. destruct (Nat.eqb_spec 0 t); [lia |]. destruct (Nat.eqb_spec 0 u); [lia | exact H0].
    + intros y. reflexivity.
Qed.


Lemma cmp_loop_eq : forall P a t u lt lf, (a, cmp_eqblk a t u lt lf) <sc P -> t <> 0 -> u <> 0 -> t <> u ->
  forall n m, m t = n -> m 0 = 0 ->
  exists w, (forall y, y <> t -> y <> u -> w y = m y) /\
    ((m t = m u /\ cmp_reach P a m (a + 9) w) \/ (m t <> m u /\ cmp_reach P a m (a + 4) w)).
Proof.
  intros P a t u lt lf Hs Ht0 Hu0 Htu. induction n as [| n IH]; intros m En H0.
  - destruct (m u) as [| u1] eqn:Eu.
    + exists m. split; [intros; reflexivity |]. left. split; [lia |].
      eapply cmp_reach_trans.
      * apply cmp_stp_dec0 with (x := t) (j := a + 3); [cmp_ins Hs 0 | exact En].
      * apply cmp_stp_dec0 with (x := u) (j := a + 9); [cmp_ins Hs 3 | exact Eu].
    + set (m1 := cmp_upd m u u1).
      exists m1. split; [intros y N1 N2; unfold m1; rewrite cmp_upd_other by lia; reflexivity |].
      right. split; [lia |].
      eapply cmp_reach_trans.
      * apply cmp_stp_dec0 with (x := t) (j := a + 3); [cmp_ins Hs 0 | exact En].
      * eapply cmp_reach_at; [apply cmp_stp_decS with (x := u) (j := a + 9) (u := u1) (w := m1);
          [cmp_ins Hs 3 | exact Eu | intros y; reflexivity] | lia].
  - set (m1 := cmp_upd m t n).
    assert (E1t : m1 t = n) by (unfold m1; apply cmp_upd_same).
    assert (E1u : m1 u = m u) by (unfold m1; apply cmp_upd_other; lia).
    assert (E10 : m1 0 = 0) by (unfold m1; rewrite cmp_upd_other by lia; exact H0).
    assert (R1 : cmp_reach P a m (S a) m1)
      by (apply cmp_stp_decS with (x := t) (j := a + 3) (u := n) (w := m1); [cmp_ins Hs 0 | exact En | intros y; reflexivity]).
    destruct (m u) as [| u1] eqn:Eu.
    + exists m1. split; [intros y N1 N2; unfold m1; rewrite cmp_upd_other by lia; reflexivity |].
      right. split; [lia |].
      eapply cmp_reach_trans; [exact R1 |].
      apply cmp_stp_dec0 with (x := u) (j := a + 4); [cmp_ins Hs 1 | exact E1u].
    + set (m2 := cmp_upd m1 u u1).
      assert (E2t : m2 t = n) by (unfold m2; rewrite cmp_upd_other by lia; exact E1t).
      assert (E2u : m2 u = u1) by (unfold m2; apply cmp_upd_same).
      assert (E20 : m2 0 = 0) by (unfold m2; rewrite cmp_upd_other by lia; exact E10).
      destruct (IH m2 E2t E20) as (w & Hw & [(Hq & Hr) | (Hq & Hr)]).
      * exists w. split; [intros y N1 N2; rewrite Hw by assumption; unfold m2, m1; rewrite !cmp_upd_other by lia; reflexivity |].
        left. split; [lia |].
        eapply cmp_reach_trans; [exact R1 |].
        eapply cmp_reach_trans.
        -- apply cmp_stp_decS with (x := u) (j := a + 4) (u := u1) (w := m2); [cmp_ins Hs 1 | exact E1u | intros y; reflexivity].
        -- eapply cmp_reach_trans; [apply cmp_stp_dec0 with (x := 0) (j := a); [cmp_ins Hs 2 | exact E20] | exact Hr].
      * exists w. split; [intros y N1 N2; rewrite Hw by assumption; unfold m2, m1; rewrite !cmp_upd_other by lia; reflexivity |].
        right. split; [lia |].
        eapply cmp_reach_trans; [exact R1 |].
        eapply cmp_reach_trans.
        -- apply cmp_stp_decS with (x := u) (j := a + 4) (u := u1) (w := m2); [cmp_ins Hs 1 | exact E1u | intros y; reflexivity].
        -- eapply cmp_reach_trans; [apply cmp_stp_dec0 with (x := 0) (j := a); [cmp_ins Hs 2 | exact E20] | exact Hr].
Qed.

Lemma cmp_blk_eq : forall P a t u lt lf m, (a, cmp_eqblk a t u lt lf) <sc P -> t <> 0 -> u <> 0 -> t <> u -> m 0 = 0 ->
  cmp_reach P a m (if Nat.eqb (m t) (m u) then lt else lf) (cmp_upd (cmp_upd m u 0) t 0).
Proof.
  intros P a t u lt lf m Hs Ht0 Hu0 Htu H0.
  assert (Hf1 : (a + 4, cmp_fin (a + 4) t u lf) <sc P).
  { apply cmp_sc_l with (r := cmp_fin (a + 9) t u lt).
    apply cmp_sc_r with (l := [mm_dec t (a + 3); mm_dec u (a + 4); mm_dec 0 a; mm_dec u (a + 9)]) (a := a); [reflexivity | exact Hs]. }
  assert (Hf2 : (a + 9, cmp_fin (a + 9) t u lt) <sc P).
  { apply cmp_sc_r with (l := cmp_fin (a + 4) t u lf) (a := a + 4); [rewrite cmp_fin_len; lia |].
    apply cmp_sc_r with (l := [mm_dec t (a + 3); mm_dec u (a + 4); mm_dec 0 a; mm_dec u (a + 9)]) (a := a); [reflexivity | exact Hs]. }
  destruct (cmp_loop_eq P a t u lt lf Hs Ht0 Hu0 Htu (m t) m eq_refl H0) as (w & Hw & [(Hq & Hr) | (Hq & Hr)]).
  - assert (Hw0 : w 0 = 0) by (rewrite Hw by lia; exact H0).
    rewrite (proj2 (Nat.eqb_eq _ _) Hq).
    eapply cmp_reach_trans; [exact Hr |].
    eapply cmp_reach_eq; [apply (cmp_blk_fin P (a + 9) t u lt w Hf2 Ht0 Hu0 Hw0) |].
    intros y. unfold cmp_upd. eqb_all. apply Hw; lia.
  - assert (Hw0 : w 0 = 0) by (rewrite Hw by lia; exact H0).
    rewrite (proj2 (Nat.eqb_neq _ _) Hq).
    eapply cmp_reach_trans; [exact Hr |].
    eapply cmp_reach_eq; [apply (cmp_blk_fin P (a + 4) t u lf w Hf1 Ht0 Hu0 Hw0) |].
    intros y. unfold cmp_upd. eqb_all. apply Hw; lia.
Qed.

Lemma cmp_loop_lt : forall P a t u lt lf, (a, cmp_ltblk a t u lt lf) <sc P -> t <> 0 -> u <> 0 -> t <> u ->
  forall n m, m t = n -> m 0 = 0 ->
  exists w, (forall y, y <> t -> y <> u -> w y = m y) /\
    ((m t < m u /\ cmp_reach P a m (a + 4) w) \/ (~ m t < m u /\ cmp_reach P a m (a + 9) w)).
Proof.
  intros P a t u lt lf Hs Ht0 Hu0 Htu. induction n as [| n IH]; intros m En H0.
  - destruct (m u) as [| u1] eqn:Eu.
    + exists m. split; [intros; reflexivity |]. right. split; [lia |].
      eapply cmp_reach_trans.
      * apply cmp_stp_dec0 with (x := t) (j := a + 3); [cmp_ins Hs 0 | exact En].
      * apply cmp_stp_dec0 with (x := u) (j := a + 9); [cmp_ins Hs 3 | exact Eu].
    + set (m1 := cmp_upd m u u1).
      exists m1. split; [intros y N1 N2; unfold m1; rewrite cmp_upd_other by lia; reflexivity |].
      left. split; [lia |].
      eapply cmp_reach_trans.
      * apply cmp_stp_dec0 with (x := t) (j := a + 3); [cmp_ins Hs 0 | exact En].
      * eapply cmp_reach_at; [apply cmp_stp_decS with (x := u) (j := a + 9) (u := u1) (w := m1);
          [cmp_ins Hs 3 | exact Eu | intros y; reflexivity] | lia].
  - set (m1 := cmp_upd m t n).
    assert (E1t : m1 t = n) by (unfold m1; apply cmp_upd_same).
    assert (E1u : m1 u = m u) by (unfold m1; apply cmp_upd_other; lia).
    assert (E10 : m1 0 = 0) by (unfold m1; rewrite cmp_upd_other by lia; exact H0).
    assert (R1 : cmp_reach P a m (S a) m1)
      by (apply cmp_stp_decS with (x := t) (j := a + 3) (u := n) (w := m1); [cmp_ins Hs 0 | exact En | intros y; reflexivity]).
    destruct (m u) as [| u1] eqn:Eu.
    + exists m1. split; [intros y N1 N2; unfold m1; rewrite cmp_upd_other by lia; reflexivity |].
      right. split; [lia |].
      eapply cmp_reach_trans; [exact R1 |].
      apply cmp_stp_dec0 with (x := u) (j := a + 9); [cmp_ins Hs 1 | exact E1u].
    + set (m2 := cmp_upd m1 u u1).
      assert (E2t : m2 t = n) by (unfold m2; rewrite cmp_upd_other by lia; exact E1t).
      assert (E2u : m2 u = u1) by (unfold m2; apply cmp_upd_same).
      assert (E20 : m2 0 = 0) by (unfold m2; rewrite cmp_upd_other by lia; exact E10).
      destruct (IH m2 E2t E20) as (w & Hw & [(Hq & Hr) | (Hq & Hr)]).
      * exists w. split; [intros y N1 N2; rewrite Hw by assumption; unfold m2, m1; rewrite !cmp_upd_other by lia; reflexivity |].
        left. split; [lia |].
        eapply cmp_reach_trans; [exact R1 |].
        eapply cmp_reach_trans.
        -- apply cmp_stp_decS with (x := u) (j := a + 9) (u := u1) (w := m2); [cmp_ins Hs 1 | exact E1u | intros y; reflexivity].
        -- eapply cmp_reach_trans; [apply cmp_stp_dec0 with (x := 0) (j := a); [cmp_ins Hs 2 | exact E20] | exact Hr].
      * exists w. split; [intros y N1 N2; rewrite Hw by assumption; unfold m2, m1; rewrite !cmp_upd_other by lia; reflexivity |].
        right. split; [lia |].
        eapply cmp_reach_trans; [exact R1 |].
        eapply cmp_reach_trans.
        -- apply cmp_stp_decS with (x := u) (j := a + 9) (u := u1) (w := m2); [cmp_ins Hs 1 | exact E1u | intros y; reflexivity].
        -- eapply cmp_reach_trans; [apply cmp_stp_dec0 with (x := 0) (j := a); [cmp_ins Hs 2 | exact E20] | exact Hr].
Qed.

Lemma cmp_blk_lt : forall P a t u lt lf m, (a, cmp_ltblk a t u lt lf) <sc P -> t <> 0 -> u <> 0 -> t <> u -> m 0 = 0 ->
  cmp_reach P a m (if Nat.ltb (m t) (m u) then lt else lf) (cmp_upd (cmp_upd m u 0) t 0).
Proof.
  intros P a t u lt lf m Hs Ht0 Hu0 Htu H0.
  assert (Hf1 : (a + 4, cmp_fin (a + 4) t u lt) <sc P).
  { apply cmp_sc_l with (r := cmp_fin (a + 9) t u lf).
    apply cmp_sc_r with (l := [mm_dec t (a + 3); mm_dec u (a + 9); mm_dec 0 a; mm_dec u (a + 9)]) (a := a); [reflexivity | exact Hs]. }
  assert (Hf2 : (a + 9, cmp_fin (a + 9) t u lf) <sc P).
  { apply cmp_sc_r with (l := cmp_fin (a + 4) t u lt) (a := a + 4); [rewrite cmp_fin_len; lia |].
    apply cmp_sc_r with (l := [mm_dec t (a + 3); mm_dec u (a + 9); mm_dec 0 a; mm_dec u (a + 9)]) (a := a); [reflexivity | exact Hs]. }
  destruct (cmp_loop_lt P a t u lt lf Hs Ht0 Hu0 Htu (m t) m eq_refl H0) as (w & Hw & [(Hq & Hr) | (Hq & Hr)]).
  - assert (Hw0 : w 0 = 0) by (rewrite Hw by lia; exact H0).
    rewrite (proj2 (Nat.ltb_lt _ _) Hq).
    eapply cmp_reach_trans; [exact Hr |].
    eapply cmp_reach_eq; [apply (cmp_blk_fin P (a + 4) t u lt w Hf1 Ht0 Hu0 Hw0) |].
    intros y. unfold cmp_upd. eqb_all. apply Hw; lia.
  - assert (Hw0 : w 0 = 0) by (rewrite Hw by lia; exact H0).
    rewrite (proj2 (Nat.ltb_nlt _ _) Hq).
    eapply cmp_reach_trans; [exact Hr |].
    eapply cmp_reach_eq; [apply (cmp_blk_fin P (a + 9) t u lf w Hf2 Ht0 Hu0 Hw0) |].
    intros y. unfold cmp_upd. eqb_all. apply Hw; lia.
Qed.
