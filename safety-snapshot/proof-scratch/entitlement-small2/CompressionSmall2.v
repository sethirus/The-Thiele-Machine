(** CompressionSmall2.v: how much a permanent record costs, and which flips
    a finite machine is forced to pay for. VM-free.

    FragmentSmall.v shows that on a finite machine a record no move revokes
    is switched on only by a move that merges states, and that charging every
    merge gives the toll. This file carries that in two directions, as the
    big build's PermanentRecordPricing.v did, on the model and with the
    eight-state fragment as the instance.

    How much. Landauer's principle as a counting premise
    [ent2_compression_priced]: a move of cost c sends any duplicate-free list
    of n states onto at least n / 2^c distinct states. Under it, switching k
    states on while m are already on costs at least log2 ((m + k) / m)
    [ent2_flips_compression_bound, ent2_flips_log_bound]. With k = 1 this is
    the toll again [ent2_a2_from_compression]. New here: the premise is
    exactly "no fibre of a move is bigger than 2^cost"
    [ent2_compression_priced_iff_fibres], so for the eight-state fragment it
    is a theorem [ent2_frag_compression_priced], the fragment's price is the
    least that satisfies it [ent2_frag_cost_minimal], and the bound is met
    with equality by the fragment's stamp [ent2_frag_bound_attained]. The
    whole small machine is not compression-priced, whatever its decision
    procedure for equality [ent2_small_not_compression_priced]: a free
    branch merges two full states.

    Which flips. Fix a finite machine and one move. A move that switches the
    reading on somewhere either merges two states or switches the reading
    off somewhere else [ent2_flip_merges_or_revokes]; a flip that forgets
    nothing is paid for by a revocation [ent2_injective_flip_revokes]; the
    move is charged at least 1 by every cost assignment that prices merges
    exactly when it merges [ent2_forced_priced_iff_merges]; a move that
    never revokes and switches the reading on is therefore forced to be
    priced [ent2_permanent_flip_forced]. The converse is false: a
    three-state machine has a forced price and no permanent record
    [ent2_forced_without_permanent].

    Scope. The pricing premise stands for Landauer's principle and is a
    named premise, not a theorem about heat. It is a statement about finite
    machines; the small machine as a whole is not one.

    Dependencies: Coq standard library, ThieleComplete.v, EntitlementSmall.v
    and FragmentSmall.v. No axioms, no Admitted.                          *)

From Coq Require Import List Bool Arith Lia.
From Coq Require Import Logic.FinFun.
Import ListNotations.
Require Import Minimal.ThieleComplete.
Require Import Minimal.EntitlementSmall.
Require Import Minimal.FragmentSmall.
Require Minimal.EarnedCore.
Module E := Minimal.EarnedCore.

(* Duplicate-free concatenation of lists with no common member. *)
Lemma ent2_nodup_app_disjoint : forall (A : Type) (l l' : list A),
  NoDup l -> NoDup l' -> (forall a, In a l -> ~ In a l') -> NoDup (l ++ l').
Proof.
  intros A l l' Hl Hl' Hdisj. induction l as [| x xs IH]; simpl.
  - exact Hl'.
  - inversion Hl as [| ? ? Hnotin Hxs]; subst.
    constructor.
    + intro Hin. apply in_app_or in Hin as [Hin | Hin].
      * exact (Hnotin Hin).
      * exact (Hdisj x (or_introl eq_refl) Hin).
    + apply IH; [exact Hxs |]. intros a Ha. apply Hdisj. right. exact Ha.
Qed.

(* ================================================================= *)
(* 1. How much a permanent record costs.                              *)
(* ================================================================= *)

Section Quantitative.

Variables (St Mv : Type).
Variable step : St -> Mv -> St.
Variable flag : St -> bool.
Variable cost : Mv -> nat.
Variable eq_dec : forall a b : St, {a = b} + {a <> b}.

(* The number of distinct states a move sends a list to. *)
Definition ent2_image_size (m : Mv) (D : list St) : nat :=
  length (nodup eq_dec (map (fun t => step t m) D)).

(* Landauer's principle as a counting premise: each unit of cost pays for
   at most one halving of the number of distinct states. *)
Definition ent2_compression_priced : Prop :=
  forall m D, NoDup D -> length D <= 2 ^ cost m * ent2_image_size m D.

(* Switching k distinct states on, with m states already on, costs enough
   that m + k <= 2^cost * m. *)
Theorem ent2_flips_compression_bound :
  forall all m F,
    frag_finite St all ->
    frag_permanent St Mv step flag ->
    ent2_compression_priced ->
    NoDup F ->
    (forall s, In s F -> flag s = false /\ flag (step s m) = true) ->
    length F + length (frag_up St flag all) <= 2 ^ cost m * length (frag_up St flag all).
Proof.
  intros all m F Hfin Hperm Hprice HndF HF.
  set (C := frag_up St flag all).
  assert (HndC : NoDup C) by (apply NoDup_filter, (proj1 Hfin)).
  assert (HinC : forall t, In t C <-> flag t = true) by (apply frag_up_spec; exact Hfin).
  assert (Hnd : NoDup (F ++ C)).
  { apply ent2_nodup_app_disjoint; [exact HndF | exact HndC |].
    intros a HaF HaC. apply HinC in HaC.
    destruct (HF a HaF) as [Ha _]. rewrite Ha in HaC. discriminate. }
  assert (Himg : incl (nodup eq_dec (map (fun t => step t m) (F ++ C))) C).
  { intros y Hy. apply nodup_In in Hy.
    apply in_map_iff in Hy as [x [<- Hx]].
    apply HinC. apply in_app_or in Hx as [HxF | HxC].
    - apply HF. exact HxF.
    - apply Hperm. apply HinC. exact HxC. }
  assert (Hle : ent2_image_size m (F ++ C) <= length C).
  { apply NoDup_incl_length; [apply NoDup_nodup | exact Himg]. }
  pose proof (Hprice m (F ++ C) Hnd) as Hc.
  rewrite app_length in Hc.
  apply Nat.le_trans with (m := 2 ^ cost m * ent2_image_size m (F ++ C));
    [exact Hc | apply Nat.mul_le_mono_l; exact Hle].
Qed.

(* A flip means at least one state is on. *)
Lemma ent2_flip_gives_state : forall (all : list St) s m,
  frag_finite St all -> flag (step s m) = true -> 0 < length (frag_up St flag all).
Proof.
  intros all s m Hfin Hflip.
  assert (Hin : In (step s m) (frag_up St flag all))
    by (apply (frag_up_spec St flag all Hfin); exact Hflip).
  destruct (frag_up St flag all); [contradiction | simpl; lia].
Qed.

(* The same bound in rounded base-2 logarithms. *)
Theorem ent2_flips_log_bound :
  forall (all : list St) s m F,
    frag_finite St all ->
    frag_permanent St Mv step flag ->
    ent2_compression_priced ->
    flag (step s m) = true ->
    NoDup F ->
    (forall t, In t F -> flag t = false /\ flag (step t m) = true) ->
    Nat.log2_up (length (frag_up St flag all) + length F)
      <= cost m + Nat.log2_up (length (frag_up St flag all)).
Proof.
  intros all s m F Hfin Hperm Hprice Hs HndF HF.
  set (n := length (frag_up St flag all)).
  assert (Hn : 0 < n) by (eapply ent2_flip_gives_state; eauto).
  pose proof (ent2_flips_compression_bound all m F Hfin Hperm Hprice HndF HF) as Hb.
  fold n in Hb.
  rewrite <- Nat.log2_up_mul_pow2 by lia.
  apply Nat.log2_up_le_mono. rewrite Nat.mul_comm. lia.
Qed.

(* With one flipped state the bound is the toll. *)
Theorem ent2_a2_from_compression :
  forall all : list St,
    frag_finite St all ->
    frag_permanent St Mv step flag ->
    ent2_compression_priced ->
    frag_toll St Mv step flag cost.
Proof.
  intros all Hfin Hperm Hprice s m Hs Hflip.
  assert (Hn : 0 < length (frag_up St flag all)) by (eapply ent2_flip_gives_state; eauto).
  assert (Hb := ent2_flips_compression_bound all m [s] Hfin Hperm Hprice
                  (NoDup_cons s (fun H : In s [] => H) (NoDup_nil St))).
  assert (HF : forall t, In t [s] -> flag t = false /\ flag (step t m) = true).
  { intros t [<- | []]. split; assumption. }
  specialize (Hb HF). simpl length in Hb.
  destruct (cost m) as [| c]; [simpl in Hb; lia | lia].
Qed.

(* ---- The premise is exactly a bound on fibres ---- *)

(* The fibre of y under m: the states m sends to y. *)
Definition ent2_fibre_eq (all : list St) (m : Mv) (y : St) : list St :=
  filter (fun x => if eq_dec (step x m) y then true else false) all.

Definition ent2_eqb (a b : St) : bool := if eq_dec a b then true else false.

Lemma ent2_eqb_spec : forall a b, ent2_eqb a b = true <-> a = b.
Proof. intros a b. unfold ent2_eqb. destruct (eq_dec a b); split; intro H; auto; discriminate. Qed.

Lemma ent2_filter_nodup_le : forall {A : Type} (p : A -> bool) (D all : list A),
  NoDup D -> incl D all -> length (filter p D) <= length (filter p all).
Proof.
  intros A p D all Hnd Hin.
  apply NoDup_incl_length; [apply NoDup_filter, Hnd |].
  intros x Hx. apply filter_In in Hx as [Hx1 Hx2]. apply filter_In. split; auto.
Qed.

Theorem ent2_compression_priced_iff_fibres : forall all,
  frag_finite St all ->
  (ent2_compression_priced <->
   forall m y, length (ent2_fibre_eq all m y) <= 2 ^ cost m).
Proof.
  intros all [Hnd Hall]. split.
  - intros Hprice m y.
    pose proof (Hprice m (ent2_fibre_eq all m y) (NoDup_filter _ Hnd)) as H.
    assert (Himg : ent2_image_size m (ent2_fibre_eq all m y) <= 1).
    { unfold ent2_image_size.
      change 1 with (length [y]).
      apply NoDup_incl_length; [apply NoDup_nodup |].
      intros z Hz. apply nodup_In in Hz. apply in_map_iff in Hz as [x [<- Hx]].
      unfold ent2_fibre_eq in Hx. apply filter_In in Hx as [_ Hx].
      destruct (eq_dec (step x m) y) as [E | _]; [| discriminate].
      rewrite E. left. reflexivity. }
    assert (Hm : 2 ^ cost m * ent2_image_size m (ent2_fibre_eq all m y) <= 2 ^ cost m * 1)
      by (apply Nat.mul_le_mono_l; exact Himg).
    lia.
  - intros Hfib m D HD. unfold ent2_image_size.
    set (imgs := nodup eq_dec (map (fun t => step t m) D)).
    assert (Hcount : length D <= 2 ^ cost m * length imgs).
    { apply (ent_fibres_count ent2_eqb ent2_eqb_spec (fun x => step x m) (2 ^ cost m) imgs D).
      - intros x Hx. unfold imgs. apply nodup_In. apply (in_map (fun t => step t m)). exact Hx.
      - intros x Hx.
        eapply Nat.le_trans.
        + apply (ent2_filter_nodup_le (fun y => ent2_eqb (step y m) (step x m)) D all HD).
          intros z _. apply Hall.
        + change (length (ent2_fibre_eq all m (step x m)) <= 2 ^ cost m). apply Hfib. }
    exact Hcount.
Qed.

End Quantitative.

(* The Landauer premise forces merges to be priced: a move that merges two
   states is charged at least 1. *)
Lemma ent2_compression_merges_priced :
  forall (St Mv : Type) (step : St -> Mv -> St) (cost : Mv -> nat)
         (eq_dec : forall a b : St, {a = b} + {a <> b}),
    ent2_compression_priced St Mv step cost eq_dec ->
    forall m a b, a <> b -> step a m = step b m -> cost m >= 1.
Proof.
  intros St Mv step cost eq_dec Hprice m a b Hab Heq.
  assert (Hnd : NoDup [a; b]).
  { constructor; [intros [H | []]; exact (Hab (eq_sym H)) |]. constructor; [intros []| constructor]. }
  pose proof (Hprice m [a; b] Hnd) as H. unfold ent2_image_size in H. simpl in H.
  rewrite <- Heq in H.
  destruct (eq_dec (step a m) (step a m)) as [_ | Hn]; [| exfalso; apply Hn; reflexivity].
  simpl in H. destruct (cost m); simpl in H; lia.
Qed.

(* ================================================================= *)
(* 2. The eight-state fragment is an instance.                        *)
(* ================================================================= *)

Definition ent2_frag_eq_dec : forall a b : frag_fstate, {a = b} + {a <> b}.
Proof. intros [p c] [q d]. decide equality; [apply Bool.bool_dec | decide equality]. Defined.

Lemma ent2_frag_eqb_agree : forall a b,
  frag_fstate_eqb a b = ent2_eqb frag_fstate ent2_frag_eq_dec a b.
Proof.
  intros [p c] [q d]. unfold frag_fstate_eqb, ent2_eqb. simpl.
  destruct (ent2_frag_eq_dec (p, c) (q, d)) as [E | N].
  - inversion E. subst. destruct q, d; reflexivity.
  - destruct p, q, c, d; simpl; try reflexivity; exfalso; apply N; reflexivity.
Qed.

Lemma ent2_frag_fibre_agree : forall m y,
  frag_fibre m y = ent2_fibre_eq frag_fstate frag_move frag_step ent2_frag_eq_dec frag_all m y.
Proof.
  intros m y. unfold frag_fibre, ent2_fibre_eq. apply filter_ext.
  intro x. rewrite ent2_frag_eqb_agree. unfold ent2_eqb. reflexivity.
Qed.

(* Every premise of the Landauer route is a theorem on the eight states. *)
Theorem ent2_frag_compression_priced :
  ent2_compression_priced frag_fstate frag_move frag_step frag_cost ent2_frag_eq_dec.
Proof.
  apply (ent2_compression_priced_iff_fibres frag_fstate frag_move frag_step frag_cost
           ent2_frag_eq_dec frag_all frag_fin_finite).
  intros m y. rewrite <- ent2_frag_fibre_agree. exact (proj1 (frag_price_is_squeeze m) y).
Qed.

(* The toll on the fragment, a second time, by the Landauer route. *)
Theorem ent2_frag_toll_by_compression :
  frag_toll frag_fstate frag_move frag_step frag_flag frag_cost.
Proof.
  exact (ent2_a2_from_compression frag_fstate frag_move frag_step frag_flag frag_cost
           ent2_frag_eq_dec frag_all frag_fin_finite frag_fin_permanent
           ent2_frag_compression_priced).
Qed.

(* The fragment's price is the least one that meets the premise: every
   compression-priced cost assignment charges each move at least what the
   fragment charges. *)
Theorem ent2_frag_cost_minimal : forall cost' : frag_move -> nat,
  ent2_compression_priced frag_fstate frag_move frag_step cost' ent2_frag_eq_dec ->
  forall m, frag_cost m <= cost' m.
Proof.
  intros cost' Hprice m.
  pose proof (proj1 (ent2_compression_priced_iff_fibres frag_fstate frag_move frag_step cost'
                       ent2_frag_eq_dec frag_all frag_fin_finite) Hprice) as Hf.
  destruct (proj2 (frag_price_is_squeeze m)) as [y Hy].
  specialize (Hf m y). rewrite <- ent2_frag_fibre_agree, Hy in Hf.
  destruct (Nat.le_gt_cases (frag_cost m) (cost' m)) as [H | H]; [exact H |].
  exfalso. assert (2 ^ cost' m < 2 ^ frag_cost m) by (apply Nat.pow_lt_mono_r; lia). lia.
Qed.

(* The bound is met with equality. Four states are off; the stamp switches
   all four on and four are already on. So 4 + 4 <= 2^1 * 4, with no slack:
   a squeeze of 8 states onto 4 pays exactly one halving. *)
Definition ent2_blank_slots : list frag_fstate :=
  [(FS0, false); (FS1, false); (FS2, false); (FS3, false)].

Theorem ent2_frag_bound_attained :
  NoDup ent2_blank_slots /\
  (forall s, In s ent2_blank_slots -> frag_flag s = false /\ frag_flag (frag_step s FStamp) = true) /\
  length ent2_blank_slots + length (frag_up frag_fstate frag_flag frag_all)
    = 2 ^ frag_cost FStamp * length (frag_up frag_fstate frag_flag frag_all).
Proof.
  split; [repeat constructor; simpl; intuition discriminate |].
  split.
  - intros s Hs. simpl in Hs. destruct Hs as [<- | [<- | [<- | [<- | []]]]]; split; reflexivity.
  - vm_compute. reflexivity.
Qed.

(* The whole small machine is not compression-priced, whichever way its
   equality is decided: DEC A 2 sends two different full states to the same
   state and is charged 0. *)
Theorem ent2_small_not_compression_priced :
  forall eq_dec : forall a b : E.state, {a = b} + {a <> b},
    ~ ent2_compression_priced E.state E.instr E.exec E.cost eq_dec.
Proof.
  intros eq_dec Hprice.
  set (a := E.mkst (E.mkcore 0 0 1 0 1 [] None false) 0 false).
  set (b := E.mkst (E.mkcore 1 0 0 0 1 [] None false) 0 false).
  assert (Hab : a <> b) by (intro H; apply (f_equal (fun s => E.ca (E.core_of s))) in H;
                            simpl in H; discriminate).
  assert (Heq : E.exec a (E.DEC E.CA 2) = E.exec b (E.DEC E.CA 2)) by reflexivity.
  pose proof (ent2_compression_merges_priced E.state E.instr E.exec E.cost eq_dec Hprice
                (E.DEC E.CA 2) a b Hab Heq) as H.
  vm_compute in H. lia.
Qed.

(* The trace floor from the Landauer premise: a certification system on any
   finite machine whose merges are priced by compression. *)
Definition ent2_cert_system_from_compression
    (St Mv : Type) (step : St -> Mv -> St) (flag : St -> bool) (cost : Mv -> nat)
    (eq_dec : forall a b : St, {a = b} + {a <> b}) (all : list St)
    (Hfin : frag_finite St all) (Hperm : frag_permanent St Mv step flag)
    (Hprice : ent2_compression_priced St Mv step cost eq_dec) : CertificationSystem :=
  mk_cert_system St Mv step cost flag
    (fun s m H0 H1 => ent2_a2_from_compression St Mv step flag cost eq_dec all
                        Hfin Hperm Hprice s m H0 H1).

Theorem ent2_compression_trace_floor :
  forall (St Mv : Type) (step : St -> Mv -> St) (flag : St -> bool) (cost : Mv -> nat)
         (eq_dec : forall a b : St, {a = b} + {a <> b}) (all : list St)
         (Hfin : frag_finite St all) (Hperm : frag_permanent St Mv step flag)
         (Hprice : ent2_compression_priced St Mv step cost eq_dec)
         (tr : list Mv) (s0 : St),
    flag s0 = false ->
    flag (ent_cs_run (ent2_cert_system_from_compression St Mv step flag cost eq_dec all
                        Hfin Hperm Hprice) tr s0) = true ->
    ent_cs_bill (ent2_cert_system_from_compression St Mv step flag cost eq_dec all
                   Hfin Hperm Hprice) tr >= 1.
Proof.
  intros St Mv step flag cost eq_dec all Hfin Hperm Hprice tr s0 H0 H1.
  destruct (ent_cs_raising_step (ent2_cert_system_from_compression St Mv step flag cost eq_dec all
                                   Hfin Hperm Hprice) tr s0 H0 H1)
    as [pre [i [post [Htr [_ [_ Hc]]]]]].
  rewrite Htr. clear H1 Htr. induction pre as [| j pre IH]; simpl in *; lia.
Qed.

(* ================================================================= *)
(* 3. Which flips a finite machine must pay for.                      *)
(* ================================================================= *)

Section Characterization.

Variables (St Mv : Type).
Variable step : St -> Mv -> St.
Variable flag : St -> bool.

(* The move m never switches the reading off. *)
Definition ent2_permanent_at (m : Mv) : Prop :=
  forall s, flag s = true -> flag (step s m) = true.

(* Permanence under the one flipping move is enough for the merge. *)
Theorem ent2_flip_merges_at :
  forall (all : list St) s m,
    frag_finite St all -> ent2_permanent_at m ->
    flag s = false -> flag (step s m) = true ->
    ~ frag_injective St Mv step m.
Proof.
  intros all s m Hfin Hperm Hs Hflip Hinj.
  set (L := frag_up St flag all). set (f := fun t => step t m).
  assert (HndL : NoDup L) by (apply NoDup_filter, (proj1 Hfin)).
  assert (HndM : NoDup (map f L)).
  { apply Injective_map_NoDup; [| exact HndL]. intros a b Hab. apply Hinj. exact Hab. }
  assert (Hincl : incl (map f L) L).
  { intros y Hy. apply in_map_iff in Hy as [x [<- Hx]].
    apply (frag_up_spec St flag all Hfin). apply (frag_up_spec St flag all Hfin) in Hx.
    apply Hperm, Hx. }
  assert (Hback : incl L (map f L)).
  { apply NoDup_length_incl; [exact HndM | rewrite map_length; lia | exact Hincl]. }
  assert (Hfs : In (f s) (map f L)) by (apply Hback, (frag_up_spec St flag all Hfin), Hflip).
  apply in_map_iff in Hfs as [c [Hc HcL]].
  apply Hinj in Hc. subst c. apply (frag_up_spec St flag all Hfin) in HcL. congruence.
Qed.

(* Merge or revoke. A flipping move either merges two states or switches the
   reading off somewhere. *)
Theorem ent2_flip_merges_or_revokes :
  forall (all : list St) s m,
    frag_finite St all -> flag s = false -> flag (step s m) = true ->
    ~ frag_injective St Mv step m \/ exists t, flag t = true /\ flag (step t m) = false.
Proof.
  intros all s m Hfin Hs Hflip.
  set (L := frag_up St flag all).
  assert (HinL : forall t, In t L <-> flag t = true) by (apply frag_up_spec; exact Hfin).
  destruct (existsb (fun t => negb (flag (step t m))) L) eqn:Hsearch.
  - right. apply existsb_exists in Hsearch as [t [Ht Hneg]].
    exists t. split; [apply HinL; exact Ht |]. apply negb_true_iff. exact Hneg.
  - left. apply (ent2_flip_merges_at all s m Hfin); auto.
    intros t Ht.
    destruct (flag (step t m)) eqn:Hstep; [reflexivity |].
    exfalso.
    assert (Hex : existsb (fun t => negb (flag (step t m))) L = true).
    { apply existsb_exists. exists t. split; [apply HinL; exact Ht | rewrite Hstep; reflexivity]. }
    rewrite Hex in Hsearch. discriminate.
Qed.

(* A flip that forgets nothing is paid for by a revocation. *)
Corollary ent2_injective_flip_revokes :
  forall (all : list St) s m,
    frag_finite St all -> frag_injective St Mv step m ->
    flag s = false -> flag (step s m) = true ->
    exists t, flag t = true /\ flag (step t m) = false.
Proof.
  intros all s m Hfin Hinj Hs Hflip.
  destruct (ent2_flip_merges_or_revokes all s m Hfin Hs Hflip) as [Hm | Hr];
    [contradiction | exact Hr].
Qed.

(* A move is forced to be priced when every cost assignment that prices
   merges charges it at least one. *)
Definition ent2_forced_priced (m : Mv) : Prop :=
  forall cost : Mv -> nat, frag_merges_priced St Mv step cost -> cost m >= 1.

Variable mv_eq_dec : forall a b : Mv, {a = b} + {a <> b}.

(* Forced price is exactly merging. *)
Theorem ent2_forced_priced_iff_merges :
  forall m, ent2_forced_priced m <-> ~ frag_injective St Mv step m.
Proof.
  intro m. split.
  - intros Hforced Hinj.
    set (free_m := fun j => if mv_eq_dec j m then 0 else 1).
    assert (Hpriced : frag_merges_priced St Mv step free_m).
    { intros j Hj. unfold free_m.
      destruct (mv_eq_dec j m) as [-> | Hne].
      - exfalso. exact (Hj Hinj).
      - unfold ge. apply le_n. }
    specialize (Hforced free_m Hpriced). unfold free_m in Hforced.
    destruct (mv_eq_dec m m) as [_ | Hne]; [inversion Hforced | apply Hne; reflexivity].
  - intros Hmerge cost Hprice. exact (Hprice m Hmerge).
Qed.

(* A move that writes a permanent record is forced to be priced. *)
Corollary ent2_permanent_flip_forced :
  forall (all : list St) s m,
    frag_finite St all -> ent2_permanent_at m ->
    flag s = false -> flag (step s m) = true ->
    ent2_forced_priced m.
Proof.
  intros all s m Hfin Hperm Hs Hflip.
  apply ent2_forced_priced_iff_merges.
  eapply ent2_flip_merges_at; eauto.
Qed.

End Characterization.

(* The inclusion is strict. Three states: T0 and T2 unmarked, T1 marked. The
   one move sends T0 to T1 (a flip), T1 to T2 (a revocation) and T2 to T1
   (merging T0 and T2). Every cost assignment that prices merges charges it,
   and it writes no permanent record. *)
Inductive ent2_tri : Type := ET0 | ET1 | ET2.

Definition ent2_tri_mark (x : ent2_tri) : bool :=
  match x with ET1 => true | _ => false end.

Definition ent2_tri_step (x : ent2_tri) (_ : unit) : ent2_tri :=
  match x with ET0 => ET1 | ET1 => ET2 | ET2 => ET1 end.

Theorem ent2_forced_without_permanent :
  frag_finite ent2_tri [ET0; ET1; ET2] /\
  ent2_tri_mark ET0 = false /\ ent2_tri_mark (ent2_tri_step ET0 tt) = true /\
  ~ ent2_permanent_at ent2_tri unit ent2_tri_step ent2_tri_mark tt /\
  ent2_forced_priced ent2_tri unit ent2_tri_step tt.
Proof.
  split; [| split; [reflexivity | split; [reflexivity | split]]].
  - split.
    + repeat constructor; simpl; intuition discriminate.
    + intro x. destruct x; simpl; auto.
  - intro Hperm. specialize (Hperm ET1 eq_refl). discriminate.
  - intros cost Hprice. apply Hprice.
    intro Hinj. specialize (Hinj ET0 ET2 eq_refl). discriminate.
Qed.

(* ================================================================= *)
(* Assumption audit.                                                  *)
(* ================================================================= *)

Print Assumptions ent2_flips_compression_bound.
Print Assumptions ent2_flips_log_bound.
Print Assumptions ent2_a2_from_compression.
Print Assumptions ent2_compression_priced_iff_fibres.
Print Assumptions ent2_compression_merges_priced.
Print Assumptions ent2_frag_compression_priced.
Print Assumptions ent2_frag_toll_by_compression.
Print Assumptions ent2_frag_cost_minimal.
Print Assumptions ent2_frag_bound_attained.
Print Assumptions ent2_small_not_compression_priced.
Print Assumptions ent2_cert_system_from_compression.
Print Assumptions ent2_compression_trace_floor.
Print Assumptions ent2_flip_merges_at.
Print Assumptions ent2_flip_merges_or_revokes.
Print Assumptions ent2_injective_flip_revokes.
Print Assumptions ent2_forced_priced_iff_merges.
Print Assumptions ent2_permanent_flip_forced.
Print Assumptions ent2_forced_without_permanent.
