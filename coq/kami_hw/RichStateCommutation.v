(** RichStateCommutation.v — Commutation lemmas between bounded-table
    operations in kami_step and graph operations in SimulationProof.vm_apply.

    These lemmas are the proof backbone for extending embed_step to all 47
    opcodes (M4 in UNIFICATION_ROADMAP.md).

    STATUS: Zero Admitted.

    Organization:
    1. Generic helpers for filtermap / graph_lookup_modules interaction
    2. Partition table commutation: snap_pt_to_graph commutes with
       graph_hw_psplit / graph_hw_pmerge
    3. Morphism table commutation: snapshot_morphisms_of_rich_state
       commutes with rich_state_add_morph / rich_state_delete_morph
    4. kami_step invariants *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

Require Import Kernel.VMState.
Require Import Kernel.VMStep.
Require Import Kernel.MuCostModel.
Import VMStep.VMStep.
Require Import KamiHW.Abstraction.

(* ====================================================================== *)
(** * 0. Generic helpers                                                   *)
(* ====================================================================== *)

(** filtermap extensionality: pointwise-equal functions give equal results. *)
Lemma filtermap_ext :
    forall {A B : Type} (f g : A -> option B) (l : list A),
      (forall x, In x l -> f x = g x) ->
      filtermap f l = filtermap g l.
Proof.
  intros A B f g l Hext.
  induction l as [|a xs IH].
  - reflexivity.
  - simpl. rewrite Hext by (left; reflexivity).
    destruct (g a); [f_equal|]; apply IH;
    intros x Hx; apply Hext; right; exact Hx.
Qed.

(** If [mid] is not in the input list, lookup in the filtermap returns None. *)
Lemma graph_lookup_modules_filtermap_not_in :
    forall (f : nat -> option ModuleState) (l : list nat) (mid : nat),
      ~ In mid l ->
      graph_lookup_modules
        (filtermap
           (fun i => match f i with
                     | None => None
                     | Some v => Some (i, v)
                     end) l) mid = None.
Proof.
  intros f l mid Hni.
  induction l as [|a xs IH].
  - reflexivity.
  - simpl. assert (Hne : a <> mid) by (intro; apply Hni; left; auto).
    assert (Hni' : ~ In mid xs) by (intro; apply Hni; right; auto).
    destruct (f a) eqn:Efa.
    + simpl. destruct (Nat.eqb a mid) eqn:E.
      * apply Nat.eqb_eq in E. congruence.
      * apply IH. exact Hni'.
    + apply IH. exact Hni'.
Qed.

(** For NoDup lists, lookup in the filtermap returns exactly [f mid]. *)
Lemma graph_lookup_modules_filtermap_in :
    forall (f : nat -> option ModuleState) (l : list nat) (mid : nat),
      NoDup l -> In mid l ->
      graph_lookup_modules
        (filtermap
           (fun i => match f i with
                     | None => None
                     | Some v => Some (i, v)
                     end) l) mid = f mid.
Proof.
  intros f l mid Hnd Hin.
  induction l as [|a xs IH].
  - inversion Hin.
  - inversion Hnd as [|? ? Hna Hnd']; subst.
    destruct Hin as [Heq | Hin'].
    + subst a. destruct (f mid) eqn:Efm.
      * simpl. rewrite Efm. simpl. rewrite Nat.eqb_refl. reflexivity.
      * simpl. rewrite Efm.
        apply graph_lookup_modules_filtermap_not_in. exact Hna.
    + simpl. destruct (f a) eqn:Efa.
      * simpl. destruct (Nat.eqb a mid) eqn:E.
        -- apply Nat.eqb_eq in E. subst. contradiction.
        -- apply IH; assumption.
      * apply IH; assumption.
Qed.

(** One step of filtermap unfolding (avoids [simpl] expanding Nat.eqb). *)
Lemma filtermap_cons_eq {A B : Type} (fn : A -> option B) (a : A) (xs : list A) :
  filtermap fn (a :: xs) =
  match fn a with None => filtermap fn xs | Some b => b :: filtermap fn xs end.
Proof. reflexivity. Qed.

(** One step of graph_remove_modules unfolding. *)
Lemma grm_cons_eq (id : nat) (m : ModuleState) (rest : list (nat * ModuleState)) (mid : nat) :
  graph_remove_modules ((id, m) :: rest) mid =
  if Nat.eqb id mid then Some (rest, m)
  else match graph_remove_modules rest mid with
       | None => None
       | Some (rest', removed) => Some ((id, m) :: rest', removed)
       end.
Proof. reflexivity. Qed.

(** graph_remove_modules on a filtermap list with NoDup. *)
Lemma graph_remove_modules_filtermap :
    forall (f : nat -> option ModuleState) (l : list nat)
           (mid : nat) (v : ModuleState),
      NoDup l -> In mid l -> f mid = Some v ->
      graph_remove_modules
        (filtermap
           (fun i => match f i with
                     | None => None
                     | Some v => Some (i, v)
                     end) l) mid =
      Some (filtermap
              (fun i => if Nat.eqb i mid then None
                        else match f i with
                             | None => None
                             | Some v => Some (i, v)
                             end) l,
            v).
Proof.
  intros f l mid v Hnd Hin Hfm.
  induction l as [|a xs IH].
  - inversion Hin.
  - inversion Hnd as [|? ? Hna Hnd']; subst.
    rewrite !filtermap_cons_eq.
    destruct Hin as [Heq | Hin'].
    + (* a = mid *)
      subst a. rewrite Hfm. rewrite Nat.eqb_refl.
      rewrite grm_cons_eq. rewrite Nat.eqb_refl.
      f_equal. f_equal.
      apply filtermap_ext. intros x Hx.
      destruct (Nat.eqb x mid) eqn:E.
      * apply Nat.eqb_eq in E. subst. contradiction.
      * reflexivity.
    + (* In mid xs *)
      assert (Hne : a <> mid) by (intro; subst; contradiction).
      assert (Eam : Nat.eqb a mid = false) by (apply Nat.eqb_neq; auto).
      destruct (f a) eqn:Efa.
      * (* f a = Some m0 *)
        rewrite Eam.
        rewrite grm_cons_eq. rewrite Eam.
        rewrite (IH Hnd' Hin'). reflexivity.
      * (* f a = None *)
        rewrite Eam.
        apply IH; assumption.
Qed.

(** Shorthand for the module constructor used by snap_pt_to_graph. *)
Definition pt_module (sz : nat) : ModuleState :=
  {| module_region := List.seq 0 sz;
     module_axioms := [];
     module_mu_tensor := module_mu_tensor_default |}.

(** The snap_pt_to_graph filtermap in generic form. *)
Lemma snap_pt_filtermap_compat :
    forall (sizes : nat -> nat) (i : nat),
      (if Nat.eqb (sizes i) 0 then None
       else Some (i, pt_module (sizes i))) =
      match (if Nat.eqb (sizes i) 0 then None else Some (pt_module (sizes i))) with
      | None => None
      | Some v => Some (i, v)
      end.
Proof. intros. destruct (Nat.eqb (sizes i) 0); reflexivity. Qed.

(** Extract snap_pt_to_graph modules into generic form. *)
Lemma snap_pt_modules_generic :
    forall (next_id : nat) (sizes : nat -> nat),
      (snap_pt_to_graph next_id sizes).(pg_modules) =
      filtermap
        (fun i => match (if Nat.eqb (sizes i) 0 then None
                         else Some (pt_module (sizes i))) with
                  | None => None
                  | Some v => Some (i, v)
                  end)
        (List.rev (List.seq 0 next_id)).
Proof.
  intros. unfold snap_pt_to_graph. simpl.
  apply filtermap_ext. intros x _.
  destruct (Nat.eqb (sizes x) 0); reflexivity.
Qed.

(** normalize_module on pt_module is the identity. *)
Lemma normalize_module_pt_module : forall n,
  normalize_module (mk_module_state (List.seq 0 n) []) = pt_module n.
Proof.
  intro n. unfold normalize_module, mk_module_state, pt_module. simpl.
  f_equal. unfold normalize_region.
  apply nodup_fixed_point. apply seq_NoDup.
Qed.

(* ====================================================================== *)
(** * 1. Partition table commutation                                       *)
(* ====================================================================== *)

(** graph_module_size on snap_pt_to_graph yields sizes mid. *)
Lemma snap_pt_to_graph_module_size :
    forall (next_id : nat) (sizes : nat -> nat) (mid : nat),
      mid < next_id ->
      graph_module_size (snap_pt_to_graph next_id sizes) mid = sizes mid.
Proof.
  intros next_id sizes mid Hlt.
  unfold graph_module_size, graph_lookup.
  rewrite snap_pt_modules_generic.
  rewrite graph_lookup_modules_filtermap_in.
  - destruct (Nat.eqb (sizes mid) 0) eqn:E.
    + apply Nat.eqb_eq in E. simpl. rewrite E. reflexivity.
    + simpl. unfold pt_module. simpl. apply seq_length.
  - apply NoDup_rev. apply seq_NoDup.
  - rewrite <- in_rev. apply in_seq. lia.
Qed.

(** graph_remove on snap_pt_to_graph extracts the module for mid. *)
Lemma snap_pt_graph_remove :
    forall (next_id : nat) (sizes : nat -> nat) (mid : nat),
      mid < next_id ->
      sizes mid > 0 ->
      graph_remove (snap_pt_to_graph next_id sizes) mid =
      Some ({| pg_next_id := next_id;
               pg_modules :=
                 filtermap
                   (fun i => if Nat.eqb (sizes i) 0 then None
                             else if Nat.eqb i mid then None
                             else Some (i, pt_module (sizes i)))
                   (List.rev (List.seq 0 next_id));
               pg_next_morph_id := 1;
               pg_morphisms := [] |},
            pt_module (sizes mid)).
Proof.
  intros next_id sizes mid Hlt Hgt.
  unfold graph_remove.
  rewrite snap_pt_modules_generic.
  rewrite graph_remove_modules_filtermap with (v := pt_module (sizes mid)).
  - simpl. f_equal. f_equal. f_equal.
    apply filtermap_ext. intros x _.
    destruct (Nat.eqb x mid) eqn:E.
    + destruct (Nat.eqb (sizes x) 0); reflexivity.
    + symmetry. apply snap_pt_filtermap_compat.
  - apply NoDup_rev. apply seq_NoDup.
  - rewrite <- in_rev. apply in_seq. lia.
  - destruct (Nat.eqb (sizes mid) 0) eqn:E.
    + apply Nat.eqb_eq in E. lia.
    + reflexivity.
Qed.

(** graph_hw_psplit on snap_pt_to_graph. *)
Theorem snap_pt_to_graph_psplit :
    forall (next_id : nat) (sizes : nat -> nat) (mid : nat),
      next_id >= 1 ->
      S (S next_id) <= 64 ->
      mid < next_id ->
      sizes mid >= 2 ->
      sizes next_id = 0 ->
      sizes (S next_id) = 0 ->
      graph_hw_psplit (snap_pt_to_graph next_id sizes) mid =
      snap_pt_to_graph (S (S next_id))
        (fun j => if Nat.eqb j mid then 0
                  else if Nat.eqb j next_id then Nat.div (sizes mid) 2
                  else if Nat.eqb j (S next_id) then sizes mid - Nat.div (sizes mid) 2
                  else sizes j).
Proof.
  Local Arguments Nat.eqb : simpl never.
  Local Arguments Nat.div : simpl never.
  Local Arguments Nat.divmod : simpl never.
  intros next_id sizes mid Hge Hle Hlt Hgt Hn0 Hsn0.
  assert (Hdiv_pos : Nat.div (sizes mid) 2 > 0) by (apply Nat.div_str_pos; lia).
  assert (Hrem_pos : sizes mid - Nat.div (sizes mid) 2 > 0).
  { assert (Nat.div (sizes mid) 2 < sizes mid) by (apply Nat.div_lt; lia). lia. }
  unfold graph_hw_psplit.
  rewrite snap_pt_to_graph_module_size by lia.
  rewrite snap_pt_graph_remove by lia. simpl.
  unfold graph_add_module. simpl.
  rewrite normalize_module_pt_module.
  rewrite normalize_module_pt_module.
  unfold snap_pt_to_graph.
  f_equal; try (simpl; reflexivity); try (simpl; lia).
  replace (List.seq 0 (S (S next_id)))
    with (List.seq 0 next_id ++ [next_id; S next_id]).
  2:{ replace (S (S next_id)) with (next_id + 2) by lia.
      rewrite seq_app. simpl. repeat rewrite Nat.add_0_r. reflexivity. }
  rewrite rev_app_distr. simpl.
  (* S next_id entry *)
  rewrite (Nat.eqb_sym (S next_id) mid).
  destruct (Nat.eqb mid (S next_id)) eqn:Emid1.
  { apply Nat.eqb_eq in Emid1. lia. }
  simpl.
  rewrite (Nat.eqb_sym (S next_id) next_id).
  assert (HnSn: (next_id =? S next_id) = false) by (apply Nat.eqb_neq; lia).
  rewrite HnSn. simpl.
  rewrite Nat.eqb_refl. simpl.
  assert (Herz: sizes mid - Nat.div (sizes mid) 2 > 0).
  { assert (Nat.div (sizes mid) 2 < sizes mid) by (apply Nat.div_lt; lia). lia. }
  assert (Herz_neq: (sizes mid - Nat.div (sizes mid) 2 =? 0) = false)
    by (apply Nat.eqb_neq; lia).
  rewrite Herz_neq. simpl. f_equal.
  (* next_id entry *)
  rewrite (Nat.eqb_sym next_id mid).
  destruct (Nat.eqb mid next_id) eqn:Emid2.
  { apply Nat.eqb_eq in Emid2. lia. }
  simpl. rewrite Nat.eqb_refl. simpl.
  assert (Elz_neq: (Nat.div (sizes mid) 2 =? 0) = false) by (apply Nat.eqb_neq; lia).
  rewrite Elz_neq. simpl. f_equal.
  apply filtermap_ext. intros x Hx.
  apply in_rev in Hx. apply in_seq in Hx.
  destruct (Nat.eqb x mid) eqn:Exm.
  - apply Nat.eqb_eq in Exm. subst.
    rewrite Nat.eqb_refl. simpl.
    destruct (sizes mid =? 0); reflexivity.
  - destruct (Nat.eqb (sizes x) 0) eqn:Esz.
    + (* sizes x = 0 *)
      simpl.
      assert (Exn: (x =? next_id) = false) by (apply Nat.eqb_neq; intro; subst; lia).
      assert (ExSn: (x =? S next_id) = false) by (apply Nat.eqb_neq; intro; subst; lia).
      rewrite Exn. simpl. rewrite ExSn. simpl.
      apply Nat.eqb_eq in Esz. rewrite Esz. simpl. reflexivity.
    + (* sizes x > 0 *)
      simpl.
      assert (Exn: (x =? next_id) = false) by (apply Nat.eqb_neq; intro; subst; lia).
      assert (ExSn: (x =? S next_id) = false) by (apply Nat.eqb_neq; intro; subst; lia).
      rewrite Exn. simpl. rewrite ExSn. simpl. rewrite Esz. simpl. reflexivity.
Qed.

(** graph_hw_pmerge on snap_pt_to_graph. *)
Theorem snap_pt_to_graph_pmerge :
    forall (next_id : nat) (sizes : nat -> nat) (m1 m2 : nat),
      next_id >= 1 ->
      S next_id <= 64 ->
      m1 < next_id ->
      m2 < next_id ->
      m1 <> m2 ->
      sizes m1 > 0 ->
      sizes m2 > 0 ->
      sizes next_id = 0 ->
      graph_hw_pmerge (snap_pt_to_graph next_id sizes) m1 m2 =
      snap_pt_to_graph (S next_id)
        (fun j => if Nat.eqb j m1 then 0
                  else if Nat.eqb j m2 then 0
                  else if Nat.eqb j next_id then sizes m1 + sizes m2
                  else sizes j).
Proof.
  intros next_id sizes m1 m2 Hge Hle Hlt1 Hlt2 Hne Hgt1 Hgt2 Hn0.
  unfold graph_hw_pmerge.
  rewrite !snap_pt_to_graph_module_size by lia.
  rewrite snap_pt_graph_remove by lia. simpl.
  (* graph_remove of m2 from the m1-removed graph *)
  assert (Hrem2 :
    graph_remove
      {| pg_next_id := next_id;
         pg_modules := filtermap (fun i =>
           if Nat.eqb (sizes i) 0 then None
           else if Nat.eqb i m1 then None
           else Some (i, pt_module (sizes i)))
           (rev (seq 0 next_id));
         pg_next_morph_id := 1;
         pg_morphisms := [] |} m2 =
    Some ({| pg_next_id := next_id;
             pg_modules := filtermap (fun i =>
               if Nat.eqb (sizes i) 0 then None
               else if Nat.eqb i m1 then None
               else if Nat.eqb i m2 then None
               else Some (i, pt_module (sizes i)))
               (rev (seq 0 next_id));
             pg_next_morph_id := 1;
             pg_morphisms := [] |},
          pt_module (sizes m2))).
  { unfold graph_remove. simpl.
    assert (Hconv :
      graph_remove_modules
        (filtermap (fun i =>
           if Nat.eqb (sizes i) 0 then None
           else if Nat.eqb i m1 then None
           else Some (i, pt_module (sizes i)))
          (rev (seq 0 next_id))) m2 =
      graph_remove_modules
        (filtermap (fun i => match (if Nat.eqb (sizes i) 0 then None
                                    else if Nat.eqb i m1 then None
                                    else Some (pt_module (sizes i))) with
                             | None => None
                             | Some v => Some (i, v)
                             end)
          (rev (seq 0 next_id))) m2).
    { f_equal. apply filtermap_ext. intros x _.
      destruct (Nat.eqb (sizes x) 0); [reflexivity|].
      destruct (Nat.eqb x m1); reflexivity. }
    rewrite Hconv.
    rewrite graph_remove_modules_filtermap with (v := pt_module (sizes m2)).
    - simpl. f_equal. f_equal. f_equal.
      apply filtermap_ext. intros x _.
      destruct (Nat.eqb x m2) eqn:E2.
      * destruct (Nat.eqb (sizes x) 0); [reflexivity|].
        destruct (Nat.eqb x m1); reflexivity.
      * destruct (Nat.eqb (sizes x) 0); [reflexivity|].
      destruct (Nat.eqb x m1); reflexivity.
    - apply NoDup_rev. apply seq_NoDup.
    - rewrite <- in_rev. apply in_seq. lia.
    - destruct (Nat.eqb (sizes m2) 0) eqn:E.
      + apply Nat.eqb_eq in E. lia.
      + destruct (Nat.eqb m2 m1) eqn:E2.
        * apply Nat.eqb_eq in E2. congruence.
        * reflexivity. }
  rewrite Hrem2. simpl.
  unfold graph_add_module. simpl.
  rewrite normalize_module_pt_module.
  Local Arguments Nat.eqb : simpl never.
  Local Arguments Nat.div : simpl never.
  unfold snap_pt_to_graph.
  f_equal; try (simpl; reflexivity); try (simpl; lia).
  replace (List.seq 0 (S next_id))
    with (List.seq 0 next_id ++ [next_id]).
  2:{ replace (S next_id) with (next_id + 1) by lia.
      rewrite seq_app. simpl. reflexivity. }
  rewrite rev_app_distr. simpl.
  rewrite (Nat.eqb_sym next_id m1).
  destruct (Nat.eqb m1 next_id) eqn:Em1n.
  { apply Nat.eqb_eq in Em1n. lia. }
  simpl.
  rewrite (Nat.eqb_sym next_id m2).
  destruct (Nat.eqb m2 next_id) eqn:Em2n.
  { apply Nat.eqb_eq in Em2n. lia. }
  simpl.
  rewrite Nat.eqb_refl. simpl.
  assert (Emsz_neq: (sizes m1 + sizes m2 =? 0) = false)
    by (apply Nat.eqb_neq; lia).
  rewrite Emsz_neq. simpl. f_equal.
  apply filtermap_ext. intros x Hx.
  apply in_rev in Hx. apply in_seq in Hx.
  destruct (Nat.eqb x m1) eqn:Em1.
  - apply Nat.eqb_eq in Em1. subst. rewrite Nat.eqb_refl.
    cbv beta iota. destruct (Nat.eqb (sizes m1) 0); reflexivity.
  - destruct (Nat.eqb x m2) eqn:Em2.
    + apply Nat.eqb_eq in Em2. subst. cbv beta iota.
      rewrite Nat.eqb_refl. cbv beta iota.
      destruct (Nat.eqb (sizes m2) 0); reflexivity.
    + assert (Exn: (x =? next_id) = false) by (apply Nat.eqb_neq; intro; subst; lia).
      destruct (Nat.eqb (sizes x) 0) eqn:Esz.
      * cbv beta iota. rewrite Exn. cbv beta iota.
        apply Nat.eqb_eq in Esz. rewrite Esz. rewrite Nat.eqb_refl.
        cbv beta iota. reflexivity.
      * cbv beta iota. rewrite Exn. cbv beta iota. rewrite Esz.
        cbv beta iota. reflexivity.
Qed.

(* ====================================================================== *)
(** * 2. Morphism table commutation                                        *)
(* ====================================================================== *)

(* Reset simpl behavior that may have leaked from pmerge proof *)
#[global] Arguments Nat.eqb : simpl nomatch.
#[global] Arguments Nat.div : simpl nomatch.

(** After rich_state_add_morph, snapshot_morphisms_of_rich_state
    prepends the new entry. *)
Lemma morph_add_commutation :
    forall (rs : RichSnapshotState) (src dst coupling_desc : nat) (is_id : bool),
      let '(rs', new_id) := rich_state_add_morph rs src dst coupling_desc is_id in
      snapshot_morphisms_of_rich_state rs' =
      (new_id,
       {| morph_source := src;
          morph_target := dst;
          morph_coupling :=
            normalize_coupling
              {| coupling_pairs :=
                   snapshot_coupling_pairs_from_desc rs coupling_desc;
                 coupling_label := coupling_label empty_coupling_data |};
          morph_is_identity := is_id |})
      :: snapshot_morphisms_of_rich_state rs.
Proof.
  intros rs src dst coupling_desc is_id.
  unfold rich_state_add_morph.
  set (n := rich_next_morph_id rs).
  unfold snapshot_morphisms_of_rich_state at 1. simpl.
  replace (List.seq 0 (n + 1)) with (List.seq 0 n ++ [n]).
  2:{ rewrite seq_app. simpl. reflexivity. }
  rewrite rev_app_distr. simpl.
  rewrite Nat.eqb_refl. simpl.
  f_equal.
  unfold snapshot_morphisms_of_rich_state.
  apply filtermap_ext. intros x Hx.
  apply in_rev in Hx. apply in_seq in Hx.
  destruct (Nat.eqb x n) eqn:E.
  + apply Nat.eqb_eq in E. lia.
  + simpl. destruct (rich_morph_table rs x) eqn:Erm; [|reflexivity].
    reflexivity.
Qed.

(** After rich_state_delete_morph, snapshot_morphisms_of_rich_state
    is the original list filtered to exclude mid. *)
Lemma morph_delete_commutation :
    forall (rs : RichSnapshotState) (mid : nat),
      snapshot_morphisms_of_rich_state (rich_state_delete_morph rs mid) =
      filter (fun entry => negb (Nat.eqb (fst entry) mid))
             (snapshot_morphisms_of_rich_state rs).
Proof.
  intros rs mid.
  unfold snapshot_morphisms_of_rich_state. simpl.
  set (l := List.rev (List.seq 0 (rich_next_morph_id rs))).
  clearbody l.
  induction l as [|a xs IH].
  - reflexivity.
  - simpl.
    destruct (Nat.eqb a mid) eqn:Eam.
    + apply Nat.eqb_eq in Eam. subst a. simpl.
      destruct (rich_morph_table rs mid) eqn:Erm.
      * simpl. rewrite Nat.eqb_refl. simpl. apply IH.
      * apply IH.
    + simpl. destruct (rich_morph_table rs a) eqn:Erm.
      * simpl. rewrite Eam. simpl. f_equal; apply IH.
      * apply IH.
Qed.

(** If rich_morph_table has an entry for mid, so does graph_lookup_morphism
    on snap_full_graph. *)
Lemma morph_lookup_commutation :
    forall (ks : KamiSnapshot) (mid : nat),
      mid < rich_next_morph_id (snap_rich_state ks) ->
      (snap_rich_state ks).(rich_morph_table) mid <> None ->
      graph_lookup_morphism (snap_full_graph ks) mid <> None.
Proof.
  intros ks mid Hlt Hne.
  unfold graph_lookup_morphism, snap_full_graph. simpl.
  unfold snapshot_morphisms_of_rich_state.
  set (rs := snap_rich_state ks).
  fold rs in Hne. fold rs in Hlt.
  set (l := List.rev (List.seq 0 (rich_next_morph_id rs))).
  assert (HnoDup : NoDup l) by (subst l; apply NoDup_rev; apply seq_NoDup).
  assert (Hin : In mid l).
  { subst l. rewrite <- in_rev. apply in_seq. subst rs. lia. }
  clearbody l rs.
  induction l as [|a xs IH].
  - inversion Hin.
  - inversion HnoDup as [|? ? Hna Hnd']; subst.
    destruct Hin as [Heq | Hin'].
    + subst a. simpl.
      destruct (rich_morph_table rs mid) eqn:Erm.
      * simpl. rewrite Nat.eqb_refl. discriminate.
      * exfalso. exact (Hne eq_refl).
    + simpl. destruct (rich_morph_table rs a) eqn:Erm.
      * simpl. destruct (Nat.eqb a mid) eqn:E.
        -- apply Nat.eqb_eq in E. subst. contradiction.
        -- apply IH; assumption.
      * apply IH; assumption.
Qed.

(** Selector values match between rich-state entries and
    graph-reconstructed morphisms. *)
Lemma morph_get_selector_commutation :
    forall (entry : MorphTableEntry) (selector : nat),
      let ms := {| morph_source := morph_entry_source entry;
                   morph_target := morph_entry_target entry;
                   morph_coupling :=
                     normalize_coupling empty_coupling_data;
                   morph_is_identity := morph_entry_is_identity entry |} in
      morphism_selector_value ms selector =
      match selector with
      | 0 => morph_entry_source entry
      | 1 => morph_entry_target entry
      | 2 => List.length (normalize_coupling empty_coupling_data).(coupling_pairs)
      | 3 => if morph_entry_is_identity entry then 1 else 0
      | _ => 0
      end.
Proof.
  intros entry selector ms.
  unfold ms, morphism_selector_value.
  destruct selector as [|[|[|[|n]]]]; simpl; reflexivity.
Qed.

(* ====================================================================== *)
(** * 3. kami_step preserves graph-relevant invariants                      *)
(* ====================================================================== *)

(** Non-partition opcodes preserve the partition table. *)
Lemma kami_step_preserves_pt :
    forall (ks : KamiSnapshot) (i : vm_instruction),
      match i with
      | instr_pnew _ _ | instr_psplit _ _ _ _ | instr_pmerge _ _ _ => False
      | _ => True
      end ->
      snap_pt_sizes (kami_step ks i) = snap_pt_sizes ks /\
      snap_pt_next_id (kami_step ks i) = snap_pt_next_id ks.
Proof.
  intros ks i Hnon_pt.
  destruct i; try contradiction; simpl;
  try (unfold kami_advance_default; simpl; split; reflexivity);
  try (unfold kami_advance_reg; simpl; split; reflexivity);
  try (unfold kami_advance_rich_morph; simpl; split; reflexivity);
  try (unfold kami_advance_rich_noret; simpl; split; reflexivity);
  try (unfold kami_advance_err; simpl; split; reflexivity);
  try (unfold kami_advance_cert_addr; simpl; split; reflexivity);
  try (simpl; split; reflexivity).
  - repeat match goal with |- context [match ?x with _ => _ end] =>
      destruct x end; simpl; split; reflexivity.
  - repeat match goal with |- context [match ?x with _ => _ end] =>
      destruct x end; simpl;
    try (unfold kami_advance_rich_morph; simpl; split; reflexivity);
    try (unfold kami_advance_err; simpl; split; reflexivity).
  - repeat match goal with |- context [match ?x with _ => _ end] =>
      destruct x end; simpl;
    try (unfold kami_advance_rich_morph; simpl; split; reflexivity);
    try (unfold kami_advance_err; simpl; split; reflexivity).
  - repeat match goal with |- context [match ?x with _ => _ end] =>
      destruct x end; simpl;
    try (unfold kami_advance_rich_morph; simpl; split; reflexivity);
    try (unfold kami_advance_err; simpl; split; reflexivity).
  - destruct (rich_morph_table _ _);
    [ unfold kami_advance_rich_noret; simpl; split; reflexivity
    | unfold kami_advance_err; simpl; split; reflexivity ].
  - destruct (rich_morph_table _ _);
    [ unfold kami_advance_cert_addr; simpl; split; reflexivity
    | unfold kami_advance_err; simpl; split; reflexivity ].
  - repeat match goal with |- context [match ?x with _ => _ end] =>
      destruct x end; simpl;
    try (unfold kami_advance_rich_morph; simpl; split; reflexivity);
    try (unfold kami_advance_err; simpl; split; reflexivity).
  - repeat match goal with |- context [match ?x with _ => _ end] =>
      destruct x end; simpl;
    try (unfold kami_advance_reg; simpl; split; reflexivity);
    try (unfold kami_advance_err; simpl; split; reflexivity).
Qed.
