(** RichStateCommutation: bounded-table commutation lemmas for the Kami abstraction

   This file proves the lookup and update lemmas needed to line up the rich
   Kami snapshot tables with the graph operations performed by vm_apply. It is
   infrastructure for the embed-step story, not a standalone semantic claim.

   The organization is simple: generic filtermap helpers first, then the
   partition-table commutation facts, then the morphism-table commutation
   facts, and finally the invariants needed by the step-level bridge.
*)

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

Require Import Kernel.VMState.
Require Import Kernel.VMStep.
Require Import Kernel.MuCostModel.
Import VMStep.VMStep.
Require Import KamiHW.Abstraction.
From KamiHW Require Import ThieleTypes.

(* *)
(** 0. Generic helpers                                                   *)
(* *)

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

(** A filtermap whose function drops the results [p] rejects is the filter of
    the original filtermap. *)
Lemma filtermap_filter :
    forall {A B : Type} (f f' : A -> option B) (p : B -> bool) (l : list A),
      (forall x, f' x = match f x with
                        | Some y => if p y then Some y else None
                        | None => None
                        end) ->
      filtermap f' l = filter p (filtermap f l).
Proof.
  intros A B f f' p l H. induction l as [|x l IH]; [reflexivity|].
  cbn [filtermap]. rewrite H. destruct (f x) as [y|]; [|exact IH].
  destruct (p y) eqn:Hp; cbn [filter]; rewrite Hp; [cbn; rewrite IH; reflexivity | exact IH].
Qed.

Lemma filter_ext_in :
    forall {A : Type} (p q : A -> bool) (l : list A),
      (forall x, In x l -> p x = q x) -> filter p l = filter q l.
Proof.
  intros A p q l H. induction l as [|x l IH]; [reflexivity|].
  cbn [filter]. rewrite (H x (or_introl eq_refl)).
  destruct (q x); [f_equal|]; apply IH; intros y Hy; apply H; right; exact Hy.
Qed.

(** A morphism survives the removal of modules [m1] and [m2] when neither is
    its source or target. *)
Definition morph_keep (m1 m2 : nat) (p : MorphismID * MorphismState) : bool :=
  negb (orb (orb (Nat.eqb (morph_source (snd p)) m1) (Nat.eqb (morph_target (snd p)) m1))
            (orb (Nat.eqb (morph_source (snd p)) m2) (Nat.eqb (morph_target (snd p)) m2))).

(** [rich_state_cascade] removes exactly the morphisms [graph_cascade_delete_morphisms]
    removes from the reconstructed morphism list. *)
Lemma snapshot_morphisms_cascade : forall rs m1 m2,
  snapshot_morphisms_of_rich_state (rich_state_cascade rs m1 m2) =
  filter (morph_keep m1 m2) (snapshot_morphisms_of_rich_state rs).
Proof.
  intros rs m1 m2. unfold snapshot_morphisms_of_rich_state.
  cbn [rich_state_cascade rich_morph_table rich_next_morph_id rich_coupling_desc_table
       rich_coupling_pair_table rich_next_coupling_pair_id].
  apply filtermap_filter. intro i.
  destruct (rich_morph_table rs i) as [e|]; [|reflexivity].
  unfold morph_keep. cbn [snd morph_source morph_target].
  destruct (Nat.eqb (morph_entry_source e) m1), (Nat.eqb (morph_entry_target e) m1),
           (Nat.eqb (morph_entry_source e) m2), (Nat.eqb (morph_entry_target e) m2);
    reflexivity.
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

(** Shorthand for the module constructor used by snap_pt_to_graph: the
    module owning the range [List.seq b sz]. *)
Definition pt_module (b sz : nat) : ModuleState :=
  {| module_region := List.seq b sz;
     module_axioms := [];
     module_mu_tensor := module_mu_tensor_default |}.

(** The snap_pt_to_graph filtermap in generic form. *)
Lemma snap_pt_filtermap_compat :
    forall (sizes bases : nat -> nat) (i : nat),
      (if Nat.eqb (sizes i) 0 then None
       else Some (i, pt_module (bases i) (sizes i))) =
      match (if Nat.eqb (sizes i) 0 then None
             else Some (pt_module (bases i) (sizes i))) with
      | None => None
      | Some v => Some (i, v)
      end.
Proof. intros. destruct (Nat.eqb (sizes i) 0); reflexivity. Qed.

(** Extract snap_pt_to_graph modules into generic form. *)
Lemma snap_pt_modules_generic :
    forall (next_id : nat) (sizes bases : nat -> nat),
      (snap_pt_to_graph next_id sizes bases).(pg_modules) =
      filtermap
        (fun i => match (if Nat.eqb (sizes i) 0 then None
                         else Some (pt_module (bases i) (sizes i))) with
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
Lemma normalize_module_pt_module : forall b n,
  normalize_module (mk_module_state (List.seq b n) []) = pt_module b n.
Proof.
  intros b n. unfold normalize_module, mk_module_state, pt_module. simpl.
  f_equal. unfold normalize_region.
  apply nodup_fixed_point. apply seq_NoDup.
Qed.

(* *)
(** 1. Partition table commutation                                       *)
(* *)

(** graph_lookup on snap_pt_to_graph reads the slot. *)
Lemma snap_pt_to_graph_lookup :
    forall (next_id : nat) (sizes bases : nat -> nat) (mid : nat),
      mid < next_id ->
      graph_lookup (snap_pt_to_graph next_id sizes bases) mid =
      (if Nat.eqb (sizes mid) 0 then None else Some (pt_module (bases mid) (sizes mid))).
Proof.
  intros next_id sizes bases mid Hlt.
  unfold graph_lookup. rewrite snap_pt_modules_generic.
  apply graph_lookup_modules_filtermap_in.
  - apply NoDup_rev. apply seq_NoDup.
  - rewrite <- in_rev. apply in_seq. lia.
Qed.

(** graph_module_size on snap_pt_to_graph yields sizes mid. *)
Lemma snap_pt_to_graph_module_size :
    forall (next_id : nat) (sizes bases : nat -> nat) (mid : nat),
      mid < next_id ->
      graph_module_size (snap_pt_to_graph next_id sizes bases) mid = sizes mid.
Proof.
  intros next_id sizes bases mid Hlt.
  unfold graph_module_size. rewrite snap_pt_to_graph_lookup by exact Hlt.
  destruct (Nat.eqb (sizes mid) 0) eqn:E.
  - apply Nat.eqb_eq in E. symmetry. exact E.
  - unfold pt_module. cbn [module_region]. apply seq_length.
Qed.

(** graph_module_region on snap_pt_to_graph yields the slot's range. *)
Lemma snap_pt_to_graph_module_region :
    forall (next_id : nat) (sizes bases : nat -> nat) (mid : nat),
      mid < next_id ->
      graph_module_region (snap_pt_to_graph next_id sizes bases) mid =
      List.seq (bases mid) (sizes mid).
Proof.
  intros next_id sizes bases mid Hlt.
  unfold graph_module_region. rewrite snap_pt_to_graph_lookup by exact Hlt.
  destruct (Nat.eqb (sizes mid) 0) eqn:E.
  - apply Nat.eqb_eq in E. rewrite E. reflexivity.
  - reflexivity.
Qed.

(** graph_remove on snap_pt_to_graph extracts the module for mid. *)
Lemma snap_pt_graph_remove :
    forall (next_id : nat) (sizes bases : nat -> nat) (mid : nat),
      mid < next_id ->
      sizes mid > 0 ->
      graph_remove (snap_pt_to_graph next_id sizes bases) mid =
      Some ({| pg_next_id := next_id;
               pg_modules :=
                 filtermap
                   (fun i => if Nat.eqb (sizes i) 0 then None
                             else if Nat.eqb i mid then None
                             else Some (i, pt_module (bases i) (sizes i)))
                   (List.rev (List.seq 0 next_id));
               pg_next_morph_id := 1;
               pg_morphisms := [] |},
            pt_module (bases mid) (sizes mid)).
Proof.
  intros next_id sizes bases mid Hlt Hgt.
  unfold graph_remove.
  rewrite snap_pt_modules_generic.
  rewrite graph_remove_modules_filtermap with (v := pt_module (bases mid) (sizes mid)).
  - simpl. f_equal. f_equal. f_equal.
    apply filtermap_ext. intros x _.
    destruct (Nat.eqb x mid) eqn:E.
    + destruct (Nat.eqb (sizes x) 0); reflexivity.
    + destruct (Nat.eqb (sizes x) 0); reflexivity.
  - apply NoDup_rev. apply seq_NoDup.
  - rewrite <- in_rev. apply in_seq. lia.
  - destruct (Nat.eqb (sizes mid) 0) eqn:E.
    + apply Nat.eqb_eq in E. lia.
    + reflexivity.
Qed.

(** The reconstruction as a record literal. *)
Lemma snap_pt_to_graph_eta : forall next_id sizes bases,
  snap_pt_to_graph next_id sizes bases =
  {| pg_next_id := next_id;
     pg_modules := filtermap (pt_module_at sizes bases) (List.rev (List.seq 0 next_id));
     pg_next_morph_id := 1;
     pg_morphisms := [] |}.
Proof. reflexivity. Qed.

(** A graph with no morphisms is its own cascade delete. *)
Lemma snap_pt_to_graph_cascade : forall next_id sizes bases mid,
  graph_cascade_delete_morphisms (snap_pt_to_graph next_id sizes bases) mid =
  snap_pt_to_graph next_id sizes bases.
Proof. reflexivity. Qed.

(** The two-slot extension of the reconstruction: slots [n] and [S n] are
    the newest, so they head the module list. *)
Lemma snap_pt_to_graph_modules_SS : forall n sizes bases,
  pg_modules (snap_pt_to_graph (S (S n)) sizes bases) =
  match pt_module_at sizes bases (S n) with Some p => [p] | None => [] end ++
  match pt_module_at sizes bases n with Some p => [p] | None => [] end ++
  filtermap (pt_module_at sizes bases) (List.rev (List.seq 0 n)).
Proof.
  intros n sizes bases. rewrite snap_pt_to_graph_modules.
  replace (List.seq 0 (S (S n))) with (List.seq 0 n ++ [n; S n]).
  2:{ replace (S (S n)) with (n + 2) by lia. rewrite seq_app. reflexivity. }
  rewrite rev_app_distr. cbn [List.rev List.app].
  cbn [filtermap].
  destruct (pt_module_at sizes bases (S n)); destruct (pt_module_at sizes bases n); reflexivity.
Qed.

Lemma snap_pt_to_graph_modules_S : forall n sizes bases,
  pg_modules (snap_pt_to_graph (S n) sizes bases) =
  match pt_module_at sizes bases n with Some p => [p] | None => [] end ++
  filtermap (pt_module_at sizes bases) (List.rev (List.seq 0 n)).
Proof.
  intros n sizes bases. rewrite snap_pt_to_graph_modules.
  rewrite rev_seq_succ. cbn [List.app filtermap].
  destruct (pt_module_at sizes bases n); reflexivity.
Qed.

(** graph_hw_psplit on snap_pt_to_graph: the module's range is cut at its
    middle into two new slots, the left half at the old base and the right
    half where the left one ends. *)
Theorem snap_pt_to_graph_psplit :
    forall (next_id : nat) (sizes bases : nat -> nat) (mid : nat),
      next_id >= 1 ->
      S (S next_id) <= PTableSz ->
      mid < next_id ->
      sizes mid >= 2 ->
      sizes next_id = 0 ->
      sizes (S next_id) = 0 ->
      graph_hw_psplit (snap_pt_to_graph next_id sizes bases) mid =
      snap_pt_to_graph (S (S next_id))
        (fun j => if Nat.eqb j mid then 0
                  else if Nat.eqb j next_id then Nat.div (sizes mid) 2
                  else if Nat.eqb j (S next_id) then sizes mid - Nat.div (sizes mid) 2
                  else sizes j)
        (fun j => if Nat.eqb j mid then 0
                  else if Nat.eqb j next_id then bases mid
                  else if Nat.eqb j (S next_id) then bases mid + Nat.div (sizes mid) 2
                  else bases j).
Proof.
  intros next_id sizes bases mid Hge Hle Hlt Hgt Hn0 Hsn0.
  assert (Hdiv_pos : Nat.div (sizes mid) 2 > 0) by (apply Nat.div_str_pos; lia).
  assert (Hrem_pos : sizes mid - Nat.div (sizes mid) 2 > 0).
  { assert (Nat.div (sizes mid) 2 < sizes mid) by (apply Nat.div_lt; lia). lia. }
  unfold graph_hw_psplit. cbv zeta.
  rewrite snap_pt_to_graph_cascade.
  rewrite snap_pt_to_graph_module_region by exact Hlt.
  rewrite normalize_seq_nodups.
  destruct (psplit_halves_of_range (bases mid) (sizes mid)) as [HL HR].
  rewrite HL, HR.
  rewrite snap_pt_graph_remove by lia.
  unfold graph_add_module. cbn [fst snd pg_next_id pg_modules pg_next_morph_id pg_morphisms].
  rewrite !normalize_module_pt_module.
  rewrite snap_pt_to_graph_eta. f_equal.
  rewrite <- snap_pt_to_graph_modules, snap_pt_to_graph_modules_SS.
  unfold pt_module_at at 1 2. cbv beta.
  assert (E1 : Nat.eqb (S next_id) mid = false) by (apply Nat.eqb_neq; lia).
  assert (E2 : Nat.eqb (S next_id) next_id = false) by (apply Nat.eqb_neq; lia).
  assert (E3 : Nat.eqb next_id mid = false) by (apply Nat.eqb_neq; lia).
  assert (E4 : Nat.eqb (sizes mid - Nat.div (sizes mid) 2) 0 = false) by (apply Nat.eqb_neq; lia).
  assert (E5 : Nat.eqb (Nat.div (sizes mid) 2) 0 = false) by (apply Nat.eqb_neq; lia).
  rewrite E1, E2, E3, !Nat.eqb_refl. cbv iota.
  rewrite E4, E5. cbv iota. cbn [List.app]. unfold pt_module. f_equal. f_equal.
  apply filtermap_ext. intros x Hx.
  apply in_rev in Hx. apply in_seq in Hx.
  assert (Exn : Nat.eqb x next_id = false) by (apply Nat.eqb_neq; lia).
  assert (ExSn : Nat.eqb x (S next_id) = false) by (apply Nat.eqb_neq; lia).
  unfold pt_module_at. cbv beta.
  destruct (Nat.eqb x mid) eqn:Exm.
  - destruct (Nat.eqb (sizes x) 0); reflexivity.
  - rewrite Exn, ExSn. destruct (Nat.eqb (sizes x) 0); reflexivity.
Qed.

(** Two ranges laid end to end form one range exactly when the second
    begins where the first ends. *)
Lemma region_contiguousb_seq_app : forall b1 s1 b2 s2, 0 < s1 -> 0 < s2 ->
  region_contiguousb (List.seq b1 s1 ++ List.seq b2 s2) = Nat.eqb (b1 + s1) b2.
Proof.
  intros b1 s1 b2 s2 H1 H2. unfold region_contiguousb.
  assert (Hhd : hd 0 (List.seq b1 s1 ++ List.seq b2 s2) = b1).
  { destruct s1 as [|s1']; [lia|]. reflexivity. }
  rewrite Hhd, app_length, !seq_length.
  destruct (Nat.eqb (b1 + s1) b2) eqn:E;
    match goal with |- context [if ?c then _ else _] => destruct c as [Heq|Hn] end.
  - reflexivity.
  - exfalso. apply Hn. apply Nat.eqb_eq in E. subst b2.
    rewrite seq_app. reflexivity.
  - exfalso. apply Nat.eqb_neq in E. apply E.
    rewrite seq_app in Heq. apply app_inv_head in Heq.
    destruct s2 as [|s2']; [lia|]. cbn [List.seq] in Heq. injection Heq as Hb _. lia.
  - reflexivity.
Qed.

(** The kernel's PMERGE adjacency test on the reconstructed graph is the
    hardware's base-and-size comparison. *)
Lemma snap_pmerge_adjacent_spec : forall next_id sizes bases m1 m2,
  m1 < next_id -> m2 < next_id -> 0 < sizes m1 -> 0 < sizes m2 ->
  pmerge_adjacent (snap_pt_to_graph next_id sizes bases) m1 m2 =
  snap_pmerge_adjacent sizes bases m1 m2.
Proof.
  intros next_id sizes bases m1 m2 H1 H2 Hs1 Hs2.
  unfold pmerge_adjacent.
  rewrite !snap_pt_to_graph_module_region by assumption.
  rewrite !region_contiguousb_seq_app by assumption.
  unfold snap_pmerge_adjacent.
  rewrite (proj2 (Nat.eqb_neq (sizes m1) 0)) by lia.
  rewrite (proj2 (Nat.eqb_neq (sizes m2) 0)) by lia.
  reflexivity.
Qed.

(** On two ranges that touch, PMERGE's joined region is the range starting
    at [snap_pmerge_base]. *)
Lemma pmerge_region_of_ranges : forall sizes bases m1 m2,
  0 < sizes m1 -> 0 < sizes m2 ->
  snap_pmerge_adjacent sizes bases m1 m2 = true ->
  pmerge_region (List.seq (bases m1) (sizes m1)) (List.seq (bases m2) (sizes m2)) =
  List.seq (snap_pmerge_base sizes bases m1 m2) (sizes m1 + sizes m2).
Proof.
  intros sizes bases m1 m2 H1 H2 Hadj.
  unfold pmerge_region, snap_pmerge_base, snap_pmerge_adjacent in *.
  rewrite region_contiguousb_seq_app by lia.
  assert (Z1 : Nat.eqb (sizes m1) 0 = false) by (apply Nat.eqb_neq; lia).
  assert (Z2 : Nat.eqb (sizes m2) 0 = false) by (apply Nat.eqb_neq; lia).
  rewrite Z1, Z2 in *. cbn [orb] in Hadj.
  destruct (Nat.eqb (bases m1 + sizes m1) (bases m2)) eqn:E.
  - apply Nat.eqb_eq in E. rewrite <- E. rewrite <- seq_app. reflexivity.
  - cbn [orb] in Hadj. apply Nat.eqb_eq in Hadj. rewrite <- Hadj.
    rewrite <- seq_app. f_equal. lia.
Qed.

(** graph_hw_pmerge on snap_pt_to_graph, for two modules whose ranges
    touch: both slots are removed and one new slot owns the joined range. *)
Theorem snap_pt_to_graph_pmerge :
    forall (next_id : nat) (sizes bases : nat -> nat) (m1 m2 : nat),
      next_id >= 1 ->
      S next_id <= PTableSz ->
      m1 < next_id ->
      m2 < next_id ->
      m1 <> m2 ->
      sizes m1 > 0 ->
      sizes m2 > 0 ->
      sizes next_id = 0 ->
      snap_pmerge_adjacent sizes bases m1 m2 = true ->
      graph_hw_pmerge (snap_pt_to_graph next_id sizes bases) m1 m2 =
      snap_pt_to_graph (S next_id)
        (fun j => if Nat.eqb j m1 then 0
                  else if Nat.eqb j m2 then 0
                  else if Nat.eqb j next_id then sizes m1 + sizes m2
                  else sizes j)
        (fun j => if Nat.eqb j m1 then 0
                  else if Nat.eqb j m2 then 0
                  else if Nat.eqb j next_id then snap_pmerge_base sizes bases m1 m2
                  else bases j).
Proof.
  intros next_id sizes bases m1 m2 Hge Hle Hlt1 Hlt2 Hne Hgt1 Hgt2 Hn0 Hadj.
  unfold graph_hw_pmerge. cbv zeta.
  change (graph_cascade_delete_morphisms
            (graph_cascade_delete_morphisms (snap_pt_to_graph next_id sizes bases) m1) m2)
    with (snap_pt_to_graph next_id sizes bases).
  rewrite !snap_pt_to_graph_module_region by assumption.
  rewrite (pmerge_region_of_ranges sizes bases m1 m2 Hgt1 Hgt2 Hadj).
  rewrite snap_pt_graph_remove by lia.
  (* graph_remove of m2 from the m1-removed graph *)
  assert (Hrem2 :
    graph_remove
      {| pg_next_id := next_id;
         pg_modules := filtermap (fun i =>
           if Nat.eqb (sizes i) 0 then None
           else if Nat.eqb i m1 then None
           else Some (i, pt_module (bases i) (sizes i)))
           (rev (seq 0 next_id));
         pg_next_morph_id := 1;
         pg_morphisms := [] |} m2 =
    Some ({| pg_next_id := next_id;
             pg_modules := filtermap (fun i =>
               if Nat.eqb (sizes i) 0 then None
               else if Nat.eqb i m1 then None
               else if Nat.eqb i m2 then None
               else Some (i, pt_module (bases i) (sizes i)))
               (rev (seq 0 next_id));
             pg_next_morph_id := 1;
             pg_morphisms := [] |},
          pt_module (bases m2) (sizes m2))).
  { unfold graph_remove. cbn [pg_modules pg_next_id pg_next_morph_id pg_morphisms].
    assert (Hconv :
      graph_remove_modules
        (filtermap (fun i =>
           if Nat.eqb (sizes i) 0 then None
           else if Nat.eqb i m1 then None
           else Some (i, pt_module (bases i) (sizes i)))
          (rev (seq 0 next_id))) m2 =
      graph_remove_modules
        (filtermap (fun i => match (if Nat.eqb (sizes i) 0 then None
                                    else if Nat.eqb i m1 then None
                                    else Some (pt_module (bases i) (sizes i))) with
                             | None => None
                             | Some v => Some (i, v)
                             end)
          (rev (seq 0 next_id))) m2).
    { f_equal. apply filtermap_ext. intros x _.
      destruct (Nat.eqb (sizes x) 0); [reflexivity|].
      destruct (Nat.eqb x m1); reflexivity. }
    rewrite Hconv.
    rewrite graph_remove_modules_filtermap with (v := pt_module (bases m2) (sizes m2)).
    - f_equal. f_equal. f_equal.
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
  rewrite Hrem2.
  unfold graph_add_module. cbn [fst snd pg_next_id pg_modules pg_next_morph_id pg_morphisms].
  rewrite normalize_module_pt_module.
  rewrite snap_pt_to_graph_eta. f_equal.
  rewrite <- snap_pt_to_graph_modules, snap_pt_to_graph_modules_S.
  unfold pt_module_at at 1. cbv beta.
  assert (E1 : Nat.eqb next_id m1 = false) by (apply Nat.eqb_neq; lia).
  assert (E2 : Nat.eqb next_id m2 = false) by (apply Nat.eqb_neq; lia).
  assert (E3 : Nat.eqb (sizes m1 + sizes m2) 0 = false) by (apply Nat.eqb_neq; lia).
  rewrite E1, E2, Nat.eqb_refl. cbv iota.
  rewrite E3. cbv iota. cbn [List.app]. unfold pt_module. f_equal.
  apply filtermap_ext. intros x Hx.
  apply in_rev in Hx. apply in_seq in Hx.
  assert (Exn : Nat.eqb x next_id = false) by (apply Nat.eqb_neq; lia).
  unfold pt_module_at. cbv beta.
  destruct (Nat.eqb x m1) eqn:Ex1.
  - destruct (Nat.eqb (sizes x) 0); reflexivity.
  - destruct (Nat.eqb x m2) eqn:Ex2.
    + destruct (Nat.eqb (sizes x) 0); reflexivity.
    + rewrite Exn. destruct (Nat.eqb (sizes x) 0); reflexivity.
Qed.

(* *)
(** 2. Morphism table commutation                                        *)
(* *)

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
              {| coupling_pairs :=
                   snapshot_coupling_pairs_from_desc rs coupling_desc;
                 coupling_label :=
                   match rich_coupling_desc_table rs coupling_desc with
                   | Some desc => coupling_desc_label desc
                   | None => coupling_label empty_coupling_data
                   end |};
          morph_is_identity := is_id;
               morph_cert_cost := 0 |})
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
                   morph_is_identity := morph_entry_is_identity entry;
               morph_cert_cost := 0 |} in
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

(* *)
(** 3. kami_step preserves graph-relevant invariants                      *)
(* *)

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
  try (simpl; split; reflexivity);
  try (repeat match goal with |- context [match ?x with _ => _ end] =>
         destruct x end; simpl;
       try (unfold kami_advance_rich_morph; simpl; split; reflexivity);
       try (unfold kami_advance_err; simpl; split; reflexivity);
       try (unfold kami_advance_rich_noret; simpl; split; reflexivity);
       try (unfold kami_advance_cert_addr; simpl; split; reflexivity);
       try (unfold kami_advance_reg; simpl; split; reflexivity);
       try (split; reflexivity)).
Qed.
