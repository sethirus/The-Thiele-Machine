(** PermanentRecordPricing: how much a permanent certificate costs, and which
    flips a finite machine is forced to pay for.

    [PermanentCertification] shows that on a finite machine a certificate no
    step revokes is switched on only by a step that merges states. This file
    carries that in two directions.

    How much. Landauer's principle, stated on the logic, says a step that
    squeezes a set of states down pays one unit for every halving. Here that
    is the counting premise [compression_priced]: an instruction with cost
    [c] maps any duplicate-free set of [n] states onto at least [n / 2^c]
    distinct states. Under that premise, switching [k] states on while [m]
    states are already certified costs at least [log2 ((m + k) / m)], stated
    in integers as [m + k <= 2^cost * m] and in rounded logarithms as
    [log2_up (m + k) <= cost + log2_up m]. With [k = 1] this is A2 again.
    The bound is attained: a four-state stamp that switches three blank
    states on pays exactly two.

    Which flips. Fix a finite machine and one instruction. Three facts.

    - Merge or revoke. If the instruction switches the reading on somewhere,
      then either it merges two states, or it switches the reading off
      somewhere else. A flip that forgets nothing is always paid for by a
      revocation.
    - Forced price is merging. The instruction is charged at least one by
      every cost assignment that prices merges exactly when the instruction
      merges. Decidable equality on instructions is used to build the free
      assignment for an injective instruction.
    - Permanent records are forced. An instruction that never revokes the
      reading and switches it on somewhere is charged by every such cost
      assignment.

    The converse of the last point is false. A three-state instruction can
    switch the reading on, switch it off elsewhere, and merge, so a forced
    price does not by itself mean a permanent record. The forced flips are
    exactly the merging ones; the permanent-record flips are a subset of
    them.

    Scope. The pricing premises stand for Landauer's principle and are named
    premises, not theorems about heat. A machine with an unbounded ledger
    is not an instance; [FiniteCertMachine] is one. *)

From Coq Require Import List Bool Arith Lia.
From Coq Require Import Logic.FinFun.
Import ListNotations.

From Kernel Require Import UniversalCertificationCost.
From Kernel Require Import PermanentCertification.

(** Duplicate-free concatenation of lists with no common member. *)
Lemma nodup_app_disjoint :
  forall (A : Type) (l l' : list A),
    NoDup l -> NoDup l' -> (forall a, In a l -> ~ In a l') ->
    NoDup (l ++ l').
Proof.
  intros A l l' Hl Hl' Hdisj. induction l as [| x xs IH]; simpl.
  - exact Hl'.
  - inversion Hl as [| ? ? Hnotin Hxs]; subst.
    constructor.
    + intro Hin. apply in_app_or in Hin as [Hin | Hin].
      * exact (Hnotin Hin).
      * exact (Hdisj x (or_introl eq_refl) Hin).
    + apply IH; [exact Hxs |].
      intros a Ha. apply Hdisj. right. exact Ha.
Qed.

(** * How much a permanent certificate costs *)

Section Quantitative.

Variables (S I : Type).
Variable step : S -> I -> S.
Variable cert : S -> bool.
Variable cost : I -> nat.
Variable eq_dec : forall a b : S, {a = b} + {a <> b}.

(** The number of distinct states an instruction sends a list to. *)
Definition image_size (i : I) (D : list S) : nat :=
  length (nodup eq_dec (map (fun t => step t i) D)).

(** Landauer's principle as a counting premise: each unit of cost pays for
    at most one halving of the number of distinct states. *)
Definition compression_priced : Prop :=
  forall i D, NoDup D -> length D <= 2 ^ cost i * image_size i D.

(** Switching [k] distinct states on, with [m] states already certified,
    costs enough that [m + k <= 2^cost * m]. *)
Theorem permanent_flips_compression_bound :
  forall all i F,
    finite_states all ->
    permanent step cert ->
    compression_priced ->
    NoDup F ->
    (forall s, In s F -> cert s = false /\ cert (step s i) = true) ->
    length F + length (certified_states S cert all)
      <= 2 ^ cost i * length (certified_states S cert all).
Proof.
  intros all i F Hfin Hperm Hprice HndF HF.
  set (C := certified_states S cert all).
  assert (HndC : NoDup C) by (apply certified_states_nodup; exact Hfin).
  assert (HinC : forall t, In t C <-> cert t = true)
    by (apply certified_states_spec; exact Hfin).
  assert (Hnd : NoDup (F ++ C)).
  { apply nodup_app_disjoint; [exact HndF | exact HndC |].
    intros a HaF HaC. apply HinC in HaC.
    destruct (HF a HaF) as [Ha _]. rewrite Ha in HaC. discriminate. }
  assert (Himg : incl (nodup eq_dec (map (fun t => step t i) (F ++ C))) C).
  { intros y Hy. apply nodup_In in Hy.
    apply in_map_iff in Hy as [x [<- Hx]].
    apply HinC. apply in_app_or in Hx as [HxF | HxC].
    - apply HF. exact HxF.
    - apply Hperm. apply HinC. exact HxC. }
  assert (Hle : image_size i (F ++ C) <= length C).
  { apply NoDup_incl_length; [apply NoDup_nodup | exact Himg]. }
  pose proof (Hprice i (F ++ C) Hnd) as Hc.
  rewrite app_length in Hc.
  apply Nat.le_trans with (m := 2 ^ cost i * image_size i (F ++ C));
    [exact Hc | apply Nat.mul_le_mono_l; exact Hle].
Qed.

(** A flip means at least one state is certified. *)
Lemma flip_gives_certified_state :
  forall (all : list S) s i,
    finite_states all ->
    cert (step s i) = true ->
    0 < length (certified_states S cert all).
Proof.
  intros all s i Hfin Hflip.
  assert (Hin : In (step s i) (certified_states S cert all))
    by (apply (certified_states_spec S cert all Hfin); exact Hflip).
  destruct (certified_states S cert all); [contradiction | simpl; lia].
Qed.

(** The same bound in rounded base-2 logarithms. *)
Theorem permanent_flips_log_bound :
  forall (all : list S) s i F,
    finite_states all ->
    permanent step cert ->
    compression_priced ->
    cert (step s i) = true ->
    NoDup F ->
    (forall t, In t F -> cert t = false /\ cert (step t i) = true) ->
    Nat.log2_up (length (certified_states S cert all) + length F)
      <= cost i + Nat.log2_up (length (certified_states S cert all)).
Proof.
  intros all s i F Hfin Hperm Hprice Hs HndF HF.
  set (m := length (certified_states S cert all)).
  assert (Hm : 0 < m) by (eapply flip_gives_certified_state; eauto).
  pose proof (permanent_flips_compression_bound all i F Hfin Hperm Hprice HndF HF)
    as Hb.
  fold m in Hb.
  rewrite <- Nat.log2_up_mul_pow2 by lia.
  apply Nat.log2_up_le_mono.
  rewrite Nat.mul_comm. lia.
Qed.

(** With one flipped state the bound is A2. *)
Theorem a2_from_compression_price_and_permanence :
  forall all : list S,
    finite_states all ->
    permanent step cert ->
    compression_priced ->
    a2_holds step cert cost.
Proof.
  intros all Hfin Hperm Hprice s i Hs Hflip.
  assert (Hm : 0 < length (certified_states S cert all))
    by (eapply flip_gives_certified_state; eauto).
  assert (Hb := permanent_flips_compression_bound all i [s] Hfin Hperm Hprice
                  (NoDup_cons s (fun H : In s [] => H) (NoDup_nil S))).
  assert (HF : forall t, In t [s] -> cert t = false /\ cert (step t i) = true).
  { intros t [<- | []]. split; assumption. }
  specialize (Hb HF). simpl length in Hb.
  destruct (cost i) as [| c]; [simpl in Hb; lia | lia].
Qed.

End Quantitative.

Arguments image_size {S I}.
Arguments compression_priced {S I}.

(** The counting premise builds a [CertificationSystem] whose A2 field is
    discharged by the bound above, and the trace-level floor follows from
    [universal_nfi_any_substrate]. *)
Definition certification_system_from_compression_price
    (S I : Type) (step : S -> I -> S) (cert : S -> bool) (cost : I -> nat)
    (eq_dec : forall a b : S, {a = b} + {a <> b})
    (all : list S)
    (Hfin : finite_states all)
    (Hperm : permanent step cert)
    (Hprice : compression_priced step cost eq_dec) : CertificationSystem :=
  {| cs_state := S;
     cs_instr := I;
     cs_step := step;
     cs_cost := cost;
     cs_cert := cert;
     cs_cert_costs :=
       a2_from_compression_price_and_permanence S I step cert cost eq_dec all
         Hfin Hperm Hprice |}.

Theorem compression_priced_trace_floor :
  forall (S I : Type) (step : S -> I -> S) (cert : S -> bool) (cost : I -> nat)
         (eq_dec : forall a b : S, {a = b} + {a <> b})
         (all : list S)
         (Hfin : finite_states all)
         (Hperm : permanent step cert)
         (Hprice : compression_priced step cost eq_dec)
         (trace : list I) (s0 : S),
    cert s0 = false ->
    cert (cs_run (certification_system_from_compression_price
                    S I step cert cost eq_dec all Hfin Hperm Hprice) trace s0) = true ->
    cs_total_cost (certification_system_from_compression_price
                     S I step cert cost eq_dec all Hfin Hperm Hprice) trace >= 1.
Proof.
  intros S I step cert cost eq_dec all Hfin Hperm Hprice trace s0 H0 H1.
  exact (universal_nfi_any_substrate
           (certification_system_from_compression_price
              S I step cert cost eq_dec all Hfin Hperm Hprice) trace s0 H0 H1).
Qed.

(** The bound is attained. Four sheets, three blank and one stamped; the one
    instruction stamps every sheet. Switching the three blanks on costs at
    least two, and cost two satisfies the counting premise. *)
Inductive Quad := Q0 | Q1 | Q2 | Q3.

Definition quad_eq_dec : forall a b : Quad, {a = b} + {a <> b}.
Proof. decide equality. Defined.

Definition quad_stamped (q : Quad) : bool :=
  match q with Q3 => true | _ => false end.

Definition quad_stamp (_ : Quad) (_ : unit) : Quad := Q3.

Lemma quads_finite : finite_states [Q0; Q1; Q2; Q3].
Proof.
  split.
  - repeat constructor; simpl; intuition discriminate.
  - intro q. destruct q; simpl; auto.
Qed.

Lemma quad_stamp_permanent : permanent quad_stamp quad_stamped.
Proof. intros q i _. reflexivity. Qed.

Lemma quad_image_nonempty :
  forall D, D <> [] -> 1 <= image_size quad_stamp quad_eq_dec tt D.
Proof.
  intros D HD. unfold image_size.
  assert (Hin : In Q3 (nodup quad_eq_dec (map (fun t => quad_stamp t tt) D))).
  { apply nodup_In. destruct D as [| d ds]; [contradiction |].
    simpl. left. reflexivity. }
  destruct (nodup quad_eq_dec (map (fun t => quad_stamp t tt) D));
    [contradiction | simpl; lia].
Qed.

Lemma quad_lists_short : forall D : list Quad, NoDup D -> length D <= 4.
Proof.
  intros D HD.
  change 4 with (length [Q0; Q1; Q2; Q3]).
  apply NoDup_incl_length; [exact HD |].
  intros q _. destruct q; simpl; auto.
Qed.

Theorem quad_stamp_cost_two_is_priced :
  compression_priced quad_stamp (fun (_ : unit) => 2) quad_eq_dec.
Proof.
  intros i D HD. destruct i.
  destruct D as [| d ds]; [simpl; lia |].
  pose proof (quad_lists_short (d :: ds) HD) as Hlen.
  pose proof (quad_image_nonempty (d :: ds) ltac:(discriminate)) as Himg.
  simpl (2 ^ 2). lia.
Qed.

Theorem quad_stamp_needs_two :
  forall cost : unit -> nat,
    compression_priced quad_stamp cost quad_eq_dec ->
    2 <= cost tt.
Proof.
  intros cost Hprice.
  pose proof (permanent_flips_compression_bound Quad unit quad_stamp
                quad_stamped cost quad_eq_dec [Q0; Q1; Q2; Q3] tt [Q0; Q1; Q2]
                quads_finite quad_stamp_permanent Hprice) as Hb.
  assert (HndF : NoDup [Q0; Q1; Q2])
    by (repeat constructor; simpl; intuition discriminate).
  specialize (Hb HndF).
  assert (HF : forall s, In s [Q0; Q1; Q2] ->
                 quad_stamped s = false /\ quad_stamped (quad_stamp s tt) = true).
  { intros s [<- | [<- | [<- | []]]]; split; reflexivity. }
  specialize (Hb HF). simpl in Hb.
  destruct (cost tt) as [| [| c]]; simpl in Hb; lia.
Qed.

(** * Which flips a finite machine must pay for *)

Section Characterization.

Variables (S I : Type).
Variable step : S -> I -> S.
Variable cert : S -> bool.

(** The instruction [i] never switches the reading off. *)
Definition permanent_at (i : I) : Prop :=
  forall s, cert s = true -> cert (step s i) = true.

(** Permanence under the one flipping instruction is enough for the merge. *)
Theorem permanent_at_flip_is_not_injective :
  forall (all : list S) s i,
    finite_states all ->
    permanent_at i ->
    cert s = false ->
    cert (step s i) = true ->
    ~ step_injective step i.
Proof.
  intros all s i Hfin Hperm Hs Hflip Hinj.
  set (L := certified_states S cert all).
  set (f := fun t => step t i).
  assert (HinL : forall t, In t L <-> cert t = true)
    by (apply certified_states_spec; exact Hfin).
  assert (HndM : NoDup (map f L)).
  { apply Injective_map_NoDup; [ | apply certified_states_nodup; exact Hfin].
    intros a b Hab. apply Hinj. exact Hab. }
  assert (Hincl : incl (map f L) L).
  { intros y Hy. apply in_map_iff in Hy as [x [<- Hx]].
    apply HinL. apply HinL in Hx. apply Hperm. exact Hx. }
  assert (Hback : incl L (map f L)).
  { apply NoDup_length_incl;
      [exact HndM | rewrite map_length; lia | exact Hincl]. }
  assert (Hfs : In (f s) (map f L)) by (apply Hback; apply HinL; exact Hflip).
  apply in_map_iff in Hfs as [c [Hc HcL]].
  apply Hinj in Hc. subst c.
  apply HinL in HcL. rewrite Hs in HcL. discriminate.
Qed.

(** Merge or revoke. A flipping instruction either merges two states or
    switches the reading off somewhere. The revoked state is found by a
    search over the certified states, so the proof is constructive. *)
Theorem flip_merges_or_revokes :
  forall (all : list S) s i,
    finite_states all ->
    cert s = false ->
    cert (step s i) = true ->
    ~ step_injective step i
    \/ exists t, cert t = true /\ cert (step t i) = false.
Proof.
  intros all s i Hfin Hs Hflip.
  set (L := certified_states S cert all).
  assert (HinL : forall t, In t L <-> cert t = true)
    by (apply certified_states_spec; exact Hfin).
  destruct (existsb (fun t => negb (cert (step t i))) L) eqn:Hsearch.
  - right. apply existsb_exists in Hsearch as [t [Ht Hneg]].
    exists t. split; [apply HinL; exact Ht |].
    apply negb_true_iff. exact Hneg.
  - left. apply (permanent_at_flip_is_not_injective all s i Hfin); auto.
    intros t Ht.
    destruct (cert (step t i)) eqn:Hstep; [reflexivity |].
    exfalso.
    assert (Hex : existsb (fun t => negb (cert (step t i))) L = true).
    { apply existsb_exists. exists t. split.
      - apply HinL. exact Ht.
      - rewrite Hstep. reflexivity. }
    rewrite Hex in Hsearch. discriminate.
Qed.

(** A flip that forgets nothing is paid for by a revocation. *)
Corollary injective_flip_revokes :
  forall (all : list S) s i,
    finite_states all ->
    step_injective step i ->
    cert s = false ->
    cert (step s i) = true ->
    exists t, cert t = true /\ cert (step t i) = false.
Proof.
  intros all s i Hfin Hinj Hs Hflip.
  destruct (flip_merges_or_revokes all s i Hfin Hs Hflip) as [Hm | Hr].
  - contradiction.
  - exact Hr.
Qed.

(** An instruction is forced to be priced when every cost assignment that
    prices merges charges it at least one. *)
Definition forced_priced (i : I) : Prop :=
  forall cost : I -> nat, merging_steps_priced step cost -> cost i >= 1.

Variable instr_eq_dec : forall a b : I, {a = b} + {a <> b}.

(** Forced price is exactly merging. *)
Theorem forced_priced_iff_merges :
  forall i, forced_priced i <-> ~ step_injective step i.
Proof.
  intro i. split.
  - intros Hforced Hinj.
    set (free_i := fun j => if instr_eq_dec j i then 0 else 1).
    assert (Hpriced : merging_steps_priced step free_i).
    { intros j Hj. unfold free_i.
      destruct (instr_eq_dec j i) as [-> | Hne].
      - exfalso. exact (Hj Hinj).
      - unfold ge. apply le_n. }
    specialize (Hforced free_i Hpriced). unfold free_i in Hforced.
    destruct (instr_eq_dec i i) as [_ | Hne]; [inversion Hforced | apply Hne; reflexivity].
  - intros Hmerge cost Hprice. exact (Hprice i Hmerge).
Qed.

(** An instruction that writes a permanent record is forced to be priced. *)
Corollary permanent_record_write_is_forced_priced :
  forall (all : list S) s i,
    finite_states all ->
    permanent_at i ->
    cert s = false ->
    cert (step s i) = true ->
    forced_priced i.
Proof.
  intros all s i Hfin Hperm Hs Hflip.
  apply forced_priced_iff_merges.
  eapply permanent_at_flip_is_not_injective; eauto.
Qed.

End Characterization.

Arguments permanent_at {S I}.
Arguments forced_priced {S I}.

(** The inclusion is strict. Three states: [T0] and [T2] unmarked, [T1]
    marked. The one instruction sends [T0] to [T1] (a flip), [T1] to [T2]
    (a revocation), and [T2] to [T1] (merging [T0] and [T2]). Every cost
    assignment that prices merges charges it, and it writes no permanent
    record. *)
Inductive Tri := T0 | T1 | T2.

Definition tri_eq_dec : forall a b : Tri, {a = b} + {a <> b}.
Proof. decide equality. Defined.

Definition tri_mark (x : Tri) : bool :=
  match x with T1 => true | _ => false end.

Definition tri_step (x : Tri) (_ : unit) : Tri :=
  match x with T0 => T1 | T1 => T2 | T2 => T1 end.

Theorem forced_price_without_permanent_record :
  finite_states [T0; T1; T2] /\
  tri_mark T0 = false /\ tri_mark (tri_step T0 tt) = true /\
  ~ permanent_at tri_step tri_mark tt /\
  forced_priced tri_step tt.
Proof.
  split; [| split; [reflexivity | split; [reflexivity | split]]].
  - split.
    + repeat constructor; simpl; intuition discriminate.
    + intro x. destruct x; simpl; auto.
  - intro Hperm. specialize (Hperm T1 eq_refl). discriminate.
  - intros cost Hprice. apply Hprice.
    intro Hinj. specialize (Hinj T0 T2 eq_refl). discriminate.
Qed.
