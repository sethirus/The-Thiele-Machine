(** NecFMerge: a permanent flip merges, the toll from merges, merge or revoke,
    and forced prices, each pushed to its limit.

    - Finiteness of the whole machine is more than the theorems use. Each of
      "a permanent flip merges", "merge or revoke" and "the toll from merges"
      holds when only the states reading yes are finitely many, and the
      permanence is needed only for the one move in question.
    - The merge sits among the yes-states and the flipped state: two of them
      land together ([nec_f_flip_collision_in_yes_and_s]). It need not involve
      the flipped state itself ([nec_f_collision_avoids_s]).
    - A merge does not make a flip ([nec_f_jump_merges_never_flips]).
    - Each premise of the toll is needed, and merge pricing is more than A2
      needs: the eight-state machine with a free jump still meets A2
      ([nec_f_a2_without_merge_pricing]). What A2 needs, on a machine with a
      permanent reading and finitely many yes-states, is exactly that every
      move which flips somewhere and merges is priced
      ([nec_f_a2_iff_flipping_merges_priced]).
    - In merge or revoke the "or" can be replaced by neither side and not by
      "and"; finiteness is needed.
    - Forced price is merging, with decidable equality cut down to "the move
      can be told apart from the others" ([nec_f_forced_iff_merges_isolated]).
      Some decidability is needed: under the continuity principle, which holds
      in Kleene's realizability model, a move on sequences is forced to be
      priced although it forgets nothing ([nec_f_forced_without_merge_under_continuity]).
    - The corollary "permanent records are forced" needs both finiteness and
      permanence. *)

From Coq Require Import List Bool Arith Lia.
From Coq Require Import Logic.FinFun.
Import ListNotations.
From Kernel Require Import PermanentCertification.
From Kernel Require Import PermanentRecordPricing.
From Kernel Require Import PermanentCertificationEntropy.
From Kernel Require Import FiniteCertMachine.

Section YesList.

Variables (S I : Type).
Variable step : S -> I -> S.
Variable cert : S -> bool.

(** Finitely many yes-states: a list without repeats naming exactly them. *)
Definition nec_f_yes_list (Y : list S) : Prop :=
  NoDup Y /\ forall t, In t Y <-> cert t = true.

Lemma nec_f_yes_list_of_finite :
  forall all, finite_states all -> nec_f_yes_list (certified_states S cert all).
Proof.
  intros all Hfin. split.
  - apply certified_states_nodup. exact Hfin.
  - apply certified_states_spec. exact Hfin.
Qed.

(** Injective on a list: no two different members land together. *)
Definition nec_f_injective_on (i : I) (l : list S) : Prop :=
  forall a b, In a l -> In b l -> step a i = step b i -> a = b.

(** The flip and the yes-states cannot all land apart. Only the yes-states
    need to be finitely many, and permanence is needed only for move i. *)
Theorem nec_f_flip_not_injective_on_yes_and_s :
  forall Y s i,
    nec_f_yes_list Y ->
    permanent_at step cert i ->
    cert s = false ->
    cert (step s i) = true ->
    ~ nec_f_injective_on i (s :: Y).
Proof.
  intros Y s i [HndY HY] Hperm Hs Hflip Hinj.
  set (f := fun t => step t i).
  assert (HsY : ~ In s Y) by (intro H; apply HY in H; congruence).
  assert (Hnd : NoDup (map f (s :: Y))).
  { assert (Hnds : NoDup (s :: Y)) by (constructor; assumption).
    clear HsY. revert Hnds Hinj. generalize (s :: Y) as l. intros l Hnd Hinj.
    assert (Hgen : forall l', incl l' l -> NoDup l' -> NoDup (map f l')).
    { induction l' as [| x xs IH]; intros Hincl Hnd'; simpl; [constructor |].
      inversion Hnd' as [| ? ? Hx Hxs]; subst. constructor.
      - intro Hin. apply in_map_iff in Hin as [y [Hy Hyin]].
        assert (y = x) by (apply Hinj; [apply Hincl; right; exact Hyin |
                                          apply Hincl; left; reflexivity | exact Hy]).
        subst y. contradiction.
      - apply IH; [intros z Hz; apply Hincl; right; exact Hz | exact Hxs]. }
    apply Hgen; [intros z Hz; exact Hz | exact Hnd]. }
  assert (Hincl : incl (map f (s :: Y)) Y).
  { intros y Hy. apply in_map_iff in Hy as [x [<- Hx]]. apply HY.
    destruct Hx as [<- | Hx]; [exact Hflip | apply Hperm; apply HY; exact Hx]. }
  pose proof (NoDup_incl_length Hnd Hincl) as Hlen.
  rewrite map_length in Hlen. simpl in Hlen. lia.
Qed.

(** The repo theorem, with finiteness cut down to finitely many yes-states. *)
Corollary nec_f_perm_flip_merges_yes_finite :
  forall Y s i,
    nec_f_yes_list Y ->
    permanent_at step cert i ->
    cert s = false ->
    cert (step s i) = true ->
    ~ step_injective step i.
Proof.
  intros Y s i HY Hperm Hs Hflip Hinj.
  apply (nec_f_flip_not_injective_on_yes_and_s Y s i HY Hperm Hs Hflip).
  intros a b _ _ H. exact (Hinj a b H).
Qed.

(** With equality of states decidable, the two states that land together are
    named, and both lie among the yes-states and the flipped state. *)
Theorem nec_f_flip_collision_in_yes_and_s :
  forall (eq_dec : forall a b : S, {a = b} + {a <> b}) Y s i,
    nec_f_yes_list Y ->
    permanent_at step cert i ->
    cert s = false ->
    cert (step s i) = true ->
    exists a b, In a (s :: Y) /\ In b (s :: Y) /\ a <> b /\ step a i = step b i.
Proof.
  intros eq_dec Y s i HY Hperm Hs Hflip.
  destruct HY as [HndY HinY].
  assert (Hnds : NoDup (s :: Y)).
  { constructor; [intro H; apply HinY in H; congruence | exact HndY]. }
  assert (Hmap : ~ NoDup (map (fun t => step t i) (s :: Y))).
  { intro Hnd. assert (Hincl : incl (map (fun t => step t i) (s :: Y)) Y).
    { intros y Hy. apply in_map_iff in Hy as [x [<- Hx]]. apply HinY.
      destruct Hx as [<- | Hx]; [exact Hflip | apply Hperm; apply HinY; exact Hx]. }
    pose proof (NoDup_incl_length Hnd Hincl) as Hlen.
    rewrite map_length in Hlen. simpl in Hlen. lia. }
  exact (not_nodup_map_witness eq_dec (fun t => step t i) (s :: Y) Hnds Hmap).
Qed.

(** Merge or revoke, with only the yes-states finitely many. *)
Theorem nec_f_merge_or_revoke_yes_finite :
  forall Y s i,
    nec_f_yes_list Y ->
    cert s = false ->
    cert (step s i) = true ->
    ~ step_injective step i \/ exists t, cert t = true /\ cert (step t i) = false.
Proof.
  intros Y s i HY Hs Hflip.
  destruct (existsb (fun t => negb (cert (step t i))) Y) eqn:Hsearch.
  - right. apply existsb_exists in Hsearch as [t [Ht Hneg]].
    exists t. split; [apply (proj2 HY); exact Ht | apply negb_true_iff; exact Hneg].
  - left. apply (nec_f_perm_flip_merges_yes_finite Y s i HY); auto.
    intros t Ht. destruct (cert (step t i)) eqn:Hst; [reflexivity |].
    exfalso.
    assert (Hex : existsb (fun t => negb (cert (step t i))) Y = true).
    { apply existsb_exists. exists t. split; [apply (proj2 HY); exact Ht | rewrite Hst; reflexivity]. }
    congruence.
Qed.

Variable cost : I -> nat.

(** The toll from merges, with only the yes-states finitely many. *)
Theorem nec_f_toll_from_merges_yes_finite :
  forall Y,
    nec_f_yes_list Y ->
    permanent step cert ->
    merging_steps_priced step cost ->
    a2_holds step cert cost.
Proof.
  intros Y HY Hperm Hprice s i Hs Hflip. apply Hprice.
  apply (nec_f_perm_flip_merges_yes_finite Y s i HY); auto.
  intros t Ht. apply Hperm. exact Ht.
Qed.

(** The weakest per-move premise: every move that flips somewhere and merges
    is priced. *)
Definition nec_f_flipping_merges_priced : Prop :=
  forall i, (exists s, cert s = false /\ cert (step s i) = true) ->
    ~ step_injective step i -> cost i >= 1.

(** On a machine with a permanent reading and finitely many yes-states, A2
    holds exactly when every move that flips somewhere and merges is priced. *)
Theorem nec_f_a2_iff_flipping_merges_priced :
  forall Y,
    nec_f_yes_list Y ->
    permanent step cert ->
    (a2_holds step cert cost <-> nec_f_flipping_merges_priced).
Proof.
  intros Y HY Hperm. split.
  - intros Ha i [s [Hs Hflip]] _. exact (Ha s i Hs Hflip).
  - intros Hp s i Hs Hflip. apply Hp; [exists s; split; assumption |].
    apply (nec_f_perm_flip_merges_yes_finite Y s i HY); auto.
    intros t Ht. apply Hperm. exact Ht.
Qed.

(** Merge pricing implies the weakest premise. *)
Lemma nec_f_merging_priced_weakens :
  merging_steps_priced step cost -> nec_f_flipping_merges_priced.
Proof. intros H i _ Hm. exact (H i Hm). Qed.

End YesList.

(** The repo's finiteness gives a yes-list, so the repo theorems are
    corollaries of the versions above. *)
Corollary nec_f_repo_perm_flip_from_yes_finite :
  forall (S I : Type) (step : S -> I -> S) (cert : S -> bool) (all : list S) s i,
    finite_states all -> permanent step cert ->
    cert s = false -> cert (step s i) = true -> ~ step_injective step i.
Proof.
  intros S I step cert all s i Hfin Hperm Hs Hflip.
  apply (nec_f_perm_flip_merges_yes_finite S I step cert
           (certified_states S cert all) s i
           (nec_f_yes_list_of_finite S cert all Hfin)); auto.
  intros t Ht. apply Hperm. exact Ht.
Qed.

(** * Witnesses on the machines of the repo *)

(** Without a flip there is no merge: the eight-state machine's NEXT is
    injective, on a finite machine with a permanent reading. *)
Theorem nec_f_no_flip_no_merge :
  finite_states all_fstates /\ permanent fstep fcert /\ step_injective fstep FNext /\
  (forall s, fcert s = false -> fcert (fstep s FNext) = false).
Proof.
  split; [exact fin_finite | split; [exact fin_permanent | split; [exact fnext_injective |]]].
  intros [p c] H. exact H.
Qed.

(** A merge does not make a flip: JUMP merges and never turns the reading on. *)
Theorem nec_f_jump_merges_never_flips :
  forall a, ~ step_injective fstep (FJump a) /\
    (forall s, fcert s = false -> fcert (fstep s (FJump a)) = false).
Proof.
  intro a. split; [apply fjump_merges |]. intros [p c] H. exact H.
Qed.

(** The merge need not involve the flipped state. Four states, c0 reading no
    and c1, c2, c3 reading yes; the move sends c0 to c1, c1 to c2, c2 and c3
    to c3. Only c0 lands on c1; c2 and c3 land together. *)
Inductive NecFChain := NecFc0 | NecFc1 | NecFc2 | NecFc3.

Definition nec_f_chain_step (x : NecFChain) (_ : unit) : NecFChain :=
  match x with NecFc0 => NecFc1 | NecFc1 => NecFc2 | _ => NecFc3 end.
Definition nec_f_chain_cert (x : NecFChain) : bool :=
  match x with NecFc0 => false | _ => true end.

Theorem nec_f_collision_avoids_s :
  finite_states [NecFc0; NecFc1; NecFc2; NecFc3] /\
  permanent nec_f_chain_step nec_f_chain_cert /\
  nec_f_chain_cert NecFc0 = false /\
  nec_f_chain_cert (nec_f_chain_step NecFc0 tt) = true /\
  (forall b, nec_f_chain_step b tt = nec_f_chain_step NecFc0 tt -> b = NecFc0) /\
  nec_f_chain_step NecFc2 tt = nec_f_chain_step NecFc3 tt.
Proof.
  split; [split; [repeat constructor; simpl; intuition discriminate | intros []; simpl; tauto] |].
  split; [intros [] [] H; simpl in *; try reflexivity; discriminate |].
  split; [reflexivity | split; [reflexivity | split; [| reflexivity]]].
  intros [] H; simpl in H; try reflexivity; discriminate.
Qed.

(** ** The toll: each premise is needed *)

(** Without finiteness: the history machine, charged nothing, prices every
    merge (it has none), keeps its reading, and certifies for free. *)
Theorem nec_f_toll_needs_finite :
  permanent history_step history_cert /\
  merging_steps_priced history_step (fun _ : unit => 0) /\
  ~ a2_holds history_step history_cert (fun _ : unit => 0).
Proof.
  destruct unbounded_history_escapes as [Hinj [Hperm [H0 H1]]].
  split; [exact Hperm | split].
  - intros [] Hm. exfalso. exact (Hm Hinj).
  - intro Ha. specialize (Ha [] tt H0 H1). cbn in *; lia.
Qed.

(** Without permanence: negation on one bit, charged nothing. *)
Theorem nec_f_toll_needs_permanent :
  finite_states [false; true] /\
  merging_steps_priced flip_step (fun _ : unit => 0) /\
  ~ a2_holds flip_step (fun b => b) (fun _ : unit => 0).
Proof.
  destruct revocable_certificate_escapes as [Hinj [H1 H2]].
  split; [split; [repeat constructor; simpl; intuition discriminate | intros []; simpl; tauto] |].
  split.
  - intros [] Hm. exfalso. exact (Hm Hinj).
  - intro Ha. specialize (Ha false tt eq_refl H1). cbn in *; lia.
Qed.

(** Merge pricing is not needed for A2: the eight-state machine with a free
    jump still meets A2, because the jump never flips. *)
Definition nec_f_free_jump_cost (i : FInstr) : nat :=
  match i with FCertify => 1 | FJump _ => 0 | FNext => 0 end.

Theorem nec_f_a2_without_merge_pricing :
  finite_states all_fstates /\ permanent fstep fcert /\
  a2_holds fstep fcert nec_f_free_jump_cost /\
  ~ merging_steps_priced fstep nec_f_free_jump_cost /\
  nec_f_flipping_merges_priced FState FInstr fstep fcert nec_f_free_jump_cost.
Proof.
  assert (Ha : a2_holds fstep fcert nec_f_free_jump_cost).
  { intros [p c] i Hs Hflip. destruct i; simpl in *; try lia; congruence. }
  split; [exact fin_finite | split; [exact fin_permanent | split; [exact Ha | split]]].
  - intro H. pose proof (H (FJump L0) (fjump_merges L0)). simpl in *. lia.
  - apply (proj1 (nec_f_a2_iff_flipping_merges_priced FState FInstr fstep fcert
                   nec_f_free_jump_cost _ (nec_f_yes_list_of_finite _ fcert _ fin_finite)
                   fin_permanent)).
    exact Ha.
Qed.

(** ** Merge or revoke: finiteness is needed, and the "or" is sharp *)

(** Without finiteness: the history machine flips, never merges, never revokes. *)
Theorem nec_f_merge_or_revoke_needs_finite :
  history_cert [] = false /\ history_cert (history_step [] tt) = true /\
  step_injective history_step tt /\
  ~ (exists t, history_cert t = true /\ history_cert (history_step t tt) = false).
Proof.
  destruct unbounded_history_escapes as [Hinj [Hperm [H0 H1]]].
  repeat split; try assumption.
  intros [t [Ht Hr]]. rewrite (Hperm t tt Ht) in Hr. discriminate.
Qed.

(** A flip that merges and never revokes: the stamp. So "revoke" alone is
    false, and so is "merge and revoke". *)
Theorem nec_f_merge_only_flip :
  finite_states [Blank; Stamped] /\
  stamped Blank = false /\ stamped (stamp_step Blank tt) = true /\
  ~ step_injective stamp_step tt /\
  ~ (exists t, stamped t = true /\ stamped (stamp_step t tt) = false).
Proof.
  split; [exact sheets_finite | split; [reflexivity | split; [reflexivity | split]]].
  - intro H. specialize (H Blank Stamped eq_refl). discriminate.
  - intros [t [_ H]]. discriminate.
Qed.

(** A flip that revokes and never merges: negation on one bit. So "merge"
    alone is false. *)
Theorem nec_f_revoke_only_flip :
  finite_states [false; true] /\
  flip_step false tt = true /\
  step_injective flip_step tt /\
  (exists t, t = true /\ flip_step t tt = false).
Proof.
  destruct revocable_certificate_escapes as [Hinj [H1 H2]].
  split; [split; [repeat constructor; simpl; intuition discriminate | intros []; simpl; tauto] |].
  split; [exact H1 | split; [exact Hinj | exists true; split; [reflexivity | exact H2]]].
Qed.

(** Both can happen at once: the three cards merge and revoke. *)
Theorem nec_f_merge_and_revoke_flip :
  tri_mark T0 = false /\ tri_mark (tri_step T0 tt) = true /\
  ~ step_injective tri_step tt /\
  (exists t, tri_mark t = true /\ tri_mark (tri_step t tt) = false).
Proof.
  split; [reflexivity | split; [reflexivity | split]].
  - intro H. specialize (H T0 T2 eq_refl). discriminate.
  - exists T1. split; reflexivity.
Qed.

(** ** Forced price: how much decidability it needs *)

Section Isolated.

Variables (S I : Type).
Variable step : S -> I -> S.

(** Decidable equality on all moves can be cut down to: the one move can be
    told apart from every other. *)
Theorem nec_f_forced_iff_merges_isolated :
  forall i, (forall j, {j = i} + {j <> i}) ->
    forced_priced step i <-> ~ step_injective step i.
Proof.
  intros i iso. split.
  - intros Hforced Hinj.
    set (c := fun j => if iso j then 0 else 1).
    assert (Hp : merging_steps_priced step c).
    { intros j Hj. unfold c. destruct (iso j) as [-> | Hne]; [exfalso; exact (Hj Hinj) | lia]. }
    specialize (Hforced c Hp). unfold c in Hforced.
    destruct (iso i) as [_ | Hne]; [lia | apply Hne; reflexivity].
  - intros Hm cost Hp. exact (Hp i Hm).
Qed.

(** The backward half needs nothing at all. *)
Theorem nec_f_merges_forced :
  forall i, ~ step_injective step i -> forced_priced step i.
Proof. intros i Hm cost Hp. exact (Hp i Hm). Qed.

End Isolated.

(** The continuity principle: every function from sequences of bits to
    numbers depends only on a finite prefix of its input. It holds in
    Kleene's realizability model; Coq neither proves nor refutes it. *)
Definition nec_f_continuity : Prop :=
  forall (F : (nat -> bool) -> nat) (a : nat -> bool),
    exists n, forall b, (forall k, k < n -> b k = a k) -> F b = F a.

(** A machine whose moves are sequences of bits. Move a sends state m to 0
    when a shows a true bit at or below m, and leaves it alone otherwise. *)
Fixpoint nec_f_seen_true (a : nat -> bool) (m : nat) : bool :=
  match m with 0 => a 0 | S m' => a (S m') || nec_f_seen_true a m' end.

Definition nec_f_seq_step (m : nat) (a : nat -> bool) : nat :=
  if nec_f_seen_true a m then 0 else m.

Definition nec_f_zero_seq : nat -> bool := fun _ => false.

Lemma nec_f_seen_true_zero : forall m, nec_f_seen_true nec_f_zero_seq m = false.
Proof. induction m; simpl; [reflexivity | exact IHm]. Qed.

Lemma nec_f_seen_true_ge :
  forall a n m, a n = true -> n <= m -> nec_f_seen_true a m = true.
Proof.
  intros a n m Hn Hle. induction Hle as [| m Hle IH].
  - destruct n; simpl; [exact Hn | rewrite Hn; reflexivity].
  - simpl. rewrite IH. apply orb_true_r.
Qed.

Lemma nec_f_zero_seq_injective : step_injective nec_f_seq_step nec_f_zero_seq.
Proof.
  intros a b H. unfold nec_f_seq_step in H. rewrite !nec_f_seen_true_zero in H. exact H.
Qed.

Lemma nec_f_true_seq_merges :
  forall n, ~ step_injective nec_f_seq_step (fun k => Nat.eqb k n).
Proof.
  intros n Hinj.
  assert (Hn : (fun k => Nat.eqb k n) n = true) by apply Nat.eqb_refl.
  assert (H : nec_f_seq_step n (fun k => Nat.eqb k n) =
              nec_f_seq_step (S n) (fun k => Nat.eqb k n)).
  { unfold nec_f_seq_step.
    rewrite (nec_f_seen_true_ge _ n n Hn (le_n n)).
    rewrite (nec_f_seen_true_ge _ n (S n) Hn (le_S _ _ (le_n n))). reflexivity. }
  apply Hinj in H. lia.
Qed.

(** Under continuity, the all-false move forgets nothing and yet every cost
    that prices merges charges it: forced does not imply merging. So the
    forward half of "forced price is merging" cannot be proved without some
    decidability of moves. *)
Theorem nec_f_forced_without_merge_under_continuity :
  nec_f_continuity ->
  forced_priced nec_f_seq_step nec_f_zero_seq /\
  step_injective nec_f_seq_step nec_f_zero_seq.
Proof.
  intro Hcont. split; [| exact nec_f_zero_seq_injective].
  intros cost Hp.
  destruct (Hcont cost nec_f_zero_seq) as [n Hn].
  set (b := fun k => Nat.eqb k n).
  assert (Hb : forall k, k < n -> b k = nec_f_zero_seq k).
  { intros k Hk. unfold b, nec_f_zero_seq. apply Nat.eqb_neq. lia. }
  rewrite <- (Hn b Hb). apply Hp. apply nec_f_true_seq_merges.
Qed.

Corollary nec_f_forced_iff_merges_needs_decidability :
  nec_f_continuity ->
  ~ (forall i, forced_priced nec_f_seq_step i -> ~ step_injective nec_f_seq_step i).
Proof.
  intros Hcont H.
  destruct (nec_f_forced_without_merge_under_continuity Hcont) as [Hf Hi].
  exact (H _ Hf Hi).
Qed.

(** ** Permanent records are forced: finiteness and permanence are needed *)

(** Without finiteness: the history machine writes a permanent record and is
    not forced, since a free price prices its (absent) merges. *)
Theorem nec_f_forced_needs_finite :
  history_cert [] = false /\ history_cert (history_step [] tt) = true /\
  permanent_at history_step history_cert tt /\
  ~ forced_priced history_step tt.
Proof.
  destruct unbounded_history_escapes as [Hinj [Hperm [H0 H1]]].
  split; [exact H0 | split; [exact H1 | split; [intros t Ht; apply Hperm; exact Ht |]]].
  intro Hf. specialize (Hf (fun _ => 0)).
  assert (Hp : merging_steps_priced history_step (fun _ : unit => 0)).
  { intros [] Hm. exfalso. exact (Hm Hinj). }
  specialize (Hf Hp). cbn in *; lia.
Qed.

(** Without permanence: negation flips the bit on and is not forced. *)
Theorem nec_f_forced_needs_permanent :
  finite_states [false; true] /\ flip_step false tt = true /\
  ~ permanent_at flip_step (fun b => b) tt /\
  ~ forced_priced flip_step tt.
Proof.
  destruct revocable_certificate_escapes as [Hinj [H1 H2]].
  split; [split; [repeat constructor; simpl; intuition discriminate | intros []; simpl; tauto] |].
  split; [exact H1 | split].
  - intro Hp. specialize (Hp true eq_refl). simpl in Hp. discriminate.
  - intro Hf. specialize (Hf (fun _ => 0)).
    assert (Hp : merging_steps_priced flip_step (fun _ : unit => 0)).
    { intros [] Hm. exfalso. exact (Hm Hinj). }
    specialize (Hf Hp). cbn in *; lia.
Qed.

Print Assumptions nec_f_flip_not_injective_on_yes_and_s.
Print Assumptions nec_f_perm_flip_merges_yes_finite.
Print Assumptions nec_f_flip_collision_in_yes_and_s.
Print Assumptions nec_f_merge_or_revoke_yes_finite.
Print Assumptions nec_f_toll_from_merges_yes_finite.
Print Assumptions nec_f_a2_iff_flipping_merges_priced.
Print Assumptions nec_f_merging_priced_weakens.
Print Assumptions nec_f_repo_perm_flip_from_yes_finite.
Print Assumptions nec_f_no_flip_no_merge.
Print Assumptions nec_f_jump_merges_never_flips.
Print Assumptions nec_f_collision_avoids_s.
Print Assumptions nec_f_toll_needs_finite.
Print Assumptions nec_f_toll_needs_permanent.
Print Assumptions nec_f_a2_without_merge_pricing.
Print Assumptions nec_f_merge_or_revoke_needs_finite.
Print Assumptions nec_f_merge_only_flip.
Print Assumptions nec_f_revoke_only_flip.
Print Assumptions nec_f_merge_and_revoke_flip.
Print Assumptions nec_f_forced_iff_merges_isolated.
Print Assumptions nec_f_merges_forced.
Print Assumptions nec_f_forced_without_merge_under_continuity.
Print Assumptions nec_f_forced_iff_merges_needs_decidability.
Print Assumptions nec_f_forced_needs_finite.
Print Assumptions nec_f_forced_needs_permanent.
