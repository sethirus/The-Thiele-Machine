(** AxHostClaims: what one run of one host program can carry as a record.

    The host machine (EarnedMulti.v with the property PSlot) records a claim
    when its CHECK passes: the fact "PSlot holds of register r at its present
    version".  The claim itself is the register r.  The version only says
    which write of r the claim is about; it is not part of what was
    established, and reading it as part of the record would let a program
    store any number for the price of one CHECK (write the register n times
    for free, then CHECK).  So the record of a run is the set of registers
    named by the facts in its table, ordered by inclusion.

    Results (all closed):

      ax_claims_named        every claim in the table of any run of a program
                             is a register named by a CHECK instruction in
                             the text of that program.
      ax_fixed_program_few   a fixed program has finitely many records: among
                             any list of runs whose claim sets are pairwise
                             inequivalent, there are at most 2^m, where m is
                             the number of registers its CHECKs name.  So no
                             fixed program carries, by its claim set, an
                             axis with more pairwise inequivalent reachable
                             records than that, in particular none with
                             infinitely many.
      ax_cap_claims          no run holds more than 16 claims.
      ax_chain_realized      the cap is attained at every height: for every
                             list of up to 16 distinct registers there is a
                             program whose run, after the k INCs that set the
                             registers up, passes through exactly the claim
                             sets of the prefixes of the list.
      ax_single_run_boundary a chain of claim sets of strictly growing size is
                             the record sequence of one run of some host
                             program exactly when it has at most 16 steps.

    Where this stops.  This is the record of the host as an axis of claims.
    What the host's registers hold, and what the universal program decodes
    from them, is data and not record: AxHost.v states how the fixed
    universal program carries the guest's claims in registers and how the
    host's table follows the guest's table exactly. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Kernel Require Import AxCore AxRice.
Require Minimal.EntitlementSmall.
Require Import Minimal.SmHostBlocks.
Module M := Minimal.EarnedMulti.
Module UC := Minimal.UniversalCodes.

Local Notation hinstr := (@M.instr UC.hprop).
Local Notation hstate := (@M.state UC.hprop).
Local Notation hrun_prog := (M.run_prog UC.hprop_eqb UC.heval).
Local Notation hends := (sm_hends UC.hprop_eqb UC.heval).

(** * 1. The claims of a run *)

Definition ax_hclaims (s : hstate) : list nat := map M.f_reg (M.facts (M.core_of s)).

(** The registers a program's CHECK instructions name. *)
Definition ax_names (P : list hinstr) : list nat :=
  flat_map (fun i => match i with M.CHECK _ r => [r] | _ => [] end) P.

Lemma ax_fetch_in : forall (P : list hinstr) n i, M.fetch P n = Some i -> In i P.
Proof.
  intros P [| n] i H; [discriminate |]. simpl in H. eapply nth_error_In. exact H.
Qed.

Lemma ax_next_in : forall (P : list hinstr) (k : @M.core UC.hprop) i, M.next_instr P k = Some i -> In i P.
Proof.
  intros P k i H. unfold M.next_instr in H. destruct (M.err k); [discriminate |].
  destruct (M.fetch P (M.pc k)) as [j |] eqn:E; [| discriminate].
  apply ax_fetch_in in E. destruct j; try (injection H as <-; exact E); discriminate.
Qed.

Lemma ax_claims_named_step : forall (P : list hinstr) (s : hstate),
  (forall r, In r (ax_hclaims s) -> In r (ax_names P)) ->
  forall r, In r (ax_hclaims (M.step UC.hprop_eqb UC.heval P s)) -> In r (ax_names P).
Proof.
  intros P s H r Hr. unfold M.step in Hr.
  destruct (M.next_instr P (M.core_of s)) as [i |] eqn:En; [| apply H; exact Hr].
  apply ax_next_in in En.
  unfold ax_hclaims in Hr. apply in_map_iff in Hr as [f [<- Hf]].
  unfold M.exec in Hf. simpl in Hf.
  destruct (M.multi_facts_step UC.hprop_eqb UC.heval (M.core_of s) i f Hf) as [Hold | [Hi _]].
  - apply H. unfold ax_hclaims. apply in_map. exact Hold.
  - rewrite Hi in En. unfold ax_names. apply in_flat_map. exists (M.CHECK (M.f_prop f) (M.f_reg f)).
    split; [exact En | left; reflexivity].
Qed.

Lemma ax_claims_named_run : forall (P : list hinstr) n (s : hstate),
  (forall r, In r (ax_hclaims s) -> In r (ax_names P)) ->
  forall r, In r (ax_hclaims (hrun_prog n P s)) -> In r (ax_names P).
Proof.
  intros P n. induction n as [| n IH]; intros s H r Hr; [apply H; exact Hr |].
  simpl in Hr. eapply IH; [| exact Hr]. apply ax_claims_named_step. exact H.
Qed.

(** From any start with an empty table, every claim of every run is named
    in the text of the program. *)
Theorem ax_claims_named : forall (P : list hinstr) n (s : hstate),
  M.facts (M.core_of s) = [] ->
  forall r, In r (ax_hclaims (hrun_prog n P s)) -> In r (ax_names P).
Proof.
  intros P n s H0. apply ax_claims_named_run.
  intros q Hq. unfold ax_hclaims in Hq. rewrite H0 in Hq. destruct Hq.
Qed.

(** * 2. A fixed program has few records *)

Lemma ax_cap_claims : forall p x n,
  length (ax_hclaims (hrun_prog n p (@sm_hstart UC.hprop x))) <= 16.
Proof.
  intros p x n. unfold ax_hclaims. rewrite map_length. apply ax_facts_cap.
Qed.

Definition ax_vec (names : list nat) (s : hstate) : list bool :=
  map (fun r => existsb (Nat.eqb r) (ax_hclaims s)) names.

Lemma ax_existsb_in : forall r l, existsb (Nat.eqb r) l = true <-> In r l.
Proof.
  intros r l. rewrite existsb_exists. split.
  - intros [x [Hx He]]. apply Nat.eqb_eq in He. subst. exact Hx.
  - intro H. exists r. split; [exact H | apply Nat.eqb_refl].
Qed.

Lemma ax_map_eq_in : forall (f g : nat -> bool) l, map f l = map g l -> forall r, In r l -> f r = g r.
Proof.
  intros f g l. induction l as [| a l IH]; intros H r Hr; [destruct Hr |].
  simpl in H. injection H as H1 H2. destruct Hr as [<- | Hr]; [exact H1 | apply IH; assumption].
Qed.

Lemma ax_vec_equiv : forall names s t,
  (forall r, In r (ax_hclaims s) -> In r names) ->
  (forall r, In r (ax_hclaims t) -> In r names) ->
  ax_vec names s = ax_vec names t ->
  forall r, In r (ax_hclaims s) <-> In r (ax_hclaims t).
Proof.
  intros names s t Hs Ht Hv r. unfold ax_vec in Hv.
  assert (H : forall q, In q names -> existsb (Nat.eqb q) (ax_hclaims s) = existsb (Nat.eqb q) (ax_hclaims t))
    by (intros q Hq; exact (ax_map_eq_in Hv Hq)).
  split; intro Hr.
  - pose proof (H r (Hs r Hr)) as E. apply ax_existsb_in. rewrite <- E. apply ax_existsb_in. exact Hr.
  - pose proof (H r (Ht r Hr)) as E. apply ax_existsb_in. rewrite E. apply ax_existsb_in. exact Hr.
Qed.

Lemma ax_nodup_map_pairs : forall (f : nat -> list bool) (l : list nat),
  NoDup l -> (forall x y, In x l -> In y l -> f x = f y -> x = y) -> NoDup (map f l).
Proof.
  intros f l. induction l as [| a l IH]; intros Hnd H; simpl; [constructor |].
  inversion Hnd as [| ? ? Hn Hl]; subst.
  constructor.
  - intro Hin. apply in_map_iff in Hin as [y [Hy Hyl]].
    assert (a = y) by (apply H; [left; reflexivity | right; exact Hyl | symmetry; exact Hy]).
    subst. exact (Hn Hyl).
  - apply IH; [exact Hl |]. intros x y Hx Hy E. apply H; [right; exact Hx | right; exact Hy | exact E].
Qed.

(** A fixed program has at most 2^m pairwise inequivalent claim sets, where m
    is the number of registers its CHECKs name. *)
Theorem ax_fixed_program_few : forall (P : list hinstr) (N : nat) (g : nat -> nat * nat),
  (forall i j, i < N -> j < N -> i <> j ->
     ~ (forall r,
          In r (ax_hclaims (hrun_prog (snd (g i)) P (@sm_hstart UC.hprop (fst (g i)))))
          <-> In r (ax_hclaims (hrun_prog (snd (g j)) P (@sm_hstart UC.hprop (fst (g j))))))) ->
  N <= 2 ^ length (ax_names P).
Proof.
  intros P N g Hdist.
  set (st := fun i => hrun_prog (snd (g i)) P (@sm_hstart UC.hprop (fst (g i)))).
  set (vec := fun i => ax_vec (ax_names P) (st i)).
  assert (Hnamed : forall i, forall r, In r (ax_hclaims (st i)) -> In r (ax_names P)).
  { intros i r Hr. unfold st in Hr. eapply ax_claims_named; [| exact Hr]. reflexivity. }
  assert (Hnd : NoDup (map vec (seq 0 N))).
  { apply ax_nodup_map_pairs; [apply seq_NoDup |].
    intros x y Hx Hy E. apply in_seq in Hx. apply in_seq in Hy.
    destruct (Nat.eq_dec x y) as [| Hne]; [assumption |].
    exfalso. apply (Hdist x y); [lia | lia | exact Hne |].
    apply (ax_vec_equiv (names := ax_names P) (s := st x) (t := st y)); [apply Hnamed | apply Hnamed | exact E]. }
  assert (Hincl : incl (map vec (seq 0 N)) (Minimal.EntitlementSmall.ent_all_bools (length (ax_names P)))).
  { intros v Hv. apply in_map_iff in Hv as [i [<- _]].
    unfold vec, ax_vec.
    replace (length (ax_names P)) with (length (map (fun r => existsb (Nat.eqb r) (ax_hclaims (st i))) (ax_names P)))
      by (apply map_length).
    apply Minimal.EntitlementSmall.ent_all_bools_complete. }
  pose proof (NoDup_incl_length Hnd Hincl) as Hlen.
  rewrite map_length, seq_length, Minimal.EntitlementSmall.ent_all_bools_length in Hlen.
  exact Hlen.
Qed.

(** Hence no fixed program has an unbounded family of reachable records that
    are pairwise inequivalent as claim sets. *)
Corollary ax_fixed_program_no_infinite : forall (P : list hinstr) (g : nat -> nat * nat),
  ~ (forall i j, i <> j ->
       ~ (forall r,
            In r (ax_hclaims (hrun_prog (snd (g i)) P (@sm_hstart UC.hprop (fst (g i)))))
            <-> In r (ax_hclaims (hrun_prog (snd (g j)) P (@sm_hstart UC.hprop (fst (g j))))))).
Proof.
  intros P g H.
  assert (Hle : (2 ^ length (ax_names P) + 1 <= 2 ^ length (ax_names P))%nat).
  { apply (ax_fixed_program_few (P := P) (g := g)). intros i j _ _ Hne. exact (H i j Hne). }
  lia.
Qed.

(** * 3. The cap is attained at every height *)

Definition ax_mem (r : nat) (l : list nat) : bool := existsb (Nat.eqb r) l.

Definition ax_prog_chain (rs : list nat) : list hinstr :=
  map (fun r => M.INC r) rs ++ map (fun r => M.CHECK UC.PSlot r) rs ++ [M.HALT].

Definition ax_i1 (pre : list nat) (s : hstate) : Prop :=
  M.err (M.core_of s) = false /\ M.pc (M.core_of s) = S (length pre) /\
  M.facts (M.core_of s) = [] /\ M.chan (M.core_of s) = None /\ M.cert s = false /\
  (forall r, M.vals (M.core_of s) r = if ax_mem r pre then 1 else 0) /\
  (forall r, M.vers (M.core_of s) r = if ax_mem r pre then 1 else 0).

Lemma ax_mem_snoc : forall x pre r, ax_mem x (pre ++ [r]) = ax_mem x pre || Nat.eqb x r.
Proof.
  intros x pre r. unfold ax_mem. rewrite existsb_app. simpl. rewrite orb_false_r. reflexivity.
Qed.

Lemma ax_i1_zero : ax_i1 [] (@sm_hstart UC.hprop 0).
Proof.
  unfold ax_i1. repeat split; try reflexivity.
  intro r. simpl. unfold sm_hin. destruct (Nat.eqb r 1); reflexivity.
Qed.

Lemma ax_nth_split : forall (rs pre post : list nat) r,
  rs = pre ++ r :: post -> nth_error rs (length pre) = Some r.
Proof.
  intros rs pre post r ->. rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
Qed.

Lemma ax_fetch_inc : forall rs pre post r,
  rs = pre ++ r :: post ->
  M.fetch (ax_prog_chain rs) (S (length pre)) = Some (M.INC r).
Proof.
  intros rs pre post r H. unfold ax_prog_chain, M.fetch.
  simpl.
  rewrite nth_error_app1 by (rewrite map_length, H; rewrite app_length; simpl; lia).
  rewrite nth_error_map.
  change (option_map (fun r0 : nat => @M.INC UC.hprop r0) (nth_error rs (length pre)) = Some (@M.INC UC.hprop r)).
  rewrite (ax_nth_split H). reflexivity.
Qed.

Lemma ax_i1_step : forall rs pre post r s,
  rs = pre ++ r :: post -> NoDup rs -> ax_i1 pre s ->
  ax_i1 (pre ++ [r]) (M.step UC.hprop_eqb UC.heval (ax_prog_chain rs) s).
Proof.
  intros rs pre post r s Hrs Hnd (He & Hpc & Hf & Hch & Hc & Hv & Hver).
  assert (Hnotin : ax_mem r pre = false).
  { destruct (ax_mem r pre) eqn:E; [| reflexivity]. exfalso.
    apply ax_existsb_in in E. rewrite Hrs in Hnd.
    apply NoDup_remove_2 in Hnd. apply Hnd. apply in_or_app. left. exact E. }
  assert (Hnext : M.next_instr (ax_prog_chain rs) (M.core_of s) = Some (M.INC r)).
  { unfold M.next_instr. rewrite He, Hpc, (ax_fetch_inc Hrs). reflexivity. }
  unfold M.step. rewrite Hnext. unfold M.exec, M.cexec. rewrite He. simpl.
  unfold ax_i1. simpl.
  rewrite He. repeat split; try assumption.
  - rewrite Hpc. rewrite app_length. simpl. lia.
  - rewrite Hc. reflexivity.
  - intro x. rewrite ax_mem_snoc. unfold M.upd; cbv beta.
    destruct (Nat.eqb x r) eqn:E.
    + apply Nat.eqb_eq in E. subst x. rewrite (Hv r), Hnotin. reflexivity.
    + rewrite Hv. rewrite orb_false_r. reflexivity.
  - intro x. rewrite ax_mem_snoc. unfold M.upd; cbv beta.
    destruct (Nat.eqb x r) eqn:E.
    + apply Nat.eqb_eq in E. subst x. rewrite (Hver r), Hnotin. reflexivity.
    + rewrite Hver. rewrite orb_false_r. reflexivity.
Qed.

Lemma ax_i1_run : forall pre rs post,
  rs = pre ++ post -> NoDup rs ->
  ax_i1 pre (hrun_prog (length pre) (ax_prog_chain rs) (@sm_hstart UC.hprop 0)).
Proof.
  intro pre. induction pre as [| x pre IH] using rev_ind; intros rs post Hrs Hnd.
  - simpl. apply ax_i1_zero.
  - assert (Hl : length (pre ++ [x]) = S (length pre)) by (rewrite app_length; simpl; lia).
    rewrite Hl, M.multi_run_prog_succ.
    assert (Hrs' : rs = pre ++ x :: post) by (rewrite Hrs, <- app_assoc; reflexivity).
    eapply ax_i1_step; [exact Hrs' | exact Hnd |].
    exact (IH rs (x :: post) Hrs' Hnd).
Qed.

Definition ax_i2 (rs pre : list nat) (s : hstate) : Prop :=
  M.err (M.core_of s) = false /\ M.pc (M.core_of s) = S (length rs + length pre) /\
  ax_hclaims s = rev pre /\ M.chan (M.core_of s) = None /\ M.cert s = false /\
  (forall r, M.vals (M.core_of s) r = if ax_mem r rs then 1 else 0) /\
  (forall r, M.vers (M.core_of s) r = if ax_mem r rs then 1 else 0).

Lemma ax_i2_base : forall rs s, ax_i1 rs s -> ax_i2 rs [] s.
Proof.
  intros rs s (He & Hpc & Hf & Hch & Hc & Hv & Hver).
  unfold ax_i2. repeat split; try assumption.
  - rewrite Hpc. simpl. rewrite Nat.add_0_r. reflexivity.
  - unfold ax_hclaims. rewrite Hf. reflexivity.
Qed.

Lemma ax_fetch_chk2 : forall rs pre post r,
  rs = pre ++ r :: post ->
  M.fetch (ax_prog_chain rs) (S (length rs + length pre)) = Some (M.CHECK UC.PSlot r).
Proof.
  intros rs pre post r H. unfold ax_prog_chain, M.fetch. simpl.
  rewrite nth_error_app2 by (rewrite map_length; apply Nat.le_add_r).
  rewrite map_length, Nat.add_comm, Nat.add_sub.
  rewrite nth_error_app1 by (rewrite map_length, H; rewrite app_length; simpl; lia).
  rewrite nth_error_map.
  change (option_map (fun r0 : nat => @M.CHECK UC.hprop UC.PSlot r0) (nth_error rs (length pre))
          = Some (@M.CHECK UC.hprop UC.PSlot r)).
  rewrite (ax_nth_split H). reflexivity.
Qed.

Lemma ax_fetch_halt2 : forall rs,
  M.fetch (ax_prog_chain rs) (S (length rs + length rs)) = Some M.HALT.
Proof.
  intro rs. unfold ax_prog_chain, M.fetch. simpl.
  rewrite nth_error_app2 by (rewrite map_length; apply Nat.le_add_r).
  rewrite map_length, Nat.add_sub.
  rewrite nth_error_app2 by (rewrite map_length; apply Nat.le_refl).
  rewrite map_length, Nat.sub_diag. reflexivity.
Qed.

Lemma ax_i2_step : forall rs pre post r s,
  rs = pre ++ r :: post -> length rs <= 16 -> ax_i2 rs pre s ->
  ax_i2 rs (pre ++ [r]) (M.step UC.hprop_eqb UC.heval (ax_prog_chain rs) s).
Proof.
  intros rs pre post r s Hrs Hlen (He & Hpc & Hcl & Hch & Hc & Hv & Hver).
  assert (Hin : ax_mem r rs = true).
  { apply ax_existsb_in. rewrite Hrs. apply in_or_app. right. left. reflexivity. }
  assert (Hnext : M.next_instr (ax_prog_chain rs) (M.core_of s) = Some (M.CHECK UC.PSlot r)).
  { unfold M.next_instr. rewrite He, Hpc, (ax_fetch_chk2 Hrs). reflexivity. }
  assert (Hflen : length (M.facts (M.core_of s)) = length pre).
  { assert (E : length (ax_hclaims s) = length (rev pre)) by (rewrite Hcl; reflexivity).
    unfold ax_hclaims in E. rewrite map_length, rev_length in E. exact E. }
  assert (Hlt : length pre < length rs).
  { rewrite Hrs. rewrite app_length. simpl. lia. }
  assert (Hok : M.check_ok UC.heval (M.core_of s) UC.PSlot r = true).
  { unfold M.check_ok. rewrite He, (Hv r), Hin, Hflen. simpl.
    replace (UC.heval UC.PSlot 1) with true by reflexivity. simpl.
    apply Nat.ltb_lt. unfold M.fact_cap. lia. }
  unfold M.step. rewrite Hnext.
  rewrite (M.multi_exec_check_pass UC.hprop_eqb UC.heval s UC.PSlot r Hok).
  unfold ax_i2. simpl. repeat split; try assumption.
  - rewrite Hpc, app_length. simpl. lia.
  - unfold ax_hclaims in *. simpl. rewrite Hcl in *. simpl. rewrite rev_app_distr. simpl. reflexivity.
Qed.

Lemma ax_i2_run : forall pre rs post,
  rs = pre ++ post -> NoDup rs -> length rs <= 16 ->
  ax_i2 rs pre (hrun_prog (length rs + length pre) (ax_prog_chain rs) (@sm_hstart UC.hprop 0)).
Proof.
  intro pre. induction pre as [| x pre IH] using rev_ind; intros rs post Hrs Hnd Hlen.
  - simpl. rewrite Nat.add_0_r. apply ax_i2_base. subst rs. rewrite app_nil_l in *.
    exact (ax_i1_run (eq_sym (app_nil_r post)) Hnd).
  - assert (Hl : (length rs + length (pre ++ [x]) = S (length rs + length pre))%nat)
      by (rewrite app_length; simpl; lia).
    rewrite Hl, M.multi_run_prog_succ.
    assert (Hrs' : rs = pre ++ x :: post) by (rewrite Hrs, <- app_assoc; reflexivity).
    eapply ax_i2_step; [exact Hrs' | exact Hlen |].
    exact (IH rs (x :: post) Hrs' Hnd Hlen).
Qed.

(** The record after the k INCs and j CHECKs of the program for the register
    list rs is the claim set of the first j registers. *)
Theorem ax_chain_realized : forall rs,
  NoDup rs -> length rs <= 16 ->
  (forall j, j <= length rs ->
     ax_hclaims (hrun_prog (length rs + j) (ax_prog_chain rs) (@sm_hstart UC.hprop 0))
     = rev (firstn j rs)) /\
  hends (ax_prog_chain rs) 0
    (hrun_prog (length rs + length rs) (ax_prog_chain rs) (@sm_hstart UC.hprop 0)).
Proof.
  intros rs Hnd Hlen. split.
  - intros j Hj.
    pose proof (ax_i2_run (eq_sym (firstn_skipn j rs)) Hnd Hlen) as H.
    rewrite (firstn_length_le rs Hj) in H.
    destruct H as (_ & _ & Hcl & _). exact Hcl.
  - pose proof (ax_i2_run (pre := rs) (post := []) (eq_sym (app_nil_r rs)) Hnd Hlen) as H.
    destruct H as (He & Hpc & _).
    exists (length rs + length rs). split; [reflexivity |].
    unfold M.halted, M.next_instr. rewrite He, Hpc, ax_fetch_halt2. reflexivity.
Qed.

(** * 4. The exact boundary: a chain of growing claim sets has at most 16 steps *)

Lemma ax_nodup_len_le : forall l : list nat, length (nodup Nat.eq_dec l) <= length l.
Proof.
  intro l. apply NoDup_incl_length; [apply NoDup_nodup |].
  intros x Hx. apply nodup_In in Hx. exact Hx.
Qed.

Lemma ax_strict_len : forall a b : list nat,
  incl a b -> (exists x, In x b /\ ~ In x a) ->
  length (nodup Nat.eq_dec a) < length (nodup Nat.eq_dec b).
Proof.
  intros a b Hab [x [Hxb Hxa]].
  assert (Hnd : NoDup (x :: nodup Nat.eq_dec a)).
  { constructor; [intro H; apply Hxa; apply nodup_In in H; exact H | apply NoDup_nodup]. }
  assert (Hin : incl (x :: nodup Nat.eq_dec a) (nodup Nat.eq_dec b)).
  { intros y [<- | Hy]; apply nodup_In; [exact Hxb |]. apply nodup_In in Hy. apply Hab. exact Hy. }
  pose proof (NoDup_incl_length Hnd Hin) as H. simpl in H. lia.
Qed.

(** Along any chain c_0, c_1, ..., c_m of claim sets of runs of any program,
    each strictly inside the next, m is at most 16. *)
Theorem ax_chain_at_most_16 : forall (P : list hinstr) (m : nat) (g : nat -> nat * nat),
  (forall i, i < m ->
     incl (ax_hclaims (hrun_prog (snd (g i)) P (@sm_hstart UC.hprop (fst (g i)))))
          (ax_hclaims (hrun_prog (snd (g (S i))) P (@sm_hstart UC.hprop (fst (g (S i))))))
     /\ exists x, In x (ax_hclaims (hrun_prog (snd (g (S i))) P (@sm_hstart UC.hprop (fst (g (S i))))))
                  /\ ~ In x (ax_hclaims (hrun_prog (snd (g i)) P (@sm_hstart UC.hprop (fst (g i)))))) ->
  m <= 16.
Proof.
  intros P m g H.
  set (c := fun i => ax_hclaims (hrun_prog (snd (g i)) P (@sm_hstart UC.hprop (fst (g i))))).
  assert (Hc : forall i, i <= m -> i <= length (nodup Nat.eq_dec (c i))).
  { induction i as [| i IH]; intro Hi; [lia |].
    destruct (H i (ltac:(lia))) as [Hinc Hex].
    pose proof (ax_strict_len (a := c i) (b := c (S i)) Hinc Hex) as Hs.
    pose proof (IH (ltac:(lia))). lia. }
  pose proof (Hc m (le_n m)) as H1.
  pose proof (ax_nodup_len_le (c m)) as H2.
  pose proof (ax_cap_claims P (fst (g m)) (snd (g m))) as H3.
  change (length (c m) <= 16) in H3. lia.
Qed.

(** Conversely every chain of at most 16 steps is realized by one run. *)
Theorem ax_chain_of_16_realized : forall m, m <= 16 ->
  exists (P : list hinstr) (g : nat -> nat * nat),
    forall i, i < m ->
      incl (ax_hclaims (hrun_prog (snd (g i)) P (@sm_hstart UC.hprop (fst (g i)))))
           (ax_hclaims (hrun_prog (snd (g (S i))) P (@sm_hstart UC.hprop (fst (g (S i))))))
      /\ exists x, In x (ax_hclaims (hrun_prog (snd (g (S i))) P (@sm_hstart UC.hprop (fst (g (S i))))))
                   /\ ~ In x (ax_hclaims (hrun_prog (snd (g i)) P (@sm_hstart UC.hprop (fst (g i))))).
Proof.
  intros m Hm.
  set (rs := seq 100 m).
  assert (Hnd : NoDup rs) by apply seq_NoDup.
  assert (Hlen : length rs <= 16) by (unfold rs; rewrite seq_length; lia).
  destruct (ax_chain_realized Hnd Hlen) as [Hcl _].
  exists (ax_prog_chain rs), (fun i => (0, length rs + i)).
  intros i Hi. simpl.
  assert (Hlr : length rs = m) by (unfold rs; apply seq_length).
  rewrite (Hcl i (ltac:(lia))), (Hcl (S i) (ltac:(lia))).
  pose proof (firstn_skipn i rs) as Hsplit.
  destruct (skipn i rs) as [| r post] eqn:Hsk.
  - exfalso. assert (length (skipn i rs) = length rs - i) by apply skipn_length.
    rewrite Hsk in H. simpl in H. lia.
  - assert (Hrs : rs = firstn i rs ++ r :: post) by (rewrite <- Hsk; symmetry; apply firstn_skipn).
    assert (Hfi : length (firstn i rs) = i) by (apply firstn_length_le; lia).
    assert (HS : firstn (S i) rs = firstn i rs ++ [r]).
    { assert (E : firstn (S i) (firstn i rs ++ r :: post) = firstn i rs ++ [r]).
      { rewrite firstn_app. rewrite firstn_all2 by (rewrite Hfi; lia). rewrite Hfi.
        replace (S i - i) with 1 by lia. simpl. reflexivity. }
      rewrite <- Hrs in E. exact E. }
    rewrite HS. rewrite rev_app_distr. simpl. split.
    + intros x Hx. right. exact Hx.
    + exists r. split; [left; reflexivity |].
      intro Hin. apply in_rev in Hin.
      rewrite Hrs in Hnd. apply NoDup_remove_2 in Hnd. apply Hnd. apply in_or_app. left. exact Hin.
Qed.

(** The boundary: m strict steps of one run's claim set are possible exactly
    when m is at most 16. *)
Theorem ax_single_run_boundary : forall m,
  (exists (P : list hinstr) (g : nat -> nat * nat),
    forall i, i < m ->
      incl (ax_hclaims (hrun_prog (snd (g i)) P (@sm_hstart UC.hprop (fst (g i)))))
           (ax_hclaims (hrun_prog (snd (g (S i))) P (@sm_hstart UC.hprop (fst (g (S i))))))
      /\ exists x, In x (ax_hclaims (hrun_prog (snd (g (S i))) P (@sm_hstart UC.hprop (fst (g (S i))))))
                   /\ ~ In x (ax_hclaims (hrun_prog (snd (g i)) P (@sm_hstart UC.hprop (fst (g i)))))) <->
  m <= 16.
Proof.
  intro m. split.
  - intros [P [g H]]. exact (ax_chain_at_most_16 (P := P) (g := g) H).
  - apply ax_chain_of_16_realized.
Qed.

Print Assumptions ax_claims_named.
Print Assumptions ax_fixed_program_few.
Print Assumptions ax_fixed_program_no_infinite.
Print Assumptions ax_cap_claims.
Print Assumptions ax_chain_realized.
Print Assumptions ax_single_run_boundary.
