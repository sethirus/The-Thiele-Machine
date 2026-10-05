(** SmHostBlocks.v: programs of the host machine put together from blocks.

    The host machine is the machine of EarnedMulti.v: a counter for every
    register number, INC, DEC, HALT, CHECK, COMMIT, CERTIFY, the ledger, the
    flag, the fact table, the channel and the trap latch. Its property
    language is left open here, as in EarnedMulti.v.

    A block B placed at offset off inside a bigger program Q is B with every
    jump target moved: a target j inside B (1 <= j <= length B) becomes
    j + off, and a target outside B becomes the line just after the block,
    S (length B + off). So "leave B" always means "go to the line after the
    block", and a block at the end of Q halts where B halts.

    What is proved:
      1. A run of B and the matching run of the block inside Q stay related
         step for step: same register values, same versions on the
         registers B names, same fact table, channel, trap latch, ledger and
         flag, and the program counter moved by the offset
         [sm_block_step, sm_block_run_mid, sm_block_run_final].
      2. A block at the end of Q halts exactly when B halts
         [sm_block_halted, sm_block_not_halted].
      3. A row of c copies of INC r adds c to register r and touches nothing
         else that a program can read [sm_incs_run].
      4. The one instruction DEC r L, placed at line L, empties register r
         and then falls through [sm_clear_run].

    Dependencies: Coq standard library and EarnedMulti.v. No axioms, no
    Admitted.                                                              *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Minimal.EarnedMulti.
Module M := Minimal.EarnedMulti.

Section Blocks.

Context {prop : Type}.
Variable prop_eqb : prop -> prop -> bool.
Variable eval : prop -> nat -> bool.

Local Notation instr := (@M.instr prop).
Local Notation core := (@M.core prop).
Local Notation state := (@M.state prop).
Local Notation cexec := (M.cexec prop_eqb eval).
Local Notation exec := (M.exec prop_eqb eval).
Local Notation step := (M.step prop_eqb eval).
Local Notation run_prog := (M.run_prog prop_eqb eval).

(* ================================================================= *)
(* Inputs and halting.                                                *)
(* ================================================================= *)

(* The input convention: the input x sits in register 1, every other
   register holds 0. Register 0 is where a result is read. *)
Definition sm_hin (x : nat) : nat -> nat := fun r => if Nat.eqb r 1 then x else 0.

Definition sm_hstart (x : nat) : state := M.start (sm_hin x).

(* Program P, started on x, has stopped by step n and its state then is s. *)
Definition sm_hends (P : list instr) (x : nat) (s : state) : Prop :=
  exists n, s = run_prog n P (sm_hstart x) /\ M.halted P (M.core_of s).

(* What a program can read of a final state: every register value, the
   fact table, the channel, the trap latch, the ledger and the flag. Not
   the program counter and not the versions. *)
Definition sm_hagree (s t : state) : Prop :=
  (forall r, M.vals (M.core_of s) r = M.vals (M.core_of t) r) /\
  M.facts (M.core_of s) = M.facts (M.core_of t) /\
  M.chan (M.core_of s) = M.chan (M.core_of t) /\
  M.err (M.core_of s) = M.err (M.core_of t) /\
  M.mu s = M.mu t /\ M.cert s = M.cert t.

(* Two programs behave the same: on every input both run forever, or both
   stop and their final states agree on everything readable. *)
Definition sm_hequiv (P Q : list instr) : Prop :=
  forall x,
    (forall s, sm_hends P x s -> exists t, sm_hends Q x t /\ sm_hagree s t) /\
    (forall t, sm_hends Q x t -> exists s, sm_hends P x s /\ sm_hagree s t).

(* The partial function of one number a program computes: started on x,
   it stops, and register 0 then holds y. *)
Definition sm_hfun (P : list instr) (x y : nat) : Prop :=
  exists s, sm_hends P x s /\ M.vals (M.core_of s) 0 = y.

Lemma sm_hagree_sym : forall s t, sm_hagree s t -> sm_hagree t s.
Proof.
  intros s t (Hv & Hf & Hc & He & Hm & Hk).
  split; [intro r; symmetry; apply Hv |]. repeat split; auto.
Qed.

Lemma sm_hequiv_sym : forall P Q, sm_hequiv P Q -> sm_hequiv Q P.
Proof.
  intros P Q H x. destruct (H x) as [H1 H2]. split.
  - intros t Ht. destruct (H2 t Ht) as [s [Hs Ha]]. exists s. split; [exact Hs |].
    apply sm_hagree_sym, Ha.
  - intros s Hs. destruct (H1 s Hs) as [t [Ht Ha]]. exists t. split; [exact Ht |].
    apply sm_hagree_sym, Ha.
Qed.

Lemma sm_hequiv_hfun : forall P Q, sm_hequiv P Q -> forall x y, sm_hfun P x y <-> sm_hfun Q x y.
Proof.
  intros P Q H x y. destruct (H x) as [H1 H2]. split.
  - intros [s [Hs Hy]]. destruct (H1 s Hs) as [t [Ht [Hv _]]].
    exists t. split; [exact Ht |]. rewrite <- Hv. exact Hy.
  - intros [t [Ht Hy]]. destruct (H2 t Ht) as [s [Hs [Hv _]]].
    exists s. split; [exact Hs |]. rewrite Hv. exact Hy.
Qed.

(* ================================================================= *)
(* Runs at the level of the core.                                     *)
(* ================================================================= *)

(* One step of the core alone: the next core never reads the ledger or
   the flag. *)
Definition sm_cstep (P : list instr) (k : core) : core :=
  match M.next_instr P k with None => k | Some i => cexec k i end.

Lemma sm_step_core : forall P s, M.core_of (step P s) = sm_cstep P (M.core_of s).
Proof.
  intros P s. unfold step, sm_cstep. destruct (M.next_instr P (M.core_of s)); reflexivity.
Qed.

Lemma sm_run_add : forall a b P s, run_prog (a + b) P s = run_prog b P (run_prog a P s).
Proof. intros. apply M.multi_run_prog_add. Qed.

Lemma sm_run_succ : forall n P s, run_prog (S n) P s = run_prog n P (step P s).
Proof. reflexivity. Qed.

Lemma sm_halted_stay : forall n P s, M.halted P (M.core_of s) -> run_prog n P s = s.
Proof. intros. apply M.multi_run_prog_halted. assumption. Qed.

Lemma sm_halted_after : forall a b P s, a <= b ->
  M.halted P (M.core_of (run_prog a P s)) -> run_prog b P s = run_prog a P s.
Proof.
  intros a b P s Hle H. replace b with (a + (b - a)) by lia.
  rewrite sm_run_add. apply sm_halted_stay. exact H.
Qed.

(* The final state of a run that stops is unique. *)
Lemma sm_hends_unique : forall P x s t, sm_hends P x s -> sm_hends P x t -> s = t.
Proof.
  intros P x s t [n [-> Hn]] [m [-> Hm]]. destruct (le_ge_dec n m) as [H | H].
  - symmetry. apply sm_halted_after; assumption.
  - apply sm_halted_after; assumption.
Qed.

Lemma sm_hfun_det : forall P x y z, sm_hfun P x y -> sm_hfun P x z -> y = z.
Proof.
  intros P x y z [s [Hs Hy]] [t [Ht Hz]].
  rewrite (sm_hends_unique P x s t Hs Ht) in Hy. congruence.
Qed.

(* ================================================================= *)
(* Blocks.                                                            *)
(* ================================================================= *)

Definition sm_rj (off len j : nat) : nat :=
  if (1 <=? j) && (j <=? len) then j + off else S (len + off).

Definition sm_ri (off len : nat) (i : instr) : instr :=
  match i with M.DEC r j => M.DEC r (sm_rj off len j) | _ => i end.

Definition sm_reloc (off : nat) (B : list instr) : list instr :=
  map (sm_ri off (length B)) B.

Lemma sm_reloc_length : forall off B, length (sm_reloc off B) = length B.
Proof. intros. unfold sm_reloc. apply map_length. Qed.

(* Q holds the block B at offset off. *)
Definition sm_embeds (Q B : list instr) (off : nat) : Prop :=
  forall p, 1 <= p <= length B ->
    M.fetch Q (p + off) = option_map (sm_ri off (length B)) (M.fetch B p).

Lemma sm_embeds_app : forall A B C,
  sm_embeds (A ++ sm_reloc (length A) B ++ C) B (length A).
Proof.
  intros A B C p Hp. destruct p as [| p]; [lia |].
  replace (S p + length A) with (S (length A + p)) by lia. simpl M.fetch.
  rewrite nth_error_app2 by lia. replace (length A + p - length A) with p by lia.
  rewrite nth_error_app1 by (rewrite sm_reloc_length; lia).
  unfold sm_reloc. rewrite nth_error_map. reflexivity.
Qed.

Lemma sm_fetch_app_past : forall (A B : list instr) n,
  length A + length B < n -> M.fetch (A ++ B) n = None.
Proof.
  intros A B n H. destruct n as [| n]; [reflexivity |]. simpl.
  apply nth_error_None. rewrite app_length. lia.
Qed.

Lemma sm_fetch_app_left : forall (A B : list instr) n,
  n <= length A -> M.fetch (A ++ B) n = M.fetch A n.
Proof.
  intros A B n H. destruct n as [| n]; [reflexivity |]. simpl.
  apply nth_error_app1. lia.
Qed.

Lemma sm_fetch_range : forall (B : list instr) p i, M.fetch B p = Some i -> 1 <= p <= length B.
Proof.
  intros B p i H. destruct p as [| p]; [discriminate |]. simpl in H.
  assert (p < length B) by (apply nth_error_Some; congruence). lia.
Qed.

Lemma sm_fetch_out : forall (B : list instr) p, ~ (1 <= p <= length B) -> M.fetch B p = None.
Proof.
  intros B p H. destruct p as [| p]; [reflexivity |]. simpl.
  apply nth_error_None. lia.
Qed.

Lemma sm_rj_in : forall off len j, 1 <= j <= len -> sm_rj off len j = j + off.
Proof.
  intros off len j H. unfold sm_rj.
  replace ((1 <=? j) && (j <=? len)) with true; [reflexivity |].
  symmetry. apply andb_true_iff. split; apply Nat.leb_le; lia.
Qed.

Lemma sm_rj_out : forall off len j, ~ (1 <= j <= len) -> sm_rj off len j = S (len + off).
Proof.
  intros off len j H. unfold sm_rj.
  destruct (1 <=? j) eqn:E1, (j <=? len) eqn:E2; simpl; try reflexivity.
  apply Nat.leb_le in E1. apply Nat.leb_le in E2. lia.
Qed.

Lemma sm_rj_S : forall off len p, 1 <= p <= len -> sm_rj off len (S p) = S (p + off).
Proof.
  intros off len p H. destruct (le_lt_dec (S p) len) as [H1 | H1].
  - rewrite sm_rj_in by lia. lia.
  - rewrite sm_rj_out by lia. lia.
Qed.

(* Related cores: B's core k and Q's core k'. Sr is a set of registers on
   which the versions agree; every CHECK and COMMIT of B names a register
   in it. INC and DEC never read a version, so they may name any register. *)
Definition sm_crel (Sr : nat -> Prop) (off len : nat) (k k' : core) : Prop :=
  (forall r, M.vals k r = M.vals k' r) /\
  (forall r, Sr r -> M.vers k r = M.vers k' r) /\
  M.facts k = M.facts k' /\ M.chan k = M.chan k' /\ M.err k = M.err k' /\
  M.pc k' = sm_rj off len (M.pc k).

Definition sm_srel (Sr : nat -> Prop) (off len : nat) (s s' : state) : Prop :=
  sm_crel Sr off len (M.core_of s) (M.core_of s') /\ M.mu s = M.mu s' /\ M.cert s = M.cert s'.

Definition sm_within (Sr : nat -> Prop) (B : list instr) : Prop :=
  forall i r, In i B -> M.mentions i r = true -> M.plain i = false -> Sr r.

Lemma sm_cost_ri : forall off len i, M.cost (sm_ri off len i) = M.cost i.
Proof. intros off len []; reflexivity. Qed.

Lemma sm_ri_halt : forall off len i, sm_ri off len i = M.HALT <-> i = M.HALT.
Proof. intros off len []; simpl; split; intro H; congruence. Qed.

Lemma sm_next_some : forall (P : list instr) k i, M.next_instr P k = Some i ->
  M.err k = false /\ M.fetch P (M.pc k) = Some i /\ i <> M.HALT.
Proof.
  intros P k i H. unfold M.next_instr in H. destruct (M.err k); [discriminate |].
  destruct (M.fetch P (M.pc k)) as [[] |]; inversion H; subst;
    repeat split; try reflexivity; discriminate.
Qed.

Lemma sm_next_intro : forall (P : list instr) k i,
  M.err k = false -> M.fetch P (M.pc k) = Some i -> i <> M.HALT -> M.next_instr P k = Some i.
Proof.
  intros P k i He Hf Hi. unfold M.next_instr. rewrite He, Hf.
  destruct i; try reflexivity. congruence.
Qed.

Lemma sm_block_cstep : forall Sr Q B off k k' i,
  sm_embeds Q B off -> sm_within Sr B -> sm_crel Sr off (length B) k k' ->
  M.next_instr B k = Some i ->
  M.next_instr Q k' = Some (sm_ri off (length B) i) /\
  sm_crel Sr off (length B) (cexec k i) (cexec k' (sm_ri off (length B) i)).
Proof.
  intros Sr Q B off k k' i Hemb Hwin (Hv & Hw & Hf & Hc & He & Hp) Hn.
  destruct (sm_next_some B k i Hn) as (Ek & Hfe & Hh).
  assert (Hr : 1 <= M.pc k <= length B) by (eapply sm_fetch_range; eauto).
  assert (Hin : In i B).
  { destruct (M.pc k) as [| q]; [lia |]. simpl in Hfe. eapply nth_error_In; eauto. }
  rewrite sm_rj_in in Hp by exact Hr.
  assert (Hq : M.fetch Q (M.pc k') = Some (sm_ri off (length B) i)).
  { rewrite Hp, (Hemb _ Hr), Hfe. reflexivity. }
  assert (Ek' : M.err k' = false) by congruence.
  split.
  { apply sm_next_intro; [exact Ek' | exact Hq |]. intro H. apply sm_ri_halt in H. auto. }
  unfold M.cexec. rewrite Ek, Ek'.
  destruct i as [r | r j | | p r | p r |]; cbv beta iota delta [sm_ri].
  - (* INC *)
    unfold sm_crel. rewrite <- (Hv r). repeat split.
    + intro q. rewrite !M.multi_val_write. destruct (Nat.eqb r q); auto.
    + intros q Hq'. rewrite !M.multi_ver_write. rewrite (Hw q Hq'). reflexivity.
    + simpl. exact Hf.
    + simpl. exact Hc.
    + simpl. exact He.
    + simpl. rewrite Hp, sm_rj_S by exact Hr. reflexivity.
  - (* DEC *)
    rewrite <- (Hv r). destruct (M.vals k r) as [| v].
    + unfold sm_crel. simpl. repeat split; auto.
      rewrite Hp, sm_rj_S by exact Hr. reflexivity.
    + unfold sm_crel. repeat split.
      * intro q. rewrite !M.multi_val_write. destruct (Nat.eqb r q); auto.
      * intros q Hq'. rewrite !M.multi_ver_write. rewrite (Hw q Hq'). reflexivity.
      * simpl. exact Hf.
      * simpl. exact Hc.
      * simpl. exact He.
  - (* HALT *) congruence.
  - (* CHECK *)
    assert (Hs : Sr r) by (apply (Hwin _ r Hin); simpl; [apply Nat.eqb_refl | reflexivity]).
    assert (Hok : M.check_ok eval k p r = M.check_ok eval k' p r).
    { unfold M.check_ok. rewrite Ek, Ek', (Hv r), Hf. reflexivity. }
    rewrite Hok. destruct (M.check_ok eval k' p r).
    + unfold sm_crel, M.record_fact, M.claim. simpl. repeat split; auto.
      * rewrite (Hw r Hs), Hf. reflexivity.
      * rewrite Hp, sm_rj_S by exact Hr. reflexivity.
    + unfold sm_crel, M.trap. simpl. repeat split; auto.
      rewrite Hp, sm_rj_in by exact Hr. reflexivity.
  - (* COMMIT *)
    assert (Hs : Sr r) by (apply (Hwin _ r Hin); simpl; [apply Nat.eqb_refl | reflexivity]).
    assert (Hcl : M.claim k p r = M.claim k' p r).
    { unfold M.claim. rewrite (Hw r Hs). reflexivity. }
    assert (Hok : M.commit_ok prop_eqb k p r = M.commit_ok prop_eqb k' p r).
    { unfold M.commit_ok. rewrite Ek, Ek', Hcl, Hf. reflexivity. }
    rewrite Hok. destruct (M.commit_ok prop_eqb k' p r).
    + unfold sm_crel, M.commit_to. simpl. rewrite Hcl. repeat split; auto.
      rewrite Hp, sm_rj_S by exact Hr. reflexivity.
    + unfold sm_crel, M.trap. simpl. repeat split; auto.
      rewrite Hp, sm_rj_in by exact Hr. reflexivity.
  - (* CERTIFY *)
    assert (Hok : M.certify_ok k = M.certify_ok k').
    { unfold M.certify_ok. rewrite Ek, Ek', Hc. reflexivity. }
    rewrite Hok. destruct (M.certify_ok k').
    + unfold sm_crel, M.goto. simpl. repeat split; auto.
      rewrite Hp, sm_rj_S by exact Hr. reflexivity.
    + unfold sm_crel, M.trap. simpl. repeat split; auto.
      rewrite Hp, sm_rj_in by exact Hr. reflexivity.
Qed.

Lemma sm_fires_ri : forall off len k k' i,
  M.err k = M.err k' -> M.chan k = M.chan k' ->
  M.fires k i = M.fires k' (sm_ri off len i).
Proof.
  intros off len k k' i He Hc. destruct i; try reflexivity. simpl.
  unfold M.certify_ok. rewrite He, Hc. reflexivity.
Qed.

Lemma sm_block_step : forall Sr Q B off s s' i,
  sm_embeds Q B off -> sm_within Sr B -> sm_srel Sr off (length B) s s' ->
  M.next_instr B (M.core_of s) = Some i ->
  M.next_instr Q (M.core_of s') = Some (sm_ri off (length B) i) /\
  sm_srel Sr off (length B) (step B s) (step Q s').
Proof.
  intros Sr Q B off s s' i Hemb Hwin [Hc [Hm Hk]] Hn.
  destruct (sm_block_cstep Sr Q B off _ _ i Hemb Hwin Hc Hn) as [Hn' Hc'].
  split; [exact Hn' |].
  unfold step. rewrite Hn, Hn'. unfold sm_srel, M.exec. simpl.
  split; [exact Hc' |]. rewrite sm_cost_ri, Hm. split; [reflexivity |].
  destruct Hc as (_ & _ & _ & Hch & He & _).
  rewrite Hk, (sm_fires_ri off (length B) _ _ i He Hch). reflexivity.
Qed.

(* While B has not stopped, the block keeps step with it. *)
Lemma sm_block_run_mid : forall Sr Q B off,
  sm_embeds Q B off -> sm_within Sr B ->
  forall n s s', sm_srel Sr off (length B) s s' ->
  (forall m, m < n -> M.next_instr B (M.core_of (run_prog m B s)) <> None) ->
  sm_srel Sr off (length B) (run_prog n B s) (run_prog n Q s').
Proof.
  intros Sr Q B off Hemb Hwin n. induction n as [| n IH]; intros s s' Hs Hgo; [exact Hs |].
  destruct (M.next_instr B (M.core_of s)) as [i |] eqn:Hn;
    [| exfalso; apply (Hgo 0); [lia | exact Hn]].
  destruct (sm_block_step Sr Q B off s s' i Hemb Hwin Hs Hn) as [_ Hs'].
  rewrite !sm_run_succ. apply IH; [exact Hs' |].
  intros m Hm. rewrite <- sm_run_succ. apply Hgo. lia.
Qed.

(* A running B means a running block. *)
Lemma sm_block_not_halted : forall Sr Q B off s s',
  sm_embeds Q B off -> sm_within Sr B -> sm_srel Sr off (length B) s s' ->
  M.next_instr B (M.core_of s) <> None -> M.next_instr Q (M.core_of s') <> None.
Proof.
  intros Sr Q B off s s' Hemb Hwin Hs Hn.
  destruct (M.next_instr B (M.core_of s)) as [i |] eqn:Hb; [| congruence].
  destruct (sm_block_step Sr Q B off s s' i Hemb Hwin Hs Hb) as [H _]. congruence.
Qed.

(* A block at the end of Q stops where B stops. *)
Lemma sm_block_halted : forall Sr Q B off k k',
  sm_embeds Q B off -> length Q = off + length B -> sm_crel Sr off (length B) k k' ->
  M.halted B k -> M.halted Q k'.
Proof.
  intros Sr Q B off k k' Hemb HQ (_ & _ & _ & _ & He & Hp) Hh.
  unfold M.halted, M.next_instr in *. rewrite <- He.
  destruct (M.err k); [reflexivity |].
  destruct (le_lt_dec 1 (M.pc k)) as [H1 | H1];
    [destruct (le_lt_dec (M.pc k) (length B)) as [H2 | H2] |].
  - rewrite Hp, sm_rj_in by lia. rewrite (Hemb _ (conj H1 H2)).
    destruct (M.fetch B (M.pc k)) as [[] |]; simpl in *; try discriminate; reflexivity.
  - rewrite Hp, sm_rj_out by lia. rewrite sm_fetch_out by lia. reflexivity.
  - rewrite Hp, sm_rj_out by lia. rewrite sm_fetch_out by lia. reflexivity.
Qed.

Lemma sm_block_run_final : forall Sr Q B off,
  sm_embeds Q B off -> sm_within Sr B -> length Q = off + length B ->
  forall n s s', sm_srel Sr off (length B) s s' ->
  sm_srel Sr off (length B) (run_prog n B s) (run_prog n Q s').
Proof.
  intros Sr Q B off Hemb Hwin HQ n. induction n as [| n IH]; intros s s' Hs; [exact Hs |].
  rewrite !sm_run_succ.
  destruct (M.next_instr B (M.core_of s)) as [i |] eqn:Hn.
  - destruct (sm_block_step Sr Q B off s s' i Hemb Hwin Hs Hn) as [_ Hs']. apply IH, Hs'.
  - assert (HQh : M.halted Q (M.core_of s'))
      by (apply (sm_block_halted Sr Q B off (M.core_of s)); [exact Hemb | exact HQ | apply Hs | exact Hn]).
    unfold step. rewrite Hn. unfold M.halted in HQh. rewrite HQh. apply IH, Hs.
Qed.

(* ================================================================= *)
(* Steps that only move counters.                                     *)
(* ================================================================= *)

Lemma sm_plain_exec : forall s i, M.plain i = true ->
  M.facts (M.core_of (exec s i)) = M.facts (M.core_of s) /\
  M.chan (M.core_of (exec s i)) = M.chan (M.core_of s) /\
  M.err (M.core_of (exec s i)) = M.err (M.core_of s) /\
  M.mu (exec s i) = M.mu s /\ M.cert (exec s i) = M.cert s.
Proof. intros. apply M.multi_plain_step. assumption. Qed.

(* A row of c copies of INC r at lines off+1 .. off+c. *)
Definition sm_incs (r c : nat) : list instr := repeat (M.INC r) c.

Lemma sm_incs_length : forall r c, length (sm_incs r c) = c.
Proof. intros. apply repeat_length. Qed.

Lemma sm_incs_run : forall Q r c off s,
  (forall p, 1 <= p <= c -> M.fetch Q (p + off) = Some (M.INC r)) ->
  M.err (M.core_of s) = false -> M.pc (M.core_of s) = S off ->
  (forall q, M.vals (M.core_of (run_prog c Q s)) q =
             if Nat.eqb q r then M.vals (M.core_of s) r + c else M.vals (M.core_of s) q) /\
  (forall q, q <> r -> M.vers (M.core_of (run_prog c Q s)) q = M.vers (M.core_of s) q) /\
  M.facts (M.core_of (run_prog c Q s)) = M.facts (M.core_of s) /\
  M.chan (M.core_of (run_prog c Q s)) = M.chan (M.core_of s) /\
  M.err (M.core_of (run_prog c Q s)) = false /\
  M.pc (M.core_of (run_prog c Q s)) = S (c + off) /\
  M.mu (run_prog c Q s) = M.mu s /\ M.cert (run_prog c Q s) = M.cert s.
Proof.
  intros Q r c. induction c as [| c IH]; intros off s Hf He Hp.
  - simpl. repeat split; auto. intro q. destruct (Nat.eqb_spec q r); subst; lia.
  - assert (Hn : M.next_instr Q (M.core_of s) = Some (M.INC r)).
    { apply sm_next_intro; [exact He | | discriminate]. rewrite Hp. apply (Hf 1). lia. }
    rewrite sm_run_succ.
    assert (Hst : step Q s = exec s (M.INC r)) by (unfold step; rewrite Hn; reflexivity).
    destruct (sm_plain_exec s (M.INC r) eq_refl) as (Hf1 & Hc1 & He1 & Hm1 & Hk1).
    assert (Hv1 : forall q, M.vals (M.core_of (exec s (M.INC r))) q =
                  if Nat.eqb q r then S (M.vals (M.core_of s) r) else M.vals (M.core_of s) q).
    { intro q. simpl. unfold M.cexec. rewrite He. rewrite M.multi_val_write.
      destruct (Nat.eqb_spec r q), (Nat.eqb_spec q r); subst; congruence. }
    assert (Hw1 : forall q, q <> r -> M.vers (M.core_of (exec s (M.INC r))) q = M.vers (M.core_of s) q).
    { intros q Hq. simpl. unfold M.cexec. rewrite He. rewrite M.multi_ver_write.
      destruct (Nat.eqb_spec r q); [congruence | reflexivity]. }
    assert (Hp1 : M.pc (M.core_of (exec s (M.INC r))) = S (S off)).
    { simpl. unfold M.cexec. rewrite He. simpl. rewrite Hp. reflexivity. }
    rewrite Hst.
    destruct (IH (S off) (exec s (M.INC r))) as (Hv & Hw & Hf2 & Hc2 & He2 & Hp2 & Hm2 & Hk2).
    + intros p Hp'. replace (p + S off) with (S p + off) by lia. apply Hf. lia.
    + rewrite He1. exact He.
    + exact Hp1.
    + repeat split.
      * intro q. rewrite Hv, !Hv1. rewrite Nat.eqb_refl.
        destruct (Nat.eqb q r); lia.
      * intros q Hq. rewrite Hw by exact Hq. apply Hw1, Hq.
      * rewrite Hf2. exact Hf1.
      * rewrite Hc2. exact Hc1.
      * exact He2.
      * rewrite Hp2. lia.
      * rewrite Hm2. exact Hm1.
      * rewrite Hk2. exact Hk1.
Qed.

(* DEC r L placed at line L: empties r, then falls through to L + 1. *)
Lemma sm_clear_run : forall Q r L v s,
  M.fetch Q L = Some (M.DEC r L) ->
  M.err (M.core_of s) = false -> M.pc (M.core_of s) = L ->
  M.vals (M.core_of s) r = v ->
  (forall q, M.vals (M.core_of (run_prog (S v) Q s)) q =
             if Nat.eqb q r then 0 else M.vals (M.core_of s) q) /\
  (forall q, q <> r -> M.vers (M.core_of (run_prog (S v) Q s)) q = M.vers (M.core_of s) q) /\
  M.facts (M.core_of (run_prog (S v) Q s)) = M.facts (M.core_of s) /\
  M.chan (M.core_of (run_prog (S v) Q s)) = M.chan (M.core_of s) /\
  M.err (M.core_of (run_prog (S v) Q s)) = false /\
  M.pc (M.core_of (run_prog (S v) Q s)) = S L /\
  M.mu (run_prog (S v) Q s) = M.mu s /\ M.cert (run_prog (S v) Q s) = M.cert s.
Proof.
  intros Q r L v. induction v as [| v IH]; intros s Hf He Hp Hv.
  - assert (Hn : M.next_instr Q (M.core_of s) = Some (M.DEC r L))
      by (apply sm_next_intro; [exact He | rewrite Hp; exact Hf | discriminate]).
    assert (Hst : run_prog 1 Q s = exec s (M.DEC r L)) by (simpl; unfold step; rewrite Hn; reflexivity).
    rewrite Hst.
    destruct (sm_plain_exec s (M.DEC r L) eq_refl) as (Hf1 & Hc1 & He1 & Hm1 & Hk1).
    assert (Hk : M.core_of (exec s (M.DEC r L)) = M.goto (M.core_of s) (S L)).
    { simpl. unfold M.cexec. rewrite He, Hv, Hp. reflexivity. }
    repeat split.
    + intro q. rewrite Hk. simpl. destruct (Nat.eqb_spec q r); subst; auto.
    + intros q _. rewrite Hk. reflexivity.
    + exact Hf1.
    + exact Hc1.
    + rewrite He1. exact He.
    + rewrite Hk. reflexivity.
    + exact Hm1.
    + exact Hk1.
  - assert (Hn : M.next_instr Q (M.core_of s) = Some (M.DEC r L))
      by (apply sm_next_intro; [exact He | rewrite Hp; exact Hf | discriminate]).
    rewrite sm_run_succ.
    assert (Hst : step Q s = exec s (M.DEC r L)) by (unfold step; rewrite Hn; reflexivity).
    rewrite Hst.
    destruct (sm_plain_exec s (M.DEC r L) eq_refl) as (Hf1 & Hc1 & He1 & Hm1 & Hk1).
    assert (Hk : M.core_of (exec s (M.DEC r L)) = M.write (M.core_of s) r v L).
    { simpl. unfold M.cexec. rewrite He, Hv. reflexivity. }
    destruct (IH (exec s (M.DEC r L))) as (Hv2 & Hw2 & Hf2 & Hc2 & He2 & Hp2 & Hm2 & Hk2).
    + exact Hf.
    + rewrite He1. exact He.
    + rewrite Hk. reflexivity.
    + rewrite Hk, M.multi_val_write, Nat.eqb_refl. reflexivity.
    + repeat split.
      * intro q. rewrite Hv2. rewrite Hk, M.multi_val_write.
        destruct (Nat.eqb_spec q r), (Nat.eqb_spec r q); subst; congruence.
      * intros q Hq. rewrite Hw2 by exact Hq. rewrite Hk, M.multi_ver_write.
        destruct (Nat.eqb_spec r q); [congruence | reflexivity].
      * rewrite Hf2. exact Hf1.
      * rewrite Hc2. exact Hc1.
      * exact He2.
      * exact Hp2.
      * rewrite Hm2. exact Hm1.
      * rewrite Hk2. exact Hk1.
Qed.

End Blocks.

(* ================================================================= *)
(* Assumption audit.                                                  *)
(* ================================================================= *)

Print Assumptions sm_block_run_mid.
Print Assumptions sm_block_run_final.
Print Assumptions sm_block_not_halted.
Print Assumptions sm_incs_run.
Print Assumptions sm_clear_run.
Print Assumptions sm_hequiv_hfun.
Print Assumptions sm_hfun_det.
