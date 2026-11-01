(** TcBlocks.v: blocks of the small machine, run inside a bigger program.

    This is the block machinery of the earlier clean-start proof (jump
    relocation, a block embedded in a program at an offset, and the
    simulation of a block's run by the bigger program's run, with the
    versions of the two counters moved by fixed amounts), together with the
    fact that a compiled counter program (INC and DEC only) changes nothing
    but the counters and the versions.

    Dependencies: Coq standard library, EarnedCore.v. No axioms and no unfinished proofs. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Minimal.EarnedCore.
Module E := Minimal.EarnedCore.
Unset Implicit Arguments.


Definition tc_rj (off len j : nat) : nat :=
  if (1 <=? j) && (j <=? len) then j + off else S (len + off).

Lemma tc_rj_in : forall off len j, 1 <= j <= len -> tc_rj off len j = j + off.
Proof.
  intros off len j H. unfold tc_rj.
  replace ((1 <=? j) && (j <=? len)) with true; [reflexivity |].
  symmetry. apply andb_true_iff. split; apply Nat.leb_le; lia.
Qed.

Lemma tc_rj_out : forall off len j, ~ (1 <= j <= len) -> tc_rj off len j = S (len + off).
Proof.
  intros off len j H. unfold tc_rj.
  destruct (1 <=? j) eqn:E1, (j <=? len) eqn:E2; simpl; try reflexivity.
  apply Nat.leb_le in E1. apply Nat.leb_le in E2. lia.
Qed.

Lemma tc_rj_S : forall off len p, 1 <= p <= len -> tc_rj off len (S p) = S (p + off).
Proof.
  intros off len p H. destruct (le_lt_dec (S p) len) as [H1 | H1].
  - rewrite tc_rj_in by lia. lia.
  - rewrite tc_rj_out by lia. lia.
Qed.

Lemma tc_grun_succ : forall n P s, E.run_prog (S n) P s = E.run_prog n P (E.step P s).
Proof. reflexivity. Qed.

Lemma tc_grun_add : forall a b P s, E.run_prog (a + b) P s = E.run_prog b P (E.run_prog a P s).
Proof. induction a as [| a IH]; intros; simpl; [reflexivity | apply IH]. Qed.

Lemma tc_ghalted_after : forall a b P s, a <= b ->
  E.halted P (E.core_of (E.run_prog a P s)) -> E.run_prog b P s = E.run_prog a P s.
Proof.
  intros a b P s Hle H. replace b with (a + (b - a)) by lia.
  rewrite tc_grun_add. apply E.run_prog_halted, H.
Qed.

(* ================================================================= *)
(* Blocks, with the versions moved.                                   *)
(* ================================================================= *)

Definition tc_gri (off len : nat) (i : E.instr) : E.instr :=
  match i with E.DEC c j => E.DEC c (tc_rj off len j) | _ => i end.

Definition tc_greloc (off : nat) (B : list E.instr) : list E.instr :=
  map (tc_gri off (length B)) B.

Lemma tc_greloc_length : forall off B, length (tc_greloc off B) = length B.
Proof. intros. apply map_length. Qed.

Definition tc_gembeds (Q B : list E.instr) (off : nat) : Prop :=
  forall p, 1 <= p <= length B ->
    E.fetch Q (p + off) = option_map (tc_gri off (length B)) (E.fetch B p).

Lemma tc_gembeds_app : forall A B C,
  tc_gembeds (A ++ tc_greloc (length A) B ++ C) B (length A).
Proof.
  intros A B C p Hp. destruct p as [| p]; [lia |].
  replace (S p + length A) with (S (length A + p)) by lia. simpl E.fetch.
  rewrite nth_error_app2 by lia. replace (length A + p - length A) with p by lia.
  rewrite nth_error_app1 by (rewrite tc_greloc_length; lia).
  unfold tc_greloc. rewrite nth_error_map. reflexivity.
Qed.

Lemma tc_gfetch_range : forall (B : list E.instr) p i, E.fetch B p = Some i -> 1 <= p <= length B.
Proof.
  intros B p i H. destruct p as [| p]; [discriminate |]. simpl in H.
  assert (p < length B) by (apply nth_error_Some; congruence). lia.
Qed.

Lemma tc_gfetch_out : forall (B : list E.instr) p, ~ (1 <= p <= length B) -> E.fetch B p = None.
Proof.
  intros B p H. destruct p as [| p]; [reflexivity |]. simpl. apply nth_error_None. lia.
Qed.

Definition tc_dc (da db : nat) (c : E.ctr) : nat := match c with E.CA => da | E.CB => db end.

Definition tc_fsh (da db : nat) (f : E.fact) : E.fact :=
  E.mkfact (E.f_prop f) (E.f_ctr f) (E.f_ver f + tc_dc da db (E.f_ctr f)).

Lemma tc_eqb_add : forall v w x, Nat.eqb (v + x) (w + x) = Nat.eqb v w.
Proof.
  intros v w x. destruct (Nat.eqb_spec v w) as [-> | H].
  - apply Nat.eqb_refl.
  - apply Nat.eqb_neq. lia.
Qed.

Lemma tc_fsh_eqb : forall da db f g, E.fact_eqb (tc_fsh da db f) (tc_fsh da db g) = E.fact_eqb f g.
Proof.
  intros da db [p c v] [q d w]. unfold E.fact_eqb, tc_fsh. simpl.
  destruct c, d; simpl; rewrite ?tc_eqb_add, ?andb_false_r; reflexivity.
Qed.

Lemma tc_existsb_fsh : forall da db f l,
  existsb (E.fact_eqb (tc_fsh da db f)) (map (tc_fsh da db) l) = existsb (E.fact_eqb f) l.
Proof.
  intros da db f l. induction l as [| g l IH]; [reflexivity |].
  simpl. rewrite tc_fsh_eqb, IH. reflexivity.
Qed.

Lemma tc_fsh_zero : forall l, map (tc_fsh 0 0) l = l.
Proof.
  induction l as [| [p c v] l IH]; [reflexivity |].
  simpl. rewrite IH. unfold tc_fsh. simpl. destruct c; simpl; rewrite Nat.add_0_r; reflexivity.
Qed.

Lemma tc_fsh_opt_zero : forall o, option_map (tc_fsh 0 0) o = o.
Proof.
  intros [[p c v] |]; [| reflexivity]. unfold tc_fsh. simpl.
  destruct c; simpl; rewrite Nat.add_0_r; reflexivity.
Qed.

(* B's core k and Q's core k': same counters and trap latch, versions of A
   and B moved by da and db, the facts and the channel moved to match, the
   program counter moved by the offset. *)
Definition tc_gcrel (off len da db : nat) (k k' : E.core) : Prop :=
  E.ca k = E.ca k' /\ E.cb k = E.cb k' /\
  E.va k' = E.va k + da /\ E.vb k' = E.vb k + db /\
  E.facts k' = map (tc_fsh da db) (E.facts k) /\
  E.chan k' = option_map (tc_fsh da db) (E.chan k) /\
  E.err k = E.err k' /\ E.pc k' = tc_rj off len (E.pc k).

Definition tc_gsrel (off len da db : nat) (s s' : E.state) : Prop :=
  tc_gcrel off len da db (E.core_of s) (E.core_of s') /\ E.mu s = E.mu s' /\ E.cert s = E.cert s'.

Lemma tc_gnext_some : forall P k i, E.next_instr P k = Some i ->
  E.err k = false /\ E.fetch P (E.pc k) = Some i /\ i <> E.HALT.
Proof.
  intros P k i H. unfold E.next_instr in H. destruct (E.err k); [discriminate |].
  destruct (E.fetch P (E.pc k)) as [[] |]; inversion H; subst;
    repeat split; try reflexivity; discriminate.
Qed.

Lemma tc_gnext_intro : forall P k i,
  E.err k = false -> E.fetch P (E.pc k) = Some i -> i <> E.HALT -> E.next_instr P k = Some i.
Proof.
  intros P k i He Hf Hi. unfold E.next_instr. rewrite He, Hf.
  destruct i; try reflexivity. congruence.
Qed.

Lemma tc_gri_halt : forall off len i, tc_gri off len i = E.HALT <-> i = E.HALT.
Proof. intros off len []; simpl; split; intro H; congruence. Qed.

Lemma tc_gcrel_val : forall off len da db k k' c, tc_gcrel off len da db k k' -> E.val k c = E.val k' c.
Proof. intros off len da db k k' [] (Ha & Hb & _); assumption. Qed.

Lemma tc_gcrel_claim : forall off len da db k k' p c, tc_gcrel off len da db k k' ->
  E.claim k' p c = tc_fsh da db (E.claim k p c).
Proof.
  intros off len da db k k' p c (_ & _ & Hva & Hvb & _). unfold E.claim, tc_fsh, E.ver. simpl.
  destruct c; simpl; [rewrite Hva | rewrite Hvb]; reflexivity.
Qed.

Lemma tc_gblock_cstep : forall Q B off da db k k' i,
  tc_gembeds Q B off -> tc_gcrel off (length B) da db k k' ->
  E.next_instr B k = Some i ->
  E.next_instr Q k' = Some (tc_gri off (length B) i) /\
  tc_gcrel off (length B) da db (E.cexec k i) (E.cexec k' (tc_gri off (length B) i)).
Proof.
  intros Q B off da db k k' i Hemb Hrel Hn.
  pose proof Hrel as (Ha & Hb & Hva & Hvb & Hf & Hc & He & Hp).
  destruct (tc_gnext_some B k i Hn) as (Ek & Hfe & Hh).
  assert (Hr : 1 <= E.pc k <= length B) by (eapply tc_gfetch_range; eauto).
  rewrite tc_rj_in in Hp by exact Hr.
  assert (Hq : E.fetch Q (E.pc k') = Some (tc_gri off (length B) i)).
  { rewrite Hp, (Hemb _ Hr), Hfe. reflexivity. }
  assert (Ek' : E.err k' = false) by congruence.
  split.
  { apply tc_gnext_intro; [exact Ek' | exact Hq |]. intro H. apply tc_gri_halt in H. auto. }
  unfold E.cexec. rewrite Ek, Ek'.
  destruct i as [c | c j | | p c | p c |]; cbv beta iota delta [tc_gri].
  - (* INC *)
    destruct c; unfold E.write, E.val; unfold tc_gcrel; cbn [E.ca E.cb E.va E.vb E.facts E.chan E.err E.pc];
      rewrite <- ?Ha, <- ?Hb;
      repeat split; auto; try lia; rewrite tc_rj_S by exact Hr; lia.
  - (* DEC *)
    destruct c; unfold E.val; cbn [E.ca E.cb].
    + destruct (E.ca k) as [| v] eqn:Ev.
      * assert (Ev' : E.ca k' = 0) by congruence. rewrite Ev'.
        unfold E.goto, tc_gcrel. cbn [E.ca E.cb E.va E.vb E.facts E.chan E.err E.pc].
        repeat split; try congruence; try lia. all: rewrite tc_rj_S by exact Hr; lia.
      * assert (Ev' : E.ca k' = S v) by congruence. rewrite Ev'.
        unfold E.write, tc_gcrel. cbn [E.ca E.cb E.va E.vb E.facts E.chan E.err E.pc].
        repeat split; try congruence; try lia.
    + destruct (E.cb k) as [| v] eqn:Ev.
      * assert (Ev' : E.cb k' = 0) by congruence. rewrite Ev'.
        unfold E.goto, tc_gcrel. cbn [E.ca E.cb E.va E.vb E.facts E.chan E.err E.pc].
        repeat split; try congruence; try lia. all: rewrite tc_rj_S by exact Hr; lia.
      * assert (Ev' : E.cb k' = S v) by congruence. rewrite Ev'.
        unfold E.write, tc_gcrel. cbn [E.ca E.cb E.va E.vb E.facts E.chan E.err E.pc].
        repeat split; try congruence; try lia.
  - congruence.
  - (* CHECK *)
    assert (Hok : E.check_ok k p c = E.check_ok k' p c).
    { unfold E.check_ok. rewrite Ek, Ek', (tc_gcrel_val _ _ _ _ k k' c Hrel), Hf, map_length. reflexivity. }
    rewrite <- Hok. destruct (E.check_ok k p c).
    + unfold E.record_fact, tc_gcrel. simpl. rewrite (tc_gcrel_claim _ _ _ _ k k' p c Hrel), Hf.
      repeat split; auto. rewrite tc_rj_S by exact Hr. lia.
    + unfold E.trap, tc_gcrel. simpl. repeat split; auto. rewrite tc_rj_in by exact Hr. lia.
  - (* COMMIT *)
    assert (Hok : E.commit_ok k p c = E.commit_ok k' p c).
    { unfold E.commit_ok. rewrite Ek, Ek', (tc_gcrel_claim _ _ _ _ k k' p c Hrel), Hf, tc_existsb_fsh.
      reflexivity. }
    rewrite <- Hok. destruct (E.commit_ok k p c).
    + unfold E.commit_to, tc_gcrel. simpl. rewrite (tc_gcrel_claim _ _ _ _ k k' p c Hrel).
      repeat split; auto. rewrite tc_rj_S by exact Hr. lia.
    + unfold E.trap, tc_gcrel. simpl. repeat split; auto. rewrite tc_rj_in by exact Hr. lia.
  - (* CERTIFY *)
    assert (Hok : E.certify_ok k = E.certify_ok k').
    { unfold E.certify_ok. rewrite Ek, Ek', Hc. destruct (E.chan k); reflexivity. }
    rewrite <- Hok. destruct (E.certify_ok k).
    + unfold E.goto, tc_gcrel. simpl. repeat split; auto. rewrite tc_rj_S by exact Hr. lia.
    + unfold E.trap, tc_gcrel. simpl. repeat split; auto. rewrite tc_rj_in by exact Hr. lia.
Qed.

Lemma tc_gblock_step : forall Q B off da db s s' i,
  tc_gembeds Q B off -> tc_gsrel off (length B) da db s s' ->
  E.next_instr B (E.core_of s) = Some i ->
  E.next_instr Q (E.core_of s') = Some (tc_gri off (length B) i) /\
  tc_gsrel off (length B) da db (E.step B s) (E.step Q s').
Proof.
  intros Q B off da db s s' i Hemb [Hc [Hm Hk]] Hn.
  destruct (tc_gblock_cstep Q B off da db _ _ i Hemb Hc Hn) as [Hn' Hc'].
  split; [exact Hn' |].
  unfold E.step. rewrite Hn, Hn'. unfold tc_gsrel, E.exec. simpl.
  split; [exact Hc' |].
  assert (Hcost : E.cost (tc_gri off (length B) i) = E.cost i) by (destruct i; reflexivity).
  rewrite Hcost, Hm. split; [reflexivity |].
  assert (Hfire : E.fires (E.core_of s) i = E.fires (E.core_of s') (tc_gri off (length B) i)).
  { destruct Hc as (_ & _ & _ & _ & _ & Hch & He & _).
    destruct i; try reflexivity. simpl. unfold E.certify_ok. rewrite He, Hch.
    destruct (E.chan (E.core_of s)); reflexivity. }
  rewrite Hk, Hfire. reflexivity.
Qed.

Lemma tc_gblock_run_mid : forall Q B off da db, tc_gembeds Q B off ->
  forall n s s', tc_gsrel off (length B) da db s s' ->
  (forall m, m < n -> E.next_instr B (E.core_of (E.run_prog m B s)) <> None) ->
  tc_gsrel off (length B) da db (E.run_prog n B s) (E.run_prog n Q s').
Proof.
  intros Q B off da db Hemb n. induction n as [| n IH]; intros s s' Hs Hgo; [exact Hs |].
  destruct (E.next_instr B (E.core_of s)) as [i |] eqn:Hn;
    [| exfalso; apply (Hgo 0); [lia | exact Hn]].
  destruct (tc_gblock_step Q B off da db s s' i Hemb Hs Hn) as [_ Hs'].
  rewrite !tc_grun_succ. apply IH; [exact Hs' |].
  intros m Hm. rewrite <- tc_grun_succ. apply Hgo. lia.
Qed.

Lemma tc_gblock_not_halted : forall Q B off da db s s',
  tc_gembeds Q B off -> tc_gsrel off (length B) da db s s' ->
  E.next_instr B (E.core_of s) <> None -> E.next_instr Q (E.core_of s') <> None.
Proof.
  intros Q B off da db s s' Hemb Hs Hn.
  destruct (E.next_instr B (E.core_of s)) as [i |] eqn:Hb; [| congruence].
  destruct (tc_gblock_step Q B off da db s s' i Hemb Hs Hb) as [H _]. congruence.
Qed.

Lemma tc_gblock_halted : forall Q B off da db k k',
  tc_gembeds Q B off -> length Q = off + length B -> tc_gcrel off (length B) da db k k' ->
  E.halted B k -> E.halted Q k'.
Proof.
  intros Q B off da db k k' Hemb HQ (_ & _ & _ & _ & _ & _ & He & Hp) Hh.
  unfold E.halted, E.next_instr in *. rewrite <- He.
  destruct (E.err k); [reflexivity |].
  destruct (le_lt_dec 1 (E.pc k)) as [H1 | H1];
    [destruct (le_lt_dec (E.pc k) (length B)) as [H2 | H2] |].
  - rewrite Hp, tc_rj_in by lia. rewrite (Hemb _ (conj H1 H2)).
    destruct (E.fetch B (E.pc k)) as [[] |]; simpl in *; try discriminate; reflexivity.
  - rewrite Hp, tc_rj_out by lia. rewrite tc_gfetch_out by lia. reflexivity.
  - rewrite Hp, tc_rj_out by lia. rewrite tc_gfetch_out by lia. reflexivity.
Qed.

Lemma tc_gblock_run_final : forall Q B off da db,
  tc_gembeds Q B off -> length Q = off + length B ->
  forall n s s', tc_gsrel off (length B) da db s s' ->
  tc_gsrel off (length B) da db (E.run_prog n B s) (E.run_prog n Q s').
Proof.
  intros Q B off da db Hemb HQ n. induction n as [| n IH]; intros s s' Hs; [exact Hs |].
  rewrite !tc_grun_succ.
  destruct (E.next_instr B (E.core_of s)) as [i |] eqn:Hn.
  - destruct (tc_gblock_step Q B off da db s s' i Hemb Hs Hn) as [_ Hs']. apply IH, Hs'.
  - assert (HQh : E.halted Q (E.core_of s'))
      by (apply (tc_gblock_halted Q B off da db (E.core_of s)); [exact Hemb | exact HQ | apply Hs | exact Hn]).
    unfold E.step. rewrite Hn. unfold E.halted in HQh. rewrite HQh. apply IH, Hs.
Qed.


Lemma tc_gplain_exec : forall s i, (exists c, i = E.INC c) \/ (exists c j, i = E.DEC c j) ->
  E.facts (E.core_of (E.exec s i)) = E.facts (E.core_of s) /\
  E.chan (E.core_of (E.exec s i)) = E.chan (E.core_of s) /\
  E.err (E.core_of (E.exec s i)) = E.err (E.core_of s) /\
  E.mu (E.exec s i) = E.mu s /\ E.cert (E.exec s i) = E.cert s.
Proof.
  intros s i Hi. destruct Hi as [[c ->] | [c [j ->]]]; unfold E.exec;
    cbn [E.core_of E.mu E.cert E.fires E.cost]; rewrite Bool.orb_false_r, Nat.add_0_r; unfold E.cexec;
    destruct (E.err (E.core_of s)) eqn:He; try (repeat split; congruence).
  - destruct c; repeat split; simpl; congruence.
  - destruct c; unfold E.val; [destruct (E.ca (E.core_of s)) | destruct (E.cb (E.core_of s))];
      repeat split; simpl; congruence.
Qed.


Lemma tc_compile_run : forall (Mp : list E.minsky) n s,
  E.err (E.core_of s) = false ->
  E.window (E.core_of (E.run_prog n (E.compile Mp) s)) = E.mrun n Mp (E.window (E.core_of s)) /\
  E.facts (E.core_of (E.run_prog n (E.compile Mp) s)) = E.facts (E.core_of s) /\
  E.chan (E.core_of (E.run_prog n (E.compile Mp) s)) = E.chan (E.core_of s) /\
  E.err (E.core_of (E.run_prog n (E.compile Mp) s)) = false /\
  E.mu (E.run_prog n (E.compile Mp) s) = E.mu s /\
  E.cert (E.run_prog n (E.compile Mp) s) = E.cert s.
Proof.
  intros Mp n. induction n as [| n IH]; intros s He; [simpl; repeat split; auto |].
  rewrite tc_grun_succ.
  destruct (E.next_instr (E.compile Mp) (E.core_of s)) as [i |] eqn:Hn.
  - assert (Hst : E.step (E.compile Mp) s = E.exec s i) by (unfold E.step; rewrite Hn; reflexivity).
    destruct (tc_gnext_some _ _ _ Hn) as (_ & Hf & _).
    assert (Hi : (exists c, i = E.INC c) \/ (exists c j, i = E.DEC c j)).
    { unfold E.compile in Hf. rewrite E.fetch_map in Hf.
      destruct (E.fetch Mp (E.pc (E.core_of s))) as [[c | c j] |]; simpl in Hf; inversion Hf;
        [left; exists c | right; exists c, j]; reflexivity. }
    destruct (tc_gplain_exec s i Hi) as (Hf1 & Hc1 & He1 & Hm1 & Hk1).
    destruct (E.simulation_step Mp (E.core_of s) He) as [Hnone Hsome].
    destruct (E.mstep Mp (E.window (E.core_of s))) as [y |] eqn:Hm.
    + destruct (Hsome y eq_refl) as [Hw He'].
      assert (Hcs : E.core_step (E.compile Mp) (E.core_of s) = E.core_of (E.step (E.compile Mp) s))
        by (symmetry; apply E.step_core).
      rewrite Hcs in Hw, He'.
      destruct (IH _ He') as (Hw2 & Hf2 & Hc2 & He2 & Hm2 & Hk2).
      simpl E.mrun. rewrite Hm. rewrite <- Hw.
      rewrite Hst in *. repeat split; congruence.
    + exfalso. assert (Hh : E.halted (E.compile Mp) (E.core_of s)) by (apply Hnone; reflexivity).
      unfold E.halted in Hh. congruence.
  - assert (Hst : E.step (E.compile Mp) s = s) by (unfold E.step; rewrite Hn; reflexivity).
    rewrite Hst. rewrite E.run_prog_halted by exact Hn.
    destruct (E.simulation_step Mp (E.core_of s) He) as [Hnone _].
    assert (Hm : E.mstep Mp (E.window (E.core_of s)) = None) by (apply Hnone; exact Hn).
    simpl E.mrun. rewrite Hm. repeat split; auto.
Qed.

Lemma tc_gfetch_app_left : forall (A B : list E.instr) n,
  n <= length A -> E.fetch (A ++ B) n = E.fetch A n.
Proof.
  intros A B n H. destruct n as [| n]; [reflexivity |]. simpl. apply nth_error_app1. lia.
Qed.

Lemma tc_gfetch_app_right : forall (A C : list E.instr) p,
  E.fetch (A ++ C) (length A + S p) = E.fetch C (S p).
Proof.
  intros A C p. replace (length A + S p) with (S (length A + p)) by lia. simpl.
  rewrite nth_error_app2 by lia. f_equal. lia.
Qed.

