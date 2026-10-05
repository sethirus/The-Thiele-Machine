(** SmGuestRice.v: Rice's theorem for programs of the small machine, run
    from the clean start.

    The small machine is the machine of EarnedCore.v: two counters A and B,
    INC, DEC, HALT, CHECK, COMMIT, CERTIFY, the ledger, the flag, the fact
    table, the channel and the trap latch. Here a program is run from the
    clean start, E.start 0 0: both counters 0, no facts, no commitment,
    flag down, ledger 0. What it does there (sm_gequiv): it runs forever, or
    it stops, and then the two counters, the trap latch, the ledger and the
    flag are what can be read. Two programs behave the same when they do
    the same thing there.

    Theorem [sm_guest_rice]. Let Pi be a property of small-machine programs
    that respects behaving the same from the clean start, with Pi y for
    some program y and not Pi n for some program n. Then Pi is undecidable
    in the sense of the vendored Saarland library.

    Why only the clean start. The standard reduction runs a copy of a
    two-counter program first and then the program y on the original input.
    With inputs placed directly in the two counters there is nowhere to
    keep the input while the copy runs: by Schroeppel (1972) a two-counter
    machine started with n and 0 cannot even compute 2^n. From the clean
    start there is no input to keep. The host machine, with a register for
    every number, has no such limit, and SmHostRice.v proves Rice's theorem
    there for programs run on an input.

    The proof reduces the complement of two-counter halting (MM2) to the
    complement of Pi. A two-counter program H with start (a, b) goes to the
    small-machine program that counts up to a and b, runs a copy of H, empties
    both counters, and runs y. Every instruction before the copy of y is an
    INC or a DEC: it pays nothing and changes no fact, channel, trap latch
    or flag. It does raise the versions of the counters, so the facts y's
    run records carry versions moved by fixed amounts; the relation
    [sm_gcrel] tracks that shift.

    Dependencies: Coq standard library, the vendored coq-undecidability
    library (MM2, Synthetic), EarnedCore.v, EarnedMulti.v, SmHostBlocks.v
    (the jump relocation sm_rj only), SmMM2Compl.v and SmHostRice.v (the
    MM2 bridge lemmas only). No axioms, no Admitted.                        *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Undecidability.Synthetic Require Import Undecidability.
From Undecidability.MinskyMachines Require Import MM2.
Require Minimal.EarnedCore.
Require Import Sm.SmHostBlocks Sm.SmMM2Compl Sm.SmHostRice.
Module E := Minimal.EarnedCore.
Unset Implicit Arguments.

(* ================================================================= *)
(* Behaviour from the clean start.                                    *)
(* ================================================================= *)

Definition sm_gends (P : list E.instr) (s : E.state) : Prop :=
  exists n, s = E.run_prog n P (E.start 0 0) /\ E.halted P (E.core_of s).

Definition sm_gagree (s t : E.state) : Prop :=
  E.ca (E.core_of s) = E.ca (E.core_of t) /\ E.cb (E.core_of s) = E.cb (E.core_of t) /\
  E.err (E.core_of s) = E.err (E.core_of t) /\ E.mu s = E.mu t /\ E.cert s = E.cert t.

Definition sm_gequiv (P Q : list E.instr) : Prop :=
  (forall s, sm_gends P s -> exists t, sm_gends Q t /\ sm_gagree s t) /\
  (forall t, sm_gends Q t -> exists s, sm_gends P s /\ sm_gagree s t).

Lemma sm_gagree_sym : forall s t, sm_gagree s t -> sm_gagree t s.
Proof. intros s t (H1 & H2 & H3 & H4 & H5). repeat split; congruence. Qed.

Lemma sm_gequiv_sym : forall P Q, sm_gequiv P Q -> sm_gequiv Q P.
Proof.
  intros P Q [H1 H2]. split.
  - intros t Ht. destruct (H2 t Ht) as [s [Hs Ha]]. exists s. split; [exact Hs | apply sm_gagree_sym, Ha].
  - intros s Hs. destruct (H1 s Hs) as [t [Ht Ha]]. exists t. split; [exact Ht | apply sm_gagree_sym, Ha].
Qed.

Lemma sm_grun_succ : forall n P s, E.run_prog (S n) P s = E.run_prog n P (E.step P s).
Proof. reflexivity. Qed.

Lemma sm_grun_add : forall a b P s, E.run_prog (a + b) P s = E.run_prog b P (E.run_prog a P s).
Proof. induction a as [| a IH]; intros; simpl; [reflexivity | apply IH]. Qed.

Lemma sm_ghalted_after : forall a b P s, a <= b ->
  E.halted P (E.core_of (E.run_prog a P s)) -> E.run_prog b P s = E.run_prog a P s.
Proof.
  intros a b P s Hle H. replace b with (a + (b - a)) by lia.
  rewrite sm_grun_add. apply E.run_prog_halted, H.
Qed.

(* ================================================================= *)
(* Blocks, with the versions moved.                                   *)
(* ================================================================= *)

Definition sm_gri (off len : nat) (i : E.instr) : E.instr :=
  match i with E.DEC c j => E.DEC c (sm_rj off len j) | _ => i end.

Definition sm_greloc (off : nat) (B : list E.instr) : list E.instr :=
  map (sm_gri off (length B)) B.

Lemma sm_greloc_length : forall off B, length (sm_greloc off B) = length B.
Proof. intros. apply map_length. Qed.

Definition sm_gembeds (Q B : list E.instr) (off : nat) : Prop :=
  forall p, 1 <= p <= length B ->
    E.fetch Q (p + off) = option_map (sm_gri off (length B)) (E.fetch B p).

Lemma sm_gembeds_app : forall A B C,
  sm_gembeds (A ++ sm_greloc (length A) B ++ C) B (length A).
Proof.
  intros A B C p Hp. destruct p as [| p]; [lia |].
  replace (S p + length A) with (S (length A + p)) by lia. simpl E.fetch.
  rewrite nth_error_app2 by lia. replace (length A + p - length A) with p by lia.
  rewrite nth_error_app1 by (rewrite sm_greloc_length; lia).
  unfold sm_greloc. rewrite nth_error_map. reflexivity.
Qed.

Lemma sm_gfetch_range : forall (B : list E.instr) p i, E.fetch B p = Some i -> 1 <= p <= length B.
Proof.
  intros B p i H. destruct p as [| p]; [discriminate |]. simpl in H.
  assert (p < length B) by (apply nth_error_Some; congruence). lia.
Qed.

Lemma sm_gfetch_out : forall (B : list E.instr) p, ~ (1 <= p <= length B) -> E.fetch B p = None.
Proof.
  intros B p H. destruct p as [| p]; [reflexivity |]. simpl. apply nth_error_None. lia.
Qed.

Definition sm_dc (da db : nat) (c : E.ctr) : nat := match c with E.CA => da | E.CB => db end.

Definition sm_fsh (da db : nat) (f : E.fact) : E.fact :=
  E.mkfact (E.f_prop f) (E.f_ctr f) (E.f_ver f + sm_dc da db (E.f_ctr f)).

Lemma sm_eqb_add : forall v w x, Nat.eqb (v + x) (w + x) = Nat.eqb v w.
Proof.
  intros v w x. destruct (Nat.eqb_spec v w) as [-> | H].
  - apply Nat.eqb_refl.
  - apply Nat.eqb_neq. lia.
Qed.

Lemma sm_fsh_eqb : forall da db f g, E.fact_eqb (sm_fsh da db f) (sm_fsh da db g) = E.fact_eqb f g.
Proof.
  intros da db [p c v] [q d w]. unfold E.fact_eqb, sm_fsh. simpl.
  destruct c, d; simpl; rewrite ?sm_eqb_add, ?andb_false_r; reflexivity.
Qed.

Lemma sm_existsb_fsh : forall da db f l,
  existsb (E.fact_eqb (sm_fsh da db f)) (map (sm_fsh da db) l) = existsb (E.fact_eqb f) l.
Proof.
  intros da db f l. induction l as [| g l IH]; [reflexivity |].
  simpl. rewrite sm_fsh_eqb, IH. reflexivity.
Qed.

Lemma sm_fsh_zero : forall l, map (sm_fsh 0 0) l = l.
Proof.
  induction l as [| [p c v] l IH]; [reflexivity |].
  simpl. rewrite IH. unfold sm_fsh. simpl. destruct c; simpl; rewrite Nat.add_0_r; reflexivity.
Qed.

Lemma sm_fsh_opt_zero : forall o, option_map (sm_fsh 0 0) o = o.
Proof.
  intros [[p c v] |]; [| reflexivity]. unfold sm_fsh. simpl.
  destruct c; simpl; rewrite Nat.add_0_r; reflexivity.
Qed.

(* B's core k and Q's core k': same counters and trap latch, versions of A
   and B moved by da and db, the facts and the channel moved to match, the
   program counter moved by the offset. *)
Definition sm_gcrel (off len da db : nat) (k k' : E.core) : Prop :=
  E.ca k = E.ca k' /\ E.cb k = E.cb k' /\
  E.va k' = E.va k + da /\ E.vb k' = E.vb k + db /\
  E.facts k' = map (sm_fsh da db) (E.facts k) /\
  E.chan k' = option_map (sm_fsh da db) (E.chan k) /\
  E.err k = E.err k' /\ E.pc k' = sm_rj off len (E.pc k).

Definition sm_gsrel (off len da db : nat) (s s' : E.state) : Prop :=
  sm_gcrel off len da db (E.core_of s) (E.core_of s') /\ E.mu s = E.mu s' /\ E.cert s = E.cert s'.

Lemma sm_gnext_some : forall P k i, E.next_instr P k = Some i ->
  E.err k = false /\ E.fetch P (E.pc k) = Some i /\ i <> E.HALT.
Proof.
  intros P k i H. unfold E.next_instr in H. destruct (E.err k); [discriminate |].
  destruct (E.fetch P (E.pc k)) as [[] |]; inversion H; subst;
    repeat split; try reflexivity; discriminate.
Qed.

Lemma sm_gnext_intro : forall P k i,
  E.err k = false -> E.fetch P (E.pc k) = Some i -> i <> E.HALT -> E.next_instr P k = Some i.
Proof.
  intros P k i He Hf Hi. unfold E.next_instr. rewrite He, Hf.
  destruct i; try reflexivity. congruence.
Qed.

Lemma sm_gri_halt : forall off len i, sm_gri off len i = E.HALT <-> i = E.HALT.
Proof. intros off len []; simpl; split; intro H; congruence. Qed.

Lemma sm_gcrel_val : forall off len da db k k' c, sm_gcrel off len da db k k' -> E.val k c = E.val k' c.
Proof. intros off len da db k k' [] (Ha & Hb & _); assumption. Qed.

Lemma sm_gcrel_claim : forall off len da db k k' p c, sm_gcrel off len da db k k' ->
  E.claim k' p c = sm_fsh da db (E.claim k p c).
Proof.
  intros off len da db k k' p c (_ & _ & Hva & Hvb & _). unfold E.claim, sm_fsh, E.ver. simpl.
  destruct c; simpl; [rewrite Hva | rewrite Hvb]; reflexivity.
Qed.

Lemma sm_gblock_cstep : forall Q B off da db k k' i,
  sm_gembeds Q B off -> sm_gcrel off (length B) da db k k' ->
  E.next_instr B k = Some i ->
  E.next_instr Q k' = Some (sm_gri off (length B) i) /\
  sm_gcrel off (length B) da db (E.cexec k i) (E.cexec k' (sm_gri off (length B) i)).
Proof.
  intros Q B off da db k k' i Hemb Hrel Hn.
  pose proof Hrel as (Ha & Hb & Hva & Hvb & Hf & Hc & He & Hp).
  destruct (sm_gnext_some B k i Hn) as (Ek & Hfe & Hh).
  assert (Hr : 1 <= E.pc k <= length B) by (eapply sm_gfetch_range; eauto).
  rewrite sm_rj_in in Hp by exact Hr.
  assert (Hq : E.fetch Q (E.pc k') = Some (sm_gri off (length B) i)).
  { rewrite Hp, (Hemb _ Hr), Hfe. reflexivity. }
  assert (Ek' : E.err k' = false) by congruence.
  split.
  { apply sm_gnext_intro; [exact Ek' | exact Hq |]. intro H. apply sm_gri_halt in H. auto. }
  unfold E.cexec. rewrite Ek, Ek'.
  destruct i as [c | c j | | p c | p c |]; cbv beta iota delta [sm_gri].
  - (* INC *)
    destruct c; unfold E.write, E.val; unfold sm_gcrel; cbn [E.ca E.cb E.va E.vb E.facts E.chan E.err E.pc];
      rewrite <- ?Ha, <- ?Hb;
      repeat split; auto; try lia; rewrite sm_rj_S by exact Hr; lia.
  - (* DEC *)
    destruct c; unfold E.val; cbn [E.ca E.cb].
    + destruct (E.ca k) as [| v] eqn:Ev.
      * assert (Ev' : E.ca k' = 0) by congruence. rewrite Ev'.
        unfold E.goto, sm_gcrel. cbn [E.ca E.cb E.va E.vb E.facts E.chan E.err E.pc].
        repeat split; try congruence; try lia. all: rewrite sm_rj_S by exact Hr; lia.
      * assert (Ev' : E.ca k' = S v) by congruence. rewrite Ev'.
        unfold E.write, sm_gcrel. cbn [E.ca E.cb E.va E.vb E.facts E.chan E.err E.pc].
        repeat split; try congruence; try lia.
    + destruct (E.cb k) as [| v] eqn:Ev.
      * assert (Ev' : E.cb k' = 0) by congruence. rewrite Ev'.
        unfold E.goto, sm_gcrel. cbn [E.ca E.cb E.va E.vb E.facts E.chan E.err E.pc].
        repeat split; try congruence; try lia. all: rewrite sm_rj_S by exact Hr; lia.
      * assert (Ev' : E.cb k' = S v) by congruence. rewrite Ev'.
        unfold E.write, sm_gcrel. cbn [E.ca E.cb E.va E.vb E.facts E.chan E.err E.pc].
        repeat split; try congruence; try lia.
  - congruence.
  - (* CHECK *)
    assert (Hok : E.check_ok k p c = E.check_ok k' p c).
    { unfold E.check_ok. rewrite Ek, Ek', (sm_gcrel_val _ _ _ _ k k' c Hrel), Hf, map_length. reflexivity. }
    rewrite <- Hok. destruct (E.check_ok k p c).
    + unfold E.record_fact, sm_gcrel. simpl. rewrite (sm_gcrel_claim _ _ _ _ k k' p c Hrel), Hf.
      repeat split; auto. rewrite sm_rj_S by exact Hr. lia.
    + unfold E.trap, sm_gcrel. simpl. repeat split; auto. rewrite sm_rj_in by exact Hr. lia.
  - (* COMMIT *)
    assert (Hok : E.commit_ok k p c = E.commit_ok k' p c).
    { unfold E.commit_ok. rewrite Ek, Ek', (sm_gcrel_claim _ _ _ _ k k' p c Hrel), Hf, sm_existsb_fsh.
      reflexivity. }
    rewrite <- Hok. destruct (E.commit_ok k p c).
    + unfold E.commit_to, sm_gcrel. simpl. rewrite (sm_gcrel_claim _ _ _ _ k k' p c Hrel).
      repeat split; auto. rewrite sm_rj_S by exact Hr. lia.
    + unfold E.trap, sm_gcrel. simpl. repeat split; auto. rewrite sm_rj_in by exact Hr. lia.
  - (* CERTIFY *)
    assert (Hok : E.certify_ok k = E.certify_ok k').
    { unfold E.certify_ok. rewrite Ek, Ek', Hc. destruct (E.chan k); reflexivity. }
    rewrite <- Hok. destruct (E.certify_ok k).
    + unfold E.goto, sm_gcrel. simpl. repeat split; auto. rewrite sm_rj_S by exact Hr. lia.
    + unfold E.trap, sm_gcrel. simpl. repeat split; auto. rewrite sm_rj_in by exact Hr. lia.
Qed.

Lemma sm_gblock_step : forall Q B off da db s s' i,
  sm_gembeds Q B off -> sm_gsrel off (length B) da db s s' ->
  E.next_instr B (E.core_of s) = Some i ->
  E.next_instr Q (E.core_of s') = Some (sm_gri off (length B) i) /\
  sm_gsrel off (length B) da db (E.step B s) (E.step Q s').
Proof.
  intros Q B off da db s s' i Hemb [Hc [Hm Hk]] Hn.
  destruct (sm_gblock_cstep Q B off da db _ _ i Hemb Hc Hn) as [Hn' Hc'].
  split; [exact Hn' |].
  unfold E.step. rewrite Hn, Hn'. unfold sm_gsrel, E.exec. simpl.
  split; [exact Hc' |].
  assert (Hcost : E.cost (sm_gri off (length B) i) = E.cost i) by (destruct i; reflexivity).
  rewrite Hcost, Hm. split; [reflexivity |].
  assert (Hfire : E.fires (E.core_of s) i = E.fires (E.core_of s') (sm_gri off (length B) i)).
  { destruct Hc as (_ & _ & _ & _ & _ & Hch & He & _).
    destruct i; try reflexivity. simpl. unfold E.certify_ok. rewrite He, Hch.
    destruct (E.chan (E.core_of s)); reflexivity. }
  rewrite Hk, Hfire. reflexivity.
Qed.

Lemma sm_gblock_run_mid : forall Q B off da db, sm_gembeds Q B off ->
  forall n s s', sm_gsrel off (length B) da db s s' ->
  (forall m, m < n -> E.next_instr B (E.core_of (E.run_prog m B s)) <> None) ->
  sm_gsrel off (length B) da db (E.run_prog n B s) (E.run_prog n Q s').
Proof.
  intros Q B off da db Hemb n. induction n as [| n IH]; intros s s' Hs Hgo; [exact Hs |].
  destruct (E.next_instr B (E.core_of s)) as [i |] eqn:Hn;
    [| exfalso; apply (Hgo 0); [lia | exact Hn]].
  destruct (sm_gblock_step Q B off da db s s' i Hemb Hs Hn) as [_ Hs'].
  rewrite !sm_grun_succ. apply IH; [exact Hs' |].
  intros m Hm. rewrite <- sm_grun_succ. apply Hgo. lia.
Qed.

Lemma sm_gblock_not_halted : forall Q B off da db s s',
  sm_gembeds Q B off -> sm_gsrel off (length B) da db s s' ->
  E.next_instr B (E.core_of s) <> None -> E.next_instr Q (E.core_of s') <> None.
Proof.
  intros Q B off da db s s' Hemb Hs Hn.
  destruct (E.next_instr B (E.core_of s)) as [i |] eqn:Hb; [| congruence].
  destruct (sm_gblock_step Q B off da db s s' i Hemb Hs Hb) as [H _]. congruence.
Qed.

Lemma sm_gblock_halted : forall Q B off da db k k',
  sm_gembeds Q B off -> length Q = off + length B -> sm_gcrel off (length B) da db k k' ->
  E.halted B k -> E.halted Q k'.
Proof.
  intros Q B off da db k k' Hemb HQ (_ & _ & _ & _ & _ & _ & He & Hp) Hh.
  unfold E.halted, E.next_instr in *. rewrite <- He.
  destruct (E.err k); [reflexivity |].
  destruct (le_lt_dec 1 (E.pc k)) as [H1 | H1];
    [destruct (le_lt_dec (E.pc k) (length B)) as [H2 | H2] |].
  - rewrite Hp, sm_rj_in by lia. rewrite (Hemb _ (conj H1 H2)).
    destruct (E.fetch B (E.pc k)) as [[] |]; simpl in *; try discriminate; reflexivity.
  - rewrite Hp, sm_rj_out by lia. rewrite sm_gfetch_out by lia. reflexivity.
  - rewrite Hp, sm_rj_out by lia. rewrite sm_gfetch_out by lia. reflexivity.
Qed.

Lemma sm_gblock_run_final : forall Q B off da db,
  sm_gembeds Q B off -> length Q = off + length B ->
  forall n s s', sm_gsrel off (length B) da db s s' ->
  sm_gsrel off (length B) da db (E.run_prog n B s) (E.run_prog n Q s').
Proof.
  intros Q B off da db Hemb HQ n. induction n as [| n IH]; intros s s' Hs; [exact Hs |].
  rewrite !sm_grun_succ.
  destruct (E.next_instr B (E.core_of s)) as [i |] eqn:Hn.
  - destruct (sm_gblock_step Q B off da db s s' i Hemb Hs Hn) as [_ Hs']. apply IH, Hs'.
  - assert (HQh : E.halted Q (E.core_of s'))
      by (apply (sm_gblock_halted Q B off da db (E.core_of s)); [exact Hemb | exact HQ | apply Hs | exact Hn]).
    unfold E.step. rewrite Hn. unfold E.halted in HQh. rewrite HQh. apply IH, Hs.
Qed.

(* ================================================================= *)
(* Counting up, and emptying.                                         *)
(* ================================================================= *)

Definition sm_gincs (c : E.ctr) (n : nat) : list E.instr := repeat (E.INC c) n.

Lemma sm_gincs_length : forall c n, length (sm_gincs c n) = n.
Proof. intros. apply repeat_length. Qed.

Lemma sm_gplain_exec : forall s i, (exists c, i = E.INC c) \/ (exists c j, i = E.DEC c j) ->
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

Lemma sm_gincs_run : forall Q c n off s,
  (forall p, 1 <= p <= n -> E.fetch Q (p + off) = Some (E.INC c)) ->
  E.err (E.core_of s) = false -> E.pc (E.core_of s) = S off ->
  E.val (E.core_of (E.run_prog n Q s)) c = E.val (E.core_of s) c + n /\
  (forall d, d <> c -> E.val (E.core_of (E.run_prog n Q s)) d = E.val (E.core_of s) d) /\
  E.facts (E.core_of (E.run_prog n Q s)) = E.facts (E.core_of s) /\
  E.chan (E.core_of (E.run_prog n Q s)) = E.chan (E.core_of s) /\
  E.err (E.core_of (E.run_prog n Q s)) = false /\
  E.pc (E.core_of (E.run_prog n Q s)) = S (n + off) /\
  E.mu (E.run_prog n Q s) = E.mu s /\ E.cert (E.run_prog n Q s) = E.cert s.
Proof.
  intros Q c n. induction n as [| n IH]; intros off s Hf He Hp.
  - simpl. repeat split; auto; lia.
  - assert (Hn : E.next_instr Q (E.core_of s) = Some (E.INC c)).
    { apply sm_gnext_intro; [exact He | | discriminate]. rewrite Hp. apply (Hf 1). lia. }
    rewrite sm_grun_succ.
    assert (Hst : E.step Q s = E.exec s (E.INC c)) by (unfold E.step; rewrite Hn; reflexivity).
    rewrite Hst.
    destruct (sm_gplain_exec s (E.INC c) (or_introl (ex_intro _ c eq_refl))) as (Hf1 & Hc1 & He1 & Hm1 & Hk1).
    assert (Hk : E.core_of (E.exec s (E.INC c)) = E.write (E.core_of s) c (S (E.val (E.core_of s) c)) (S (S off))).
    { simpl. unfold E.cexec. rewrite He, Hp. reflexivity. }
    destruct (IH (S off) (E.exec s (E.INC c))) as (Hv & Hv' & Hf2 & Hc2 & He2 & Hp2 & Hm2 & Hk2).
    + intros p Hp'. replace (p + S off) with (S p + off) by lia. apply Hf. lia.
    + rewrite He1. exact He.
    + rewrite Hk. destruct c; reflexivity.
    + repeat split.
      * rewrite Hv, Hk. destruct c; simpl; lia.
      * intros d Hd. rewrite Hv' by exact Hd. rewrite Hk. destruct c, d; simpl; congruence.
      * rewrite Hf2. exact Hf1.
      * rewrite Hc2. exact Hc1.
      * exact He2.
      * rewrite Hp2. lia.
      * rewrite Hm2. exact Hm1.
      * rewrite Hk2. exact Hk1.
Qed.

Lemma sm_gclear_run : forall Q c L v s,
  E.fetch Q L = Some (E.DEC c L) ->
  E.err (E.core_of s) = false -> E.pc (E.core_of s) = L ->
  E.val (E.core_of s) c = v ->
  E.val (E.core_of (E.run_prog (S v) Q s)) c = 0 /\
  (forall d, d <> c -> E.val (E.core_of (E.run_prog (S v) Q s)) d = E.val (E.core_of s) d) /\
  E.facts (E.core_of (E.run_prog (S v) Q s)) = E.facts (E.core_of s) /\
  E.chan (E.core_of (E.run_prog (S v) Q s)) = E.chan (E.core_of s) /\
  E.err (E.core_of (E.run_prog (S v) Q s)) = false /\
  E.pc (E.core_of (E.run_prog (S v) Q s)) = S L /\
  E.mu (E.run_prog (S v) Q s) = E.mu s /\ E.cert (E.run_prog (S v) Q s) = E.cert s.
Proof.
  intros Q c L v. induction v as [| v IH]; intros s Hf He Hp Hv.
  - assert (Hn : E.next_instr Q (E.core_of s) = Some (E.DEC c L))
      by (apply sm_gnext_intro; [exact He | rewrite Hp; exact Hf | discriminate]).
    assert (Hst : E.run_prog 1 Q s = E.exec s (E.DEC c L)) by (simpl; unfold E.step; rewrite Hn; reflexivity).
    rewrite Hst.
    destruct (sm_gplain_exec s (E.DEC c L) (or_intror (ex_intro _ c (ex_intro _ L eq_refl))))
      as (Hf1 & Hc1 & He1 & Hm1 & Hk1).
    assert (Hk : E.core_of (E.exec s (E.DEC c L)) = E.goto (E.core_of s) (S L)).
    { simpl. unfold E.cexec. rewrite He. rewrite Hv, Hp. reflexivity. }
    repeat split.
    + rewrite Hk. exact Hv.
    + intros d _. rewrite Hk. destruct d; reflexivity.
    + exact Hf1.
    + exact Hc1.
    + rewrite He1. exact He.
    + rewrite Hk. reflexivity.
    + exact Hm1.
    + exact Hk1.
  - assert (Hn : E.next_instr Q (E.core_of s) = Some (E.DEC c L))
      by (apply sm_gnext_intro; [exact He | rewrite Hp; exact Hf | discriminate]).
    rewrite sm_grun_succ.
    assert (Hst : E.step Q s = E.exec s (E.DEC c L)) by (unfold E.step; rewrite Hn; reflexivity).
    rewrite Hst.
    destruct (sm_gplain_exec s (E.DEC c L) (or_intror (ex_intro _ c (ex_intro _ L eq_refl))))
      as (Hf1 & Hc1 & He1 & Hm1 & Hk1).
    assert (Hk : E.core_of (E.exec s (E.DEC c L)) = E.write (E.core_of s) c v L).
    { simpl. unfold E.cexec. rewrite He, Hv. reflexivity. }
    destruct (IH (E.exec s (E.DEC c L))) as (Hv2 & Hv2' & Hf2 & Hc2 & He2 & Hp2 & Hm2 & Hk2).
    + exact Hf.
    + rewrite He1. exact He.
    + rewrite Hk. destruct c; reflexivity.
    + rewrite Hk. destruct c; reflexivity.
    + repeat split.
      * exact Hv2.
      * intros d Hd. rewrite Hv2' by exact Hd. rewrite Hk. destruct c, d; simpl; congruence.
      * rewrite Hf2. exact Hf1.
      * rewrite Hc2. exact Hc1.
      * exact He2.
      * exact Hp2.
      * rewrite Hm2. exact Hm1.
      * rewrite Hk2. exact Hk1.
Qed.

(* ================================================================= *)
(* A compiled two-counter program keeps everything but the counters. *)
(* ================================================================= *)

Lemma sm_compile_run : forall (Mp : list E.minsky) n s,
  E.err (E.core_of s) = false ->
  E.window (E.core_of (E.run_prog n (E.compile Mp) s)) = E.mrun n Mp (E.window (E.core_of s)) /\
  E.facts (E.core_of (E.run_prog n (E.compile Mp) s)) = E.facts (E.core_of s) /\
  E.chan (E.core_of (E.run_prog n (E.compile Mp) s)) = E.chan (E.core_of s) /\
  E.err (E.core_of (E.run_prog n (E.compile Mp) s)) = false /\
  E.mu (E.run_prog n (E.compile Mp) s) = E.mu s /\
  E.cert (E.run_prog n (E.compile Mp) s) = E.cert s.
Proof.
  intros Mp n. induction n as [| n IH]; intros s He; [simpl; repeat split; auto |].
  rewrite sm_grun_succ.
  destruct (E.next_instr (E.compile Mp) (E.core_of s)) as [i |] eqn:Hn.
  - assert (Hst : E.step (E.compile Mp) s = E.exec s i) by (unfold E.step; rewrite Hn; reflexivity).
    destruct (sm_gnext_some _ _ _ Hn) as (_ & Hf & _).
    assert (Hi : (exists c, i = E.INC c) \/ (exists c j, i = E.DEC c j)).
    { unfold E.compile in Hf. rewrite E.fetch_map in Hf.
      destruct (E.fetch Mp (E.pc (E.core_of s))) as [[c | c j] |]; simpl in Hf; inversion Hf;
        [left; exists c | right; exists c, j]; reflexivity. }
    destruct (sm_gplain_exec s i Hi) as (Hf1 & Hc1 & He1 & Hm1 & Hk1).
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

(* ================================================================= *)
(* The reduction program.                                             *)
(* ================================================================= *)

Definition sm_ghblock (H : list mm2_instr) : list E.instr := E.compile (map sm_of_mm2 H).

Definition sm_grice_pre (a b : nat) (H : list mm2_instr) : list E.instr :=
  let L1 := S (a + b + length (sm_ghblock H)) in
  (sm_gincs E.CA a ++ sm_gincs E.CB b) ++ sm_greloc (a + b) (sm_ghblock H) ++
  [E.DEC E.CA L1; E.DEC E.CB (S L1)].

Definition sm_grice_prog (a b : nat) (H : list mm2_instr) (P : list E.instr) : list E.instr :=
  sm_grice_pre a b H ++ sm_greloc (length (sm_grice_pre a b H)) P.

Lemma sm_grice_pre_length : forall a b H,
  length (sm_grice_pre a b H) = S (S (a + b + length (sm_ghblock H))).
Proof.
  intros. unfold sm_grice_pre. rewrite !app_length, sm_greloc_length, !sm_gincs_length.
  simpl. lia.
Qed.

Lemma sm_gfetch_app_left : forall (A B : list E.instr) n,
  n <= length A -> E.fetch (A ++ B) n = E.fetch A n.
Proof.
  intros A B n H. destruct n as [| n]; [reflexivity |]. simpl. apply nth_error_app1. lia.
Qed.

Lemma sm_gfetch_app_right : forall (A C : list E.instr) p,
  E.fetch (A ++ C) (length A + S p) = E.fetch C (S p).
Proof.
  intros A C p. replace (length A + S p) with (S (length A + p)) by lia. simpl.
  rewrite nth_error_app2 by lia. f_equal. lia.
Qed.

Lemma sm_grice_prog_split : forall a b H P,
  let L1 := S (a + b + length (sm_ghblock H)) in
  sm_grice_prog a b H P =
  ((sm_gincs E.CA a ++ sm_gincs E.CB b) ++ sm_greloc (a + b) (sm_ghblock H)) ++
  ([E.DEC E.CA L1; E.DEC E.CB (S L1)] ++ sm_greloc (S L1) P).
Proof.
  intros a b H P L1. unfold sm_grice_prog. rewrite sm_grice_pre_length.
  unfold sm_grice_pre. fold L1. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma sm_grice_fetch_a : forall a b H P p, 1 <= p <= a ->
  E.fetch (sm_grice_prog a b H P) (p + 0) = Some (E.INC E.CA).
Proof.
  intros a b H P p Hp. unfold sm_grice_prog, sm_grice_pre.
  rewrite <- !app_assoc. rewrite sm_gfetch_app_left by (rewrite sm_gincs_length; lia).
  destruct p as [| p]; [lia |]. simpl. unfold sm_gincs. apply nth_error_repeat. lia.
Qed.

Lemma sm_grice_fetch_b : forall a b H P p, 1 <= p <= b ->
  E.fetch (sm_grice_prog a b H P) (p + a) = Some (E.INC E.CB).
Proof.
  intros a b H P p Hp. unfold sm_grice_prog, sm_grice_pre.
  rewrite <- !app_assoc.
  destruct p as [| p]; [lia |]. replace (S p + a) with (S (a + p)) by lia. simpl.
  rewrite nth_error_app2 by (rewrite sm_gincs_length; lia).
  rewrite sm_gincs_length. replace (a + p - a) with p by lia.
  rewrite nth_error_app1 by (rewrite sm_gincs_length; lia).
  unfold sm_gincs. apply nth_error_repeat. lia.
Qed.

Lemma sm_grice_embeds_h : forall a b H P,
  sm_gembeds (sm_grice_prog a b H P) (sm_ghblock H) (a + b).
Proof.
  intros a b H P. unfold sm_grice_prog, sm_grice_pre.
  set (A := sm_gincs E.CA a ++ sm_gincs E.CB b).
  assert (HA : length A = a + b) by (unfold A; rewrite app_length, !sm_gincs_length; reflexivity).
  rewrite <- HA. rewrite <- !app_assoc. apply sm_gembeds_app.
Qed.

Lemma sm_grice_fetch_clear1 : forall a b H P,
  let L1 := S (a + b + length (sm_ghblock H)) in
  E.fetch (sm_grice_prog a b H P) L1 = Some (E.DEC E.CA L1).
Proof.
  intros a b H P L1. rewrite sm_grice_prog_split. fold L1.
  set (A := (sm_gincs E.CA a ++ sm_gincs E.CB b) ++ sm_greloc (a + b) (sm_ghblock H)).
  assert (Eq : L1 = length A + 1)
    by (unfold A; rewrite !app_length, sm_greloc_length, !sm_gincs_length; unfold L1; lia).
  transitivity (E.fetch (A ++ ([E.DEC E.CA L1; E.DEC E.CB (S L1)] ++ sm_greloc (S L1) P)) (length A + 1));
    [f_equal; exact Eq |].
  rewrite sm_gfetch_app_right. reflexivity.
Qed.

Lemma sm_grice_fetch_clear2 : forall a b H P,
  let L1 := S (a + b + length (sm_ghblock H)) in
  E.fetch (sm_grice_prog a b H P) (S L1) = Some (E.DEC E.CB (S L1)).
Proof.
  intros a b H P L1. rewrite sm_grice_prog_split. fold L1.
  set (A := (sm_gincs E.CA a ++ sm_gincs E.CB b) ++ sm_greloc (a + b) (sm_ghblock H)).
  assert (Eq : S L1 = length A + 2)
    by (unfold A; rewrite !app_length, sm_greloc_length, !sm_gincs_length; unfold L1; lia).
  transitivity (E.fetch (A ++ ([E.DEC E.CA L1; E.DEC E.CB (S L1)] ++ sm_greloc (S L1) P)) (length A + 2));
    [f_equal; exact Eq |].
  rewrite sm_gfetch_app_right. reflexivity.
Qed.

Lemma sm_grice_embeds_p : forall a b H P,
  sm_gembeds (sm_grice_prog a b H P) P (length (sm_grice_pre a b H)).
Proof.
  intros a b H P. unfold sm_grice_prog. rewrite <- (app_nil_r (sm_greloc _ P)).
  apply sm_gembeds_app.
Qed.

Lemma sm_grice_length : forall a b H P,
  length (sm_grice_prog a b H P) = length (sm_grice_pre a b H) + length P.
Proof. intros. unfold sm_grice_prog. rewrite app_length, sm_greloc_length. reflexivity. Qed.

Lemma sm_ghblock_no_halt : forall H, ~ In E.HALT (sm_ghblock H).
Proof.
  intros H Hin. unfold sm_ghblock, E.compile in Hin. rewrite map_map in Hin.
  apply in_map_iff in Hin. destruct Hin as [[| | j | j] [Hx _]]; discriminate.
Qed.

(* After counting up to a and b. *)
Lemma sm_grice_phase1 : forall a b H P,
  let s1 := E.run_prog (a + b) (sm_grice_prog a b H P) (E.start 0 0) in
  E.ca (E.core_of s1) = a /\ E.cb (E.core_of s1) = b /\
  E.facts (E.core_of s1) = [] /\ E.chan (E.core_of s1) = None /\
  E.err (E.core_of s1) = false /\ E.pc (E.core_of s1) = S (a + b) /\
  E.mu s1 = 0 /\ E.cert s1 = false.
Proof.
  intros a b H P s1. unfold s1. rewrite sm_grun_add.
  set (Q := sm_grice_prog a b H P).
  destruct (sm_gincs_run Q E.CA a 0 (E.start 0 0)) as (Hv1 & Hv1' & Hf1 & Hc1 & He1 & Hp1 & Hm1 & Hk1).
  { intros p Hp. apply sm_grice_fetch_a. exact Hp. }
  { reflexivity. }
  { reflexivity. }
  destruct (sm_gincs_run Q E.CB b a (E.run_prog a Q (E.start 0 0)))
    as (Hv2 & Hv2' & Hf2 & Hc2 & He2 & Hp2 & Hm2 & Hk2).
  { intros p Hp. apply sm_grice_fetch_b. exact Hp. }
  { exact He1. }
  { rewrite Hp1. lia. }
  repeat split.
  - change (E.ca (E.core_of (E.run_prog b Q (E.run_prog a Q (E.start 0 0)))))
      with (E.val (E.core_of (E.run_prog b Q (E.run_prog a Q (E.start 0 0)))) E.CA).
    rewrite Hv2' by discriminate. rewrite Hv1. reflexivity.
  - change (E.cb (E.core_of (E.run_prog b Q (E.run_prog a Q (E.start 0 0)))))
      with (E.val (E.core_of (E.run_prog b Q (E.run_prog a Q (E.start 0 0)))) E.CB).
    rewrite Hv2, Hv1' by discriminate. reflexivity.
  - rewrite Hf2, Hf1. reflexivity.
  - rewrite Hc2, Hc1. reflexivity.
  - exact He2.
  - rewrite Hp2. lia.
  - rewrite Hm2, Hm1. reflexivity.
  - rewrite Hk2, Hk1. reflexivity.
Qed.

Definition sm_gat1 (s : E.state) : E.state := E.mkst (E.goto (E.core_of s) 1) (E.mu s) (E.cert s).

Lemma sm_gat1_rel : forall s off len, E.pc (E.core_of s) = S off ->
  sm_gsrel off len 0 0 (sm_gat1 s) s.
Proof.
  intros s off len Hp. unfold sm_gsrel, sm_gcrel, sm_gat1, E.goto. simpl.
  rewrite sm_fsh_zero, sm_fsh_opt_zero. repeat split; auto; try lia.
  rewrite Hp. unfold sm_rj. destruct (Nat.leb_spec 1 1), (Nat.leb_spec 1 len); simpl; lia.
Qed.

Lemma sm_gfinal_equiv : forall Q P off da db,
  sm_gembeds Q P off -> length Q = off + length P ->
  (exists T0, sm_gsrel off (length P) da db (E.start 0 0) (E.run_prog T0 Q (E.start 0 0))) ->
  sm_gequiv Q P.
Proof.
  intros Q P off da db Hemb HQ [T0 HT].
  assert (Hall : forall m, sm_gsrel off (length P) da db (E.run_prog m P (E.start 0 0))
                              (E.run_prog (T0 + m) Q (E.start 0 0))).
  { intro m. rewrite sm_grun_add. apply (sm_gblock_run_final Q P off da db Hemb HQ), HT. }
  assert (Hag : forall s t, sm_gsrel off (length P) da db s t -> sm_gagree s t).
  { intros s t ((Ha & Hb & _ & _ & _ & _ & He & _) & Hm & Hk). repeat split; auto. }
  split.
  - intros s [N [-> HN]].
    set (m := N - T0).
    assert (Es : E.run_prog (T0 + m) Q (E.start 0 0) = E.run_prog N Q (E.start 0 0))
      by (apply sm_ghalted_after; [unfold m; lia | exact HN]).
    pose proof (Hall m) as Hr. rewrite Es in Hr.
    exists (E.run_prog m P (E.start 0 0)). split.
    + exists m. split; [reflexivity |].
      unfold E.halted. destruct (E.next_instr P (E.core_of (E.run_prog m P (E.start 0 0)))) eqn:Hn;
        [| reflexivity].
      exfalso. apply (sm_gblock_not_halted Q P off da db _ _ Hemb Hr); [congruence | exact HN].
    + apply sm_gagree_sym, Hag, Hr.
  - intros t [m [-> Hm]].
    exists (E.run_prog (T0 + m) Q (E.start 0 0)). split.
    + exists (T0 + m). split; [reflexivity |].
      apply (sm_gblock_halted Q P off da db (E.core_of (E.run_prog m P (E.start 0 0)))); auto.
      apply (Hall m).
    + apply sm_gagree_sym, Hag, (Hall m).
Qed.

Lemma sm_option_dec' : forall (o : option E.mconf), o = None \/ ~ o = None.
Proof. intros [y |]; [right; discriminate | left; reflexivity]. Qed.

Theorem sm_grice_prog_halts : forall H a b P,
  MM2_HALTING (H, a, b) -> sm_gequiv (sm_grice_prog a b H P) P.
Proof.
  intros H a b P Hh.
  set (Q := sm_grice_prog a b H P).
  set (Mp := map sm_of_mm2 H).
  set (B := sm_ghblock H).
  apply sm_mm2_terminates_iff in Hh. fold Mp in Hh. destruct Hh as [n1 Hn1].
  destruct (sm_least (fun n => E.mstep Mp (E.mrun n Mp (1, (a, b))) = None)
              (fun n => sm_option_dec' _) n1 Hn1) as [n0 [Hn0 Hlt]].
  destruct (sm_grice_phase1 a b H P) as (Ha1 & Hb1 & Hf1 & Hc1 & He1 & Hp1 & Hm1 & Hk1).
  fold Q in Ha1, Hb1, Hf1, Hc1, He1, Hp1, Hm1, Hk1.
  set (s1 := E.run_prog (a + b) Q (E.start 0 0)) in *.
  set (sB := sm_gat1 s1).
  assert (HeB : E.err (E.core_of sB) = false) by exact He1.
  assert (HwinB : E.window (E.core_of sB) = (1, (a, b))).
  { unfold E.window, sB, sm_gat1, E.goto. simpl. rewrite Ha1, Hb1. reflexivity. }
  destruct (sm_compile_run Mp n0 sB HeB) as (HwB & HfB & HcB & HeB2 & HmB & HkB).
  rewrite HwinB in HwB. change (E.compile Mp) with B in HwB, HfB, HcB, HeB2, HmB, HkB.
  destruct (E.mrun n0 Mp (1, (a, b))) as [p' [a' b']] eqn:Erun.
  assert (HhB : E.next_instr B (E.core_of (E.run_prog n0 B sB)) = None).
  { destruct (E.simulation_step Mp _ HeB2) as [Hnone _]. apply Hnone. fold B.
    rewrite HwB. exact Hn0. }
  assert (HgoB : forall m, m < n0 -> E.next_instr B (E.core_of (E.run_prog m B sB)) <> None).
  { intros m Hm Hn. apply (Hlt m Hm).
    destruct (sm_compile_run Mp m sB HeB) as (Hw' & _ & _ & He' & _).
    rewrite HwinB in Hw'. rewrite <- Hw'.
    destruct (E.simulation_step Mp _ He') as [Hnone _]. apply Hnone. exact Hn. }
  assert (Hrel1 : sm_gsrel (a + b) (length B) 0 0 sB s1) by (apply sm_gat1_rel; exact Hp1).
  pose proof (sm_gblock_run_mid Q B (a + b) 0 0 (sm_grice_embeds_h a b H P) n0 sB s1 Hrel1 HgoB) as Hrel2.
  set (s2 := E.run_prog n0 Q s1) in *.
  destruct Hrel2 as ((Ha2 & Hb2 & _ & _ & Hf2 & Hc2 & He2 & Hp2) & Hm2 & Hk2).
  assert (Hpc' : E.pc (E.core_of (E.run_prog n0 B sB)) = p') by (unfold E.window in HwB; congruence).
  assert (Hout : ~ (1 <= p' <= length B)).
  { intro Hr. unfold E.next_instr in HhB. rewrite HeB2, Hpc' in HhB.
    destruct p' as [| q]; [lia |]. simpl in HhB.
    destruct (nth_error B q) as [i |] eqn:Hi.
    - destruct i; try discriminate. apply (sm_ghblock_no_halt H). eapply nth_error_In. exact Hi.
    - apply nth_error_None in Hi. lia. }
  set (L1 := S (a + b + length (sm_ghblock H))).
  assert (Hpc2 : E.pc (E.core_of s2) = L1).
  { rewrite Hp2, Hpc', sm_rj_out by exact Hout. unfold L1. fold B. lia. }
  assert (Hva : E.val (E.core_of s2) E.CA = a') by (simpl; rewrite <- Ha2; unfold E.window in HwB; congruence).
  assert (Hvb : E.val (E.core_of s2) E.CB = b') by (simpl; rewrite <- Hb2; unfold E.window in HwB; congruence).
  assert (Hf2' : E.facts (E.core_of s2) = []) by (rewrite Hf2, HfB, sm_fsh_zero; exact Hf1).
  assert (Hc2' : E.chan (E.core_of s2) = None) by (rewrite Hc2, HcB, sm_fsh_opt_zero; exact Hc1).
  assert (He2' : E.err (E.core_of s2) = false) by (rewrite <- He2; exact HeB2).
  assert (Hm2' : E.mu s2 = 0) by (rewrite <- Hm2, HmB; exact Hm1).
  assert (Hk2' : E.cert s2 = false) by (rewrite <- Hk2, HkB; exact Hk1).
  destruct (sm_gclear_run Q E.CA L1 a' s2 (sm_grice_fetch_clear1 a b H P) He2' Hpc2 Hva)
    as (Hv3 & Hv3' & Hf3 & Hc3 & He3 & Hp3 & Hm3 & Hk3).
  set (s3 := E.run_prog (S a') Q s2) in *.
  assert (Hvb3 : E.val (E.core_of s3) E.CB = b') by (rewrite Hv3' by discriminate; exact Hvb).
  destruct (sm_gclear_run Q E.CB (S L1) b' s3 (sm_grice_fetch_clear2 a b H P) He3 Hp3 Hvb3)
    as (Hv4 & Hv4' & Hf4 & Hc4 & He4 & Hp4 & Hm4 & Hk4).
  set (s4 := E.run_prog (S b') Q s3) in *.
  apply (sm_gfinal_equiv Q P (length (sm_grice_pre a b H)) (E.va (E.core_of s4)) (E.vb (E.core_of s4))).
  - apply sm_grice_embeds_p.
  - apply sm_grice_length.
  - exists (a + b + n0 + S a' + S b').
    replace (E.run_prog (a + b + n0 + S a' + S b') Q (E.start 0 0)) with s4
      by (unfold s4, s3, s2, s1; rewrite !sm_grun_add; reflexivity).
    split; [| split].
    + unfold sm_gcrel. cbn [E.start E.start_core E.core_of E.ca E.cb E.va E.vb E.facts E.chan E.err E.pc map option_map].
      split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]].
      * change (E.ca (E.core_of s4)) with (E.val (E.core_of s4) E.CA).
        rewrite Hv4' by discriminate. symmetry. exact Hv3.
      * symmetry. exact Hv4.
      * lia.
      * lia.
      * rewrite Hf4, Hf3, Hf2'. reflexivity.
      * rewrite Hc4, Hc3, Hc2'. reflexivity.
      * rewrite He4. reflexivity.
      * rewrite Hp4, sm_grice_pre_length. unfold sm_rj.
        destruct (Nat.leb_spec 1 1), (Nat.leb_spec 1 (length P)); simpl; unfold L1; lia.
    + cbn [E.mu E.start]. rewrite Hm4, Hm3, Hm2'. reflexivity.
    + cbn [E.cert E.start]. rewrite Hk4, Hk3, Hk2'. reflexivity.
Qed.

Theorem sm_grice_prog_diverges : forall H a b P,
  ~ MM2_HALTING (H, a, b) ->
  forall N, ~ E.halted (sm_grice_prog a b H P) (E.core_of (E.run_prog N (sm_grice_prog a b H P) (E.start 0 0))).
Proof.
  intros H a b P Hnh N HN.
  set (Q := sm_grice_prog a b H P) in *.
  set (Mp := map sm_of_mm2 H).
  set (B := sm_ghblock H).
  destruct (sm_grice_phase1 a b H P) as (Ha1 & Hb1 & Hf1 & Hc1 & He1 & Hp1 & Hm1 & Hk1).
  fold Q in Ha1, Hb1, Hf1, Hc1, He1, Hp1, Hm1, Hk1.
  set (s1 := E.run_prog (a + b) Q (E.start 0 0)) in *.
  set (sB := sm_gat1 s1).
  assert (HeB : E.err (E.core_of sB) = false) by exact He1.
  assert (HwinB : E.window (E.core_of sB) = (1, (a, b))).
  { unfold E.window, sB, sm_gat1, E.goto. simpl. rewrite Ha1, Hb1. reflexivity. }
  assert (HgoB : forall m, E.next_instr B (E.core_of (E.run_prog m B sB)) <> None).
  { intros m Hn. apply Hnh. apply sm_mm2_terminates_iff. exists m. fold Mp.
    destruct (sm_compile_run Mp m sB HeB) as (Hw' & _ & _ & He' & _).
    rewrite HwinB in Hw'. rewrite <- Hw'.
    destruct (E.simulation_step Mp _ He') as [Hnone _]. apply Hnone. exact Hn. }
  assert (Hrel1 : sm_gsrel (a + b) (length B) 0 0 sB s1) by (apply sm_gat1_rel; exact Hp1).
  pose proof (sm_gblock_run_mid Q B (a + b) 0 0 (sm_grice_embeds_h a b H P) N sB s1 Hrel1
                (fun m _ => HgoB m)) as Hrel2.
  apply (sm_gblock_not_halted Q B (a + b) 0 0 _ _ (sm_grice_embeds_h a b H P) Hrel2 (HgoB N)).
  unfold s1. rewrite <- sm_grun_add.
  rewrite (sm_ghalted_after N (a + b + N) Q (E.start 0 0)) by (lia || exact HN).
  exact HN.
Qed.

(* ================================================================= *)
(* A program that never stops, and Rice's theorem.                    *)
(* ================================================================= *)

Definition sm_gloop : list E.instr := [E.INC E.CA; E.DEC E.CA 1].

Lemma sm_gloop_runs : forall n s,
  E.err (E.core_of s) = false ->
  (E.pc (E.core_of s) = 1 \/ (E.pc (E.core_of s) = 2 /\ E.ca (E.core_of s) <> 0)) ->
  E.err (E.core_of (E.run_prog n sm_gloop s)) = false /\
  (E.pc (E.core_of (E.run_prog n sm_gloop s)) = 1 \/
   (E.pc (E.core_of (E.run_prog n sm_gloop s)) = 2 /\ E.ca (E.core_of (E.run_prog n sm_gloop s)) <> 0)).
Proof.
  induction n as [| n IH]; intros s He Hp; [auto |].
  rewrite sm_grun_succ.
  destruct Hp as [Hp | [Hp Hv]].
  - assert (Ek : E.core_of (E.step sm_gloop s) =
                 E.write (E.core_of s) E.CA (S (E.ca (E.core_of s))) 2).
    { unfold E.step, E.next_instr. rewrite He, Hp. simpl. unfold E.cexec. rewrite He, Hp.
      unfold E.write. simpl. rewrite He. reflexivity. }
    apply IH; rewrite Ek; simpl.
    + exact He.
    + right. split; [reflexivity | discriminate].
  - destruct (E.ca (E.core_of s)) as [| v] eqn:Ev; [congruence |].
    assert (Ek : E.core_of (E.step sm_gloop s) = E.write (E.core_of s) E.CA v 1).
    { unfold E.step, E.next_instr. rewrite He, Hp. simpl. unfold E.cexec. rewrite He. simpl.
      rewrite Ev. unfold E.write. simpl. rewrite He. reflexivity. }
    apply IH; rewrite Ek; simpl.
    + exact He.
    + left. reflexivity.
Qed.

Lemma sm_gloop_diverges : forall N, ~ E.halted sm_gloop (E.core_of (E.run_prog N sm_gloop (E.start 0 0))).
Proof.
  intros N HN. destruct (sm_gloop_runs N (E.start 0 0) eq_refl (or_introl eq_refl)) as [He Hp].
  unfold E.halted, E.next_instr in HN. rewrite He in HN.
  destruct Hp as [Hp | [Hp _]]; rewrite Hp in HN; discriminate.
Qed.

Lemma sm_gnever_equiv : forall P Q,
  (forall N, ~ E.halted P (E.core_of (E.run_prog N P (E.start 0 0)))) ->
  (forall N, ~ E.halted Q (E.core_of (E.run_prog N Q (E.start 0 0)))) ->
  sm_gequiv P Q.
Proof.
  intros P Q HP HQ. split.
  - intros s [N [-> HN]]. exfalso. exact (HP N HN).
  - intros t [N [-> HN]]. exfalso. exact (HQ N HN).
Qed.

Definition sm_gext (Pi : list E.instr -> Prop) : Prop :=
  forall p q, sm_gequiv p q -> Pi p -> Pi q.

Lemma sm_gext_compl : forall Pi, sm_gext Pi -> sm_gext (complement Pi).
Proof.
  intros Pi H p q Hpq Hnp Hq. apply Hnp. apply (H q p); [apply sm_gequiv_sym, Hpq | exact Hq].
Qed.

Lemma sm_guest_rice_loop : forall (Pi : list E.instr -> Prop) y,
  sm_gext Pi -> Pi y -> ~ Pi sm_gloop -> undecidable Pi.
Proof.
  intros Pi y Hext Hy Hloop.
  apply undecidability_from_complement.
  apply (undecidability_from_reducibility sm_MM2_HALTING_compl_undec).
  exists (fun q : MM2_PROBLEM => let '(H, a, b) := q in sm_grice_prog a b H y).
  intros [[H a] b]. unfold complement. split.
  - intros Hnh HPi. apply Hloop.
    apply (Hext (sm_grice_prog a b H y)); [| exact HPi].
    apply sm_gnever_equiv; [apply sm_grice_prog_diverges, Hnh | apply sm_gloop_diverges].
  - intros HnPi Hh. apply HnPi.
    apply (Hext y); [apply sm_gequiv_sym, sm_grice_prog_halts, Hh | exact Hy].
Qed.

(* Rice's theorem for the small machine from the clean start. *)
Theorem sm_guest_rice : forall (Pi : list E.instr -> Prop) y n,
  sm_gext Pi -> Pi y -> ~ Pi n -> undecidable Pi.
Proof.
  intros Pi y n Hext Hy Hn Hdec.
  destruct Hdec as [d Hd] eqn:Hdec'.
  destruct (d sm_gloop) eqn:Hdl.
  - assert (Hl : Pi sm_gloop) by (apply Hd; exact Hdl).
    apply (undecidability_from_complement (p := Pi)); [| exact Hdec].
    apply (sm_guest_rice_loop (complement Pi) n).
    + apply sm_gext_compl, Hext.
    + exact Hn.
    + intro H. exact (H Hl).
  - assert (Hl : ~ Pi sm_gloop) by (intro H; apply Hd in H; congruence).
    exact (sm_guest_rice_loop Pi y Hext Hy Hl Hdec).
Qed.

(* "Halts from the clean start" is one such property. *)
Corollary sm_guest_halting_clean_undecidable :
  undecidable (fun P : list E.instr => exists n, E.halted P (E.core_of (E.run_prog n P (E.start 0 0)))).
Proof.
  apply (sm_guest_rice _ [] sm_gloop).
  - intros p q [H1 _] [n Hn]. destruct (H1 _ (ex_intro _ n (conj eq_refl Hn))) as [t [[m [-> Hm]] _]].
    exists m. exact Hm.
  - exists 0. reflexivity.
  - intros [n Hn]. exact (sm_gloop_diverges n Hn).
Qed.

Print Assumptions sm_grice_prog_halts.
Print Assumptions sm_grice_prog_diverges.
Print Assumptions sm_guest_rice.
Print Assumptions sm_guest_halting_clean_undecidable.
