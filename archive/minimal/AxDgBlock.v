(** AxDgBlock: a block of the host machine run inside a bigger program whose
    registers have been written before, so that the versions differ.

    SmHostBlocks.v relates a run of a block B to the run of the block inside a
    bigger program Q step by step, but it needs the versions of the registers
    that B checks to agree exactly.  A program that has already written those
    registers (a preamble that computes, then hands over to B) breaks that.

    Here the two runs are related by a SHIFT of the versions.  The version of
    register r in the bigger program is the version in the standalone run
    plus a number dl r that stays fixed, because every write adds one on both
    sides.  A fact of the bigger program is the fact of the standalone run
    with dl (its register) added to its version.  A CHECK or COMMIT then
    behaves the same in both: the claim (property, register) is the same, the
    versions are shifted together, and fact identity is preserved by the
    shift.

    Results (all closed):

      ax_dg_block_step   one step of B and the matching step of Q keep the
                         shifted relation, and Q has the matching instruction;
      ax_dg_block_run    the relation holds for every run length n, for a
                         block whose exit line in Q is a HALT or past the end;
      ax_dg_block_stop   B stopped implies Q stopped (at the related state);
      ax_dg_block_go     B running implies Q running;
      ax_dg_blind_*      what the relation says about the claims: the
                         (property, register) lists of the fact tables and the
                         channels are equal. *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is recursion theory on the multi-register host machine (blocks that run with the versions of the registers shifted), built for
   the content diagonal of AxDgFixed.v. That file connects it to the axis
   (AxCore.v); the host machine's link to the abstract record lives in
   UniversalInterpreterLinks.v. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Minimal.EarnedMulti.
Require Minimal.UniversalCodes.
Require Import Minimal.SmHostBlocks.
Module M := Minimal.EarnedMulti.
Module UC := Minimal.UniversalCodes.

Local Notation hinstr := (@M.instr UC.hprop).
Local Notation hcore := (@M.core UC.hprop).
Local Notation hstate := (@M.state UC.hprop).
Local Notation hfact := (@M.fact UC.hprop).
Local Notation hcexec := (M.cexec UC.hprop_eqb UC.heval).
Local Notation hstep := (M.step UC.hprop_eqb UC.heval).
Local Notation hrun_prog := (M.run_prog UC.hprop_eqb UC.heval).
Local Notation hfact_eqb := (M.fact_eqb UC.hprop_eqb).

(** The fact with a version shifted by a number per register. *)
Definition ax_dg_shift (dl : nat -> nat) (f : hfact) : hfact :=
  M.mkfact (M.f_prop f) (M.f_reg f) (M.f_ver f + dl (M.f_reg f)).

(** The claim of a fact: the property and the register, not the version. *)
Definition ax_dg_blind (f : hfact) : UC.hprop * nat := (M.f_prop f, M.f_reg f).

Lemma ax_dg_blind_shift : forall dl f, ax_dg_blind (ax_dg_shift dl f) = ax_dg_blind f.
Proof. intros dl [p r v]. reflexivity. Qed.

Lemma ax_dg_shift_eqb : forall dl f g,
  hfact_eqb (ax_dg_shift dl f) (ax_dg_shift dl g) = hfact_eqb f g.
Proof.
  intros dl [p r v] [q s w]. unfold M.fact_eqb, ax_dg_shift. simpl.
  destruct (Nat.eqb_spec r s) as [<- | Hne].
  - replace (Nat.eqb (v + dl r) (w + dl r)) with (Nat.eqb v w); [reflexivity |].
    apply eq_true_iff_eq. rewrite !Nat.eqb_eq. lia.
  - replace (Nat.eqb r s) with false by (symmetry; apply Nat.eqb_neq; exact Hne).
    rewrite !andb_false_r, !andb_false_l. reflexivity.
Qed.

Lemma ax_dg_existsb_shift : forall dl f fs,
  existsb (hfact_eqb (ax_dg_shift dl f)) (map (ax_dg_shift dl) fs) = existsb (hfact_eqb f) fs.
Proof.
  intros dl f fs. induction fs as [| g fs IH]; [reflexivity |].
  simpl. rewrite IH, ax_dg_shift_eqb. reflexivity.
Qed.

(** Related cores: B's core k and Q's core k', with the versions of Q's core
    those of B's plus dl, and the facts of Q's core those of B's shifted. *)
Definition ax_dg_crel (dl : nat -> nat) (off len : nat) (k k' : hcore) : Prop :=
  (forall r, M.vals k r = M.vals k' r) /\
  (forall r, M.vers k' r = M.vers k r + dl r) /\
  M.facts k' = map (ax_dg_shift dl) (M.facts k) /\
  M.chan k' = option_map (ax_dg_shift dl) (M.chan k) /\
  M.err k = M.err k' /\
  M.pc k' = sm_rj off len (M.pc k).

Definition ax_dg_srel (dl : nat -> nat) (off len : nat) (s s' : hstate) : Prop :=
  ax_dg_crel dl off len (M.core_of s) (M.core_of s') /\ M.mu s = M.mu s' /\ M.cert s = M.cert s'.

Lemma ax_dg_block_cstep : forall dl Q B off k k' i,
  sm_embeds Q B off -> ax_dg_crel dl off (length B) k k' ->
  M.next_instr B k = Some i ->
  M.next_instr Q k' = Some (sm_ri off (length B) i) /\
  ax_dg_crel dl off (length B) (hcexec k i) (hcexec k' (sm_ri off (length B) i)).
Proof.
  intros dl Q B off k k' i Hemb (Hv & Hw & Hf & Hc & He & Hp) Hn.
  destruct (sm_next_some B k i Hn) as (Ek & Hfe & Hh).
  assert (Hr : 1 <= M.pc k <= length B) by (eapply sm_fetch_range; eauto).
  rewrite sm_rj_in in Hp by exact Hr.
  assert (Hq : M.fetch Q (M.pc k') = Some (sm_ri off (length B) i)).
  { rewrite Hp, (Hemb _ Hr), Hfe. reflexivity. }
  assert (Ek' : M.err k' = false) by congruence.
  split.
  { apply sm_next_intro; [exact Ek' | exact Hq |]. intro H. apply sm_ri_halt in H. auto. }
  unfold M.cexec. rewrite Ek, Ek'.
  destruct i as [r | r j | | p r | p r |]; cbv beta iota delta [sm_ri].
  - (* INC *)
    unfold ax_dg_crel. rewrite <- (Hv r). repeat split.
    + intro q. rewrite !M.multi_val_write. destruct (Nat.eqb r q); auto.
    + intro q. rewrite !M.multi_ver_write. rewrite (Hw q). destruct (Nat.eqb r q); lia.
    + simpl. exact Hf.
    + simpl. exact Hc.
    + simpl. exact He.
    + simpl. rewrite Hp, sm_rj_S by exact Hr. reflexivity.
  - (* DEC *)
    rewrite <- (Hv r). destruct (M.vals k r) as [| v].
    + unfold ax_dg_crel. simpl. repeat split; auto.
      rewrite Hp, sm_rj_S by exact Hr. reflexivity.
    + unfold ax_dg_crel. repeat split.
      * intro q. rewrite !M.multi_val_write. destruct (Nat.eqb r q); auto.
      * intro q. rewrite !M.multi_ver_write. rewrite (Hw q). destruct (Nat.eqb r q); lia.
      * simpl. exact Hf.
      * simpl. exact Hc.
      * simpl. exact He.
  - (* HALT *) congruence.
  - (* CHECK *)
    assert (Hok : M.check_ok UC.heval k p r = M.check_ok UC.heval k' p r).
    { unfold M.check_ok. rewrite Ek, Ek', (Hv r), Hf, map_length. reflexivity. }
    rewrite Hok. destruct (M.check_ok UC.heval k' p r).
    + unfold ax_dg_crel, M.record_fact, M.claim. simpl. repeat split; auto.
      * simpl. rewrite Hf. f_equal. unfold ax_dg_shift. simpl. rewrite (Hw r). reflexivity.
      * rewrite Hp, sm_rj_S by exact Hr. reflexivity.
    + unfold ax_dg_crel, M.trap. simpl. repeat split; auto.
      rewrite Hp, sm_rj_in by exact Hr. reflexivity.
  - (* COMMIT *)
    assert (Hcl : M.claim k' p r = ax_dg_shift dl (M.claim k p r)).
    { unfold M.claim, ax_dg_shift. simpl. rewrite (Hw r). reflexivity. }
    assert (Hok : M.commit_ok UC.hprop_eqb k p r = M.commit_ok UC.hprop_eqb k' p r).
    { unfold M.commit_ok. rewrite Ek, Ek', Hcl, Hf, ax_dg_existsb_shift. reflexivity. }
    rewrite Hok. destruct (M.commit_ok UC.hprop_eqb k' p r).
    + unfold ax_dg_crel, M.commit_to. simpl. rewrite Hcl. repeat split; auto.
      rewrite Hp, sm_rj_S by exact Hr. reflexivity.
    + unfold ax_dg_crel, M.trap. simpl. repeat split; auto.
      rewrite Hp, sm_rj_in by exact Hr. reflexivity.
  - (* CERTIFY *)
    assert (Hok : M.certify_ok k = M.certify_ok k').
    { unfold M.certify_ok. rewrite Ek, Ek', Hc. destruct (M.chan k); reflexivity. }
    rewrite Hok. destruct (M.certify_ok k').
    + unfold ax_dg_crel, M.goto. simpl. repeat split; auto.
      rewrite Hp, sm_rj_S by exact Hr. reflexivity.
    + unfold ax_dg_crel, M.trap. simpl. repeat split; auto.
      rewrite Hp, sm_rj_in by exact Hr. reflexivity.
Qed.

Lemma ax_dg_block_step : forall dl Q B off s s' i,
  sm_embeds Q B off -> ax_dg_srel dl off (length B) s s' ->
  M.next_instr B (M.core_of s) = Some i ->
  M.next_instr Q (M.core_of s') = Some (sm_ri off (length B) i) /\
  ax_dg_srel dl off (length B) (hstep B s) (hstep Q s').
Proof.
  intros dl Q B off s s' i Hemb [Hc [Hm Hk]] Hn.
  destruct (ax_dg_block_cstep dl Q B off _ _ i Hemb Hc Hn) as [Hn' Hc'].
  split; [exact Hn' |].
  unfold M.step. rewrite Hn, Hn'. unfold ax_dg_srel, M.exec. simpl.
  split; [exact Hc' |]. rewrite sm_cost_ri, Hm. split; [reflexivity |].
  destruct Hc as (_ & _ & _ & Hch & He & _).
  rewrite Hk. f_equal.
  destruct i; try reflexivity. simpl. unfold M.certify_ok. rewrite He.
  destruct (M.chan (M.core_of s)) as [a |], (M.chan (M.core_of s')) as [b |]; simpl in Hch;
    first [reflexivity | discriminate].
Qed.

(** The block at the line after which Q has a HALT or nothing: B stops
    exactly when Q does. *)
Lemma ax_dg_block_stop : forall dl Q B off k k',
  sm_embeds Q B off ->
  (M.fetch Q (S (length B + off)) = None \/ M.fetch Q (S (length B + off)) = Some M.HALT) ->
  ax_dg_crel dl off (length B) k k' ->
  M.halted B k -> M.halted Q k'.
Proof.
  intros dl Q B off k k' Hemb Hex (_ & _ & _ & _ & He & Hp) Hh.
  unfold M.halted, M.next_instr in *. rewrite <- He.
  destruct (M.err k); [reflexivity |].
  destruct (le_lt_dec 1 (M.pc k)) as [H1 | H1];
    [destruct (le_lt_dec (M.pc k) (length B)) as [H2 | H2] |].
  - rewrite Hp, sm_rj_in by lia. rewrite (Hemb _ (conj H1 H2)).
    destruct (M.fetch B (M.pc k)) as [[] |]; simpl in *; try discriminate; reflexivity.
  - rewrite Hp, sm_rj_out by lia. destruct Hex as [Hx | Hx]; rewrite Hx; reflexivity.
  - rewrite Hp, sm_rj_out by lia. destruct Hex as [Hx | Hx]; rewrite Hx; reflexivity.
Qed.

(** B running means Q running. *)
Lemma ax_dg_block_go : forall dl Q B off s s',
  sm_embeds Q B off -> ax_dg_srel dl off (length B) s s' ->
  M.next_instr B (M.core_of s) <> None -> M.next_instr Q (M.core_of s') <> None.
Proof.
  intros dl Q B off s s' Hemb Hs Hn.
  destruct (M.next_instr B (M.core_of s)) as [i |] eqn:Hb; [| congruence].
  destruct (ax_dg_block_step dl Q B off s s' i Hemb Hs Hb) as [H _]. congruence.
Qed.

Lemma ax_dg_block_run : forall dl Q B off,
  sm_embeds Q B off ->
  (M.fetch Q (S (length B + off)) = None \/ M.fetch Q (S (length B + off)) = Some M.HALT) ->
  forall n s s', ax_dg_srel dl off (length B) s s' ->
  ax_dg_srel dl off (length B) (hrun_prog n B s) (hrun_prog n Q s').
Proof.
  intros dl Q B off Hemb Hex n. induction n as [| n IH]; intros s s' Hs; [exact Hs |].
  rewrite !sm_run_succ.
  destruct (M.next_instr B (M.core_of s)) as [i |] eqn:Hn.
  - destruct (ax_dg_block_step dl Q B off s s' i Hemb Hs Hn) as [_ Hs']. apply IH, Hs'.
  - assert (HQh : M.halted Q (M.core_of s')).
    { apply (ax_dg_block_stop dl Q B off (M.core_of s)); [exact Hemb | exact Hex | apply Hs | exact Hn]. }
    unfold M.step. rewrite Hn. unfold M.halted in HQh. rewrite HQh. apply IH, Hs.
Qed.

(** What the relation says about the claims. *)
Lemma ax_dg_blind_facts : forall dl off len k k',
  ax_dg_crel dl off len k k' ->
  map ax_dg_blind (M.facts k') = map ax_dg_blind (M.facts k).
Proof.
  intros dl off len k k' (_ & _ & Hf & _). rewrite Hf, map_map.
  apply map_ext. intro f. apply ax_dg_blind_shift.
Qed.

Lemma ax_dg_blind_chan : forall dl off len k k',
  ax_dg_crel dl off len k k' ->
  option_map ax_dg_blind (M.chan k') = option_map ax_dg_blind (M.chan k).
Proof.
  intros dl off len k k' (_ & _ & _ & Hc & _). rewrite Hc.
  destruct (M.chan k) as [f |]; [| reflexivity]. simpl. rewrite ax_dg_blind_shift. reflexivity.
Qed.

Print Assumptions ax_dg_block_run.
Print Assumptions ax_dg_block_stop.
Print Assumptions ax_dg_block_go.
Print Assumptions ax_dg_blind_facts.
