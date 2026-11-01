(** AxDgFixed: a fixed point that keeps the claims, and the diagonal on the
    content of the fact table.

    The recursion theorem with record of the repository (sm2_kleene_obs,
    SmFixedPoint.v) gives, for a map F computed by a host program, a program
    e that agrees with F e on stopping, register 0, trap latch, ledger, flag,
    the NUMBER of facts and whether the channel is empty.  It does not keep
    which claim is in the table, and cannot in general: for F p = [INC r] with
    r one above the number of p, no program agrees with F e on any register
    (SmNoExact.v), because a program cannot name a register above its own
    number.

    A map whose values are two fixed programs does not have that problem.  The
    two programs name their own registers, and e can contain them as blocks.
    This file builds, for such a map, a program e that agrees with F e on

      every register value, the claims of the fact table (property and
      register, in order, with multiplicity), the claim in the channel, the
      trap latch, the ledger, the flag,

    and on stopping.  Only the VERSIONS recorded in the facts differ, because
    e has written registers before it hands over, and a version says how many
    writes came before, not which claim was made.

    Results (all closed):

      ax_dg_fixed     F with values in {yes, no}, yes different from no,
                      computed by a host program T: some program e has
                      ax_dg_equiv e (F e);
      ax_dg_obs_sm2   ax_dg_obs implies sm2_obs, so this is stronger than
                      the recursion theorem with record;
      ax_dg_obs_hagree  and hagree implies ax_dg_obs: the relation sits
                      between what a program can read (level 1) and the six
                      numbers of the recursion theorem (level 2);
      ax_dg_diagonal_record, ax_dg_diagonal_threshold
                      the diagonal for every reading that is a function of
                      the final state up to ax_dg_obs: no Boolean function d on
                      programs whose flip a host program computes is correct
                      for a property that respects behaving alike. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Undecidability.Shared.Libs.DLW.Vec Require Import pos vec.
From Undecidability.Shared.Libs.DLW.Code Require Import subcode sss.
From Undecidability.MinskyMachines Require Import MM MMA.
From Undecidability.MinskyMachines.MMA Require Import mma_defs.
From Undecidability.L Require Import Tactics.LTactics Datatypes.LNat Datatypes.LOptions
  Datatypes.LProd Datatypes.Lists Datatypes.LBool.
From Undecidability.MinskyMachines.Reductions Require Import L_computable_to_MMA_computable.
From Undecidability.Synthetic Require Import Undecidability.
Require Minimal.EarnedMulti Minimal.UniversalCodes.
Require Import Minimal.SmHostBlocks Minimal.SmCodes Minimal.SmInterp Kernel.SmEvalL Kernel.SmFuel
  Kernel.SmMMAHost Kernel.SmNoExact Kernel.SmHostRice Kernel.SmKleene Kernel.SmFixedPoint.
From Kernel Require Import AxCore AxRice AxDgLoops AxDgPre AxDgPhase.
From Minimal Require Import AxDgBlock.
Module M := Minimal.EarnedMulti.
Module UC := Minimal.UniversalCodes.
Unset Implicit Arguments.

Local Notation hinstr := (@M.instr UC.hprop).
Local Notation hcore := (@M.core UC.hprop).
Local Notation hstate := (@M.state UC.hprop).
Local Notation hstep := (M.step UC.hprop_eqb UC.heval).
Local Notation hrun_prog := (M.run_prog UC.hprop_eqb UC.heval).
Local Notation hends := (sm_hends UC.hprop_eqb UC.heval).
Local Notation hfun := (sm_hfun UC.hprop_eqb UC.heval).

(** * 1. The relation: everything readable, with the versions of the facts forgotten *)

Definition ax_dg_obs (s t : hstate) : Prop :=
  (forall r, M.vals (M.core_of s) r = M.vals (M.core_of t) r) /\
  map ax_dg_blind (M.facts (M.core_of s)) = map ax_dg_blind (M.facts (M.core_of t)) /\
  option_map ax_dg_blind (M.chan (M.core_of s)) = option_map ax_dg_blind (M.chan (M.core_of t)) /\
  M.err (M.core_of s) = M.err (M.core_of t) /\
  M.mu s = M.mu t /\ M.cert s = M.cert t.

Definition ax_dg_equiv (P Q : list hinstr) : Prop :=
  forall x,
    (forall s, hends P x s -> exists t, hends Q x t /\ ax_dg_obs s t) /\
    (forall t, hends Q x t -> exists s, hends P x s /\ ax_dg_obs s t).

Lemma ax_dg_obs_sym : forall s t, ax_dg_obs s t -> ax_dg_obs t s.
Proof.
  intros s t (Hv & Hf & Hc & He & Hm & Hk). repeat split; try (intro r; symmetry; apply Hv); auto.
Qed.

Lemma ax_dg_equiv_sym : forall P Q, ax_dg_equiv P Q -> ax_dg_equiv Q P.
Proof.
  intros P Q H x. destruct (H x) as [H1 H2]. split.
  - intros t Ht. destruct (H2 t Ht) as [s [Hs Ho]]. exists s. split; [exact Hs | apply ax_dg_obs_sym; exact Ho].
  - intros s Hs. destruct (H1 s Hs) as [t [Ht Ho]]. exists t. split; [exact Ht | apply ax_dg_obs_sym; exact Ho].
Qed.

(** The relation is finer than the six numbers of the recursion theorem with
    record, and coarser than everything a program can read. *)
Lemma ax_dg_obs_sm2 : forall s t, ax_dg_obs s t -> sm2_obs s t.
Proof.
  intros s t (Hv & Hf & Hc & He & Hm & Hk). unfold sm2_obs. repeat split.
  - apply Hv.
  - exact He.
  - exact Hm.
  - exact Hk.
  - rewrite <- (map_length ax_dg_blind), Hf, map_length. reflexivity.
  - intro H. destruct (M.chan (M.core_of t)) as [b |] eqn:E; [| reflexivity].
    rewrite H in Hc. simpl in Hc. discriminate.
  - intro H. destruct (M.chan (M.core_of s)) as [a |] eqn:E; [| reflexivity].
    rewrite H in Hc. simpl in Hc. discriminate.
Qed.

Lemma ax_dg_obs_hagree : forall s t, sm_hagree s t -> ax_dg_obs s t.
Proof.
  intros s t (Hv & Hf & Hc & He & Hm & Hk). unfold ax_dg_obs. repeat split; auto.
  - rewrite Hf. reflexivity.
  - rewrite Hc. reflexivity.
Qed.

(** * 2. The bit as an MMA program *)

(** Fuel search for: run the program numbered (fst d) on the number of the
    program the s-m-n loader builds from c, and compare the answer with
    (snd d). *)
Definition ax_dg_fb (d : nat * nat) (fuel x c : nat) : option nat :=
  match sm_uev fuel (sm_kspec c) (fst d) with
  | Some y => Some (if Nat.eqb y (snd d) then 1 else 0)
  | None => None
  end.

Instance term_ax_dg_fb : computable ax_dg_fb. Proof. extract. Qed.

Lemma ax_dg_fb_mono : forall d n n' x c m,
  ax_dg_fb d n x c = Some m -> n <= n' -> ax_dg_fb d n' x c = Some m.
Proof.
  intros d n n' x c m H Hle. unfold ax_dg_fb in *.
  destruct (sm_uev n (sm_kspec c) (fst d)) as [y |] eqn:E; [| discriminate].
  rewrite (sm_uev_mono n n' _ _ Hle y E). exact H.
Qed.

Definition ax_dg_Rb (d : nat * nat) (v : Vector.t nat 2) (m : nat) : Prop :=
  exists n, ax_dg_fb d n (Vector.hd v) (Vector.hd (Vector.tl v)) = Some m.

Theorem ax_dg_Rb_MMA : forall d, MMA_computable (ax_dg_Rb d).
Proof.
  intro d. apply L_computable_to_MMA_computable.
  exact (@sm_L_computable_fuel2 (nat * nat) _ ax_dg_fb _ d (fun n n' x c m H Hle => ax_dg_fb_mono d n n' x c m H Hle)).
Qed.

Print Assumptions ax_dg_Rb_MMA.

(** * 3. Entering a block from a clean state *)

(** A clean state at the first line of the block Y, with x in register 1: the
    standalone start of Y on x and this state are related by the shift that
    is the version of every register in this state. *)
Lemma ax_dg_enter : forall (V Y : list hinstr) off s_e x,
  sm_embeds V Y off ->
  (M.fetch V (S (length Y + off)) = None \/ M.fetch V (S (length Y + off)) = Some M.HALT) ->
  ax_dg_clean s_e (S off) (sm_hin x) ->
  forall m, ax_dg_srel (M.vers (M.core_of s_e)) off (length Y)
              (hrun_prog m Y (sm_hstart x)) (hrun_prog m V s_e).
Proof.
  intros V Y off s_e x Hemb Hex Hs m.
  destruct Hs as (He & Hp & Hv & Hf & Hc & Hm & Hk).
  apply (ax_dg_block_run (M.vers (M.core_of s_e)) V Y off Hemb Hex m).
  unfold ax_dg_srel, ax_dg_crel. cbn [sm_hstart M.start M.start_core M.core_of M.mu M.cert M.vers M.vals
    M.facts M.chan M.err M.pc].
  refine (conj (conj _ (conj _ (conj _ (conj _ (conj _ _))))) (conj _ _)).
  - intro r. symmetry. exact (Hv r).
  - intro r. reflexivity.
  - rewrite Hf. reflexivity.
  - rewrite Hc. reflexivity.
  - symmetry. exact He.
  - rewrite Hp, ax_dg_rj_one. reflexivity.
  - symmetry. exact Hm.
  - symmetry. exact Hk.
Qed.

(** * 4. The program e agrees with the block it enters *)


Lemma ax_dg_assemble : forall c0 (V Y : list hinstr) off x n_e,
  sm_embeds V Y off ->
  (M.fetch V (S (length Y + off)) = None \/ M.fetch V (S (length Y + off)) = Some M.HALT) ->
  ax_dg_clean (hrun_prog n_e V (sm_at1 (sm_spec_s1 c0 V x))) (S off) (sm_hin x) ->
  (forall s, hends (sm_spec c0 V) x s -> exists t, hends Y x t /\ ax_dg_obs s t) /\
  (forall t, hends Y x t -> exists s, hends (sm_spec c0 V) x s /\ ax_dg_obs s t).
Proof.
  intros c0 V Y off x n_e Hemb Hex Hclean.
  set (S1 := sm_at1 (sm_spec_s1 c0 V x)) in *.
  set (se := hrun_prog n_e V S1) in *.
  destruct (sm2_spec_ends c0 V x) as [Hfwd Hbwd].
  fold S1 in Hfwd, Hbwd.
  assert (Henter := ax_dg_enter V Y off se x Hemb Hex Hclean).
  (* the observation between the final state of e, the state of V, and the final state of Y *)
  assert (Hobs : forall k s, sm_srel (fun _ => True) c0 (length V) (hrun_prog (n_e + k) V S1) s ->
            ax_dg_obs s (hrun_prog k Y (sm_hstart x))).
  { intros k s Hsr.
    assert (Hr : hrun_prog (n_e + k) V S1 = hrun_prog k V se) by (subst se; apply (sm_run_add UC.hprop_eqb UC.heval)).
    rewrite Hr in Hsr.
    pose proof (Henter k) as Hy.
    destruct Hsr as ((Hv1 & _ & Hf1 & Hc1 & He1 & _) & Hm1 & Hk1).
    destruct Hy as (Hy1 & Hm2 & Hk2).
    pose proof Hy1 as (Hv2 & _ & _ & _ & He2 & _).
    unfold ax_dg_obs. refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
    - intro r. rewrite <- Hv1. symmetry. exact (Hv2 r).
    - rewrite <- Hf1. exact (ax_dg_blind_facts _ _ _ _ _ Hy1).
    - rewrite <- Hc1. exact (ax_dg_blind_chan _ _ _ _ _ Hy1).
    - rewrite <- He1. symmetry. exact He2.
    - rewrite <- Hm1. symmetry. exact Hm2.
    - rewrite <- Hk1. symmetry. exact Hk2. }
  split.
  - intros s Hs. destruct (Hfwd s Hs) as (n & Hh & Hsr).
    (* a stop before the entry stays a stop at the entry *)
    assert (Hn : exists k, n_e + k = n \/ (n < n_e /\ k = 0 /\ hrun_prog n_e V S1 = hrun_prog n V S1)).
    { destruct (le_lt_dec n_e n) as [H | H].
      - exists (n - n_e). left. lia.
      - exists 0. right. split; [exact H |]. split; [reflexivity |].
        apply (sm_halted_after UC.hprop_eqb UC.heval n n_e V S1); [lia | exact Hh]. }
    destruct Hn as [k [Hk | (Hlt & Hk0 & Hrun)]].
    + subst n. exists (hrun_prog k Y (sm_hstart x)). split.
      * exists k. split; [reflexivity |].
        destruct (M.next_instr Y (M.core_of (hrun_prog k Y (sm_hstart x)))) eqn:Hn; [| exact Hn].
        exfalso. assert (Hr : hrun_prog (n_e + k) V S1 = hrun_prog k V se) by (subst se; apply (sm_run_add UC.hprop_eqb UC.heval)).
        rewrite Hr in Hh.
        pose proof (ax_dg_block_go _ V Y off _ _ Hemb (Henter k)) as Hgo.
        apply Hgo; [congruence |]. exact Hh.
      * apply (Hobs k s Hsr).
    + subst k. exists (hrun_prog 0 Y (sm_hstart x)). split.
      * exists 0. split; [reflexivity |].
        destruct (M.next_instr Y (M.core_of (hrun_prog 0 Y (sm_hstart x)))) eqn:Hn; [| exact Hn].
        exfalso. pose proof (ax_dg_block_go _ V Y off _ _ Hemb (Henter 0)) as Hgo.
        apply Hgo; [congruence |].
        assert (Hh' : M.halted V (M.core_of (hrun_prog n_e V S1))) by (rewrite Hrun; exact Hh).
        exact Hh'.
      * apply (Hobs 0 s). rewrite Nat.add_0_r. rewrite Hrun. exact Hsr.
  - intros t [k [-> Hht]]. 
    assert (Hhalt : M.halted V (M.core_of (hrun_prog (n_e + k) V S1))).
    { rewrite (sm_run_add UC.hprop_eqb UC.heval n_e k V S1). fold se.
      pose proof (Henter k) as Hy. destruct Hy as (Hy1 & _).
      exact (ax_dg_block_stop _ V Y off _ _ Hemb Hex Hy1 Hht). }
    destruct (Hbwd (n_e + k) Hhalt) as (s & Hs & Hsr).
    exists s. split; [exact Hs |]. apply (Hobs k s Hsr).
Qed.

(** * 5. The fixed point *)

Theorem ax_dg_fixed : forall (yes no T : list hinstr) (F : list hinstr -> list hinstr),
  yes <> no -> (forall p, F p = yes \/ F p = no) -> sm_computes_map T F ->
  exists e, ax_dg_equiv e (F e).
Proof.
  intros yes no T F Hyn HF HT.
  destruct (ax_dg_Rb_MMA (sm_hcode T, sm_hcode yes)) as [nn [Pm HPm]].
  set (V := ax_dg_V nn Pm yes no).
  set (c0 := sm_hcode V).
  set (e := sm_spec c0 V).
  assert (Hcode : sm_kspec c0 = sm_hcode e).
  { unfold e, c0. rewrite sm_kspec_code, sm_hdecode_hcode. reflexivity. }
  exists e. intro x.
  set (bit := if Nat.eqb (sm_hcode (F e)) (sm_hcode yes) then 1 else 0).
  assert (Hbit : bit = 0 \/ bit = 1) by (unfold bit; destruct (Nat.eqb _ _); auto).
  assert (Hb : exists n, ax_dg_fb (sm_hcode T, sm_hcode yes) n 0 c0 = Some bit).
  { destruct (proj2 (sm_uev_spec (sm_hcode e) (sm_hcode T) (sm_hcode (F e)))) as [n Hn].
    { rewrite sm_hdecode_hcode. exact (HT e). }
    exists n. unfold ax_dg_fb. cbn [fst snd]. rewrite Hcode, Hn. reflexivity. }
  assert (Hout : exists c' (v' : Vector.t nat (2 + nn)),
            sss_output (@mma_sss (S (S (S nn)))) (1, Pm) (1, ax_dg_vec nn c0)
              (c', Vector.cons nat bit (2 + nn) v')).
  { apply (proj1 (HPm (Vector.cons nat 0 1 (Vector.cons nat c0 0 (Vector.nil nat))) bit)).
    exact Hb. }
  set (S1 := sm_at1 (sm_spec_s1 c0 V x)).
  assert (HS1 : ax_dg_clean S1 1 (sm_in2 x c0)).
  { destruct (sm_spec_phase1 c0 V x) as (Hv & _ & Hf & Hc & He & Hp & Hm & Hk).
    unfold S1, sm_at1, M.goto, ax_dg_clean. cbn [M.core_of M.pc M.vals M.facts M.chan M.err M.mu M.cert].
    repeat split; auto. }
  destruct (ax_dg_prelude nn Pm yes no c0 x bit S1 Hbit Hout HS1) as [ne Hne].
  destruct (HF e) as [HFy | HFn].
  - assert (Hb1 : bit = 1) by (unfold bit; rewrite HFy, Nat.eqb_refl; reflexivity).
    rewrite Hb1 in Hne. cbn [Nat.eqb] in Hne. rewrite HFy.
    exact (ax_dg_assemble c0 V yes (ax_dg_offY nn Pm no) x ne
             (ax_dg_embeds_yes nn Pm yes no) (or_introl (ax_dg_exit_yes nn Pm yes no)) Hne).
  - assert (Hb0 : bit = 0).
    { unfold bit. rewrite HFn.
      destruct (Nat.eqb_spec (sm_hcode no) (sm_hcode yes)) as [E | E]; [| reflexivity].
      exfalso. apply Hyn. symmetry. exact (sm_hcode_inj _ _ E). }
    rewrite Hb0 in Hne. cbn [Nat.eqb] in Hne. rewrite HFn.
    exact (ax_dg_assemble c0 V no (ax_dg_offN nn Pm) x ne
             (ax_dg_embeds_no nn Pm yes no) (or_intror (ax_dg_exit_no nn Pm yes no)) Hne).
Qed.

Print Assumptions ax_dg_fixed.

(** * 6. The diagonal for readings that see the claims *)

Section DiagonalReadings.

Variable A : Type.
Variable P : BPre A.
Variable rd : hstate -> A.

(** A reading is a function of the final state up to ax_dg_obs: the registers,
    the claims, the channel claim, the trap, the ledger and the flag. *)
Definition ax_reads_dg : Prop :=
  forall s t, ax_dg_obs s t -> @ax_req A P (rd s) (rd t).

Lemma ax_dg_equiv_record : ax_reads_dg -> forall p q,
  ax_dg_equiv p q -> @ax_record_equiv A P rd p q.
Proof.
  intros Hr p q H x. destruct (H x) as [H1 H2]. split.
  - intros s Hs. destruct (H1 s Hs) as [t [Ht Ho]]. exists t. split; [exact Ht | apply Hr; exact Ho].
  - intros t Ht. destruct (H2 t Ht) as [s [Hs Ho]]. exists s. split; [exact Hs | apply Hr; exact Ho].
Qed.

(** Level 2 readings, and the readings of AxRice.v that see everything. *)
Lemma ax_dg_reads_of_obs : @ax_reads_obs A P rd -> ax_reads_dg.
Proof. intros H s t Ho. apply H. apply ax_dg_obs_sm2. exact Ho. Qed.

Lemma ax_dg_reads_hagree : ax_reads_dg -> @ax_reads_hagree A P rd.
Proof. intros H s t Ha. apply H. apply ax_dg_obs_hagree. exact Ha. Qed.

Theorem ax_dg_diagonal_record : ax_reads_dg -> forall (Pi : list hinstr -> Prop) yes no,
  (forall p q, @ax_record_equiv A P rd p q -> Pi p -> Pi q) ->
  Pi yes -> ~ Pi no ->
  forall d : list hinstr -> bool,
  (exists T, sm_computes_map T (fun p => if d p then no else yes)) ->
  ~ (forall p, d p = true <-> Pi p).
Proof.
  intros Hr Pi yes no Hext Hy Hn d [T HT] Hd.
  assert (Hyn : yes <> no) by (intro E; subst; exact (Hn Hy)).
  assert (HF : forall p, (if d p then no else yes) = yes \/ (if d p then no else yes) = no)
    by (intro p; destruct (d p); [right | left]; reflexivity).
  destruct (ax_dg_fixed yes no T (fun p => if d p then no else yes) Hyn HF HT) as [e He].
  pose proof (ax_dg_equiv_record Hr e _ He) as Hre. simpl in Hre.
  destruct (d e) eqn:Hde.
  - apply Hn. apply (Hext e no); [exact Hre | apply Hd, Hde].
  - assert (HPe : Pi e).
    { apply (Hext yes e); [| exact Hy]. apply (@ax_record_equiv_sym A P rd). exact Hre. }
    apply Hd in HPe. congruence.
Qed.

Theorem ax_dg_diagonal_threshold : ax_reads_dg -> forall a (Pi : list hinstr -> Prop) yes no,
  (forall p q, @ax_reach_equiv A P rd a p q -> Pi p -> Pi q) ->
  Pi yes -> ~ Pi no ->
  forall d : list hinstr -> bool,
  (exists T, sm_computes_map T (fun p => if d p then no else yes)) ->
  ~ (forall p, d p = true <-> Pi p).
Proof.
  intros Hr a Pi yes no Hext Hy Hn d HT.
  apply (ax_dg_diagonal_record Hr Pi yes no); [| exact Hy | exact Hn | exact HT].
  intros p q Hpq HP. apply (Hext p q); [| exact HP].
  apply @ax_record_equiv_reach. exact Hpq.
Qed.

End DiagonalReadings.

Print Assumptions ax_dg_diagonal_record.
Print Assumptions ax_dg_diagonal_threshold.

(** * 7. The claims axis: which claim is in the table *)

Definition ax_dg_claim : Type := (UC.hprop * nat)%type.

Definition ax_dg_ceqb (a b : ax_dg_claim) : bool :=
  UC.hprop_eqb (fst a) (fst b) && Nat.eqb (snd a) (snd b).

Lemma ax_dg_ceqb_spec : forall a b, ax_dg_ceqb a b = true <-> a = b.
Proof.
  intros [p r] [q s]. unfold ax_dg_ceqb. simpl. rewrite andb_true_iff, UC.hprop_eqb_eq, Nat.eqb_eq.
  split; [intros [-> ->]; reflexivity | intro H; split; congruence].
Qed.

(** Inclusion of claim lists, as a Boolean preorder. *)
Definition ax_dg_incl (xs ys : list ax_dg_claim) : bool :=
  forallb (fun a => existsb (ax_dg_ceqb a) ys) xs.

Lemma ax_dg_incl_spec : forall xs ys,
  ax_dg_incl xs ys = true <-> forall a, In a xs -> In a ys.
Proof.
  intros xs ys. unfold ax_dg_incl. rewrite forallb_forall. split.
  - intros H a Ha. specialize (H a Ha). apply existsb_exists in H.
    destruct H as [b [Hb Hab]]. apply ax_dg_ceqb_spec in Hab. subst. exact Hb.
  - intros H a Ha. apply existsb_exists. exists a. split; [apply H, Ha |].
    apply ax_dg_ceqb_spec. reflexivity.
Qed.

Definition ax_dg_claim_pre : BPre (list ax_dg_claim).
Proof.
  refine {| bp_leb := ax_dg_incl |}.
  - intro x. apply ax_dg_incl_spec. auto.
  - intros x y z H1 H2.
    pose proof (proj1 (ax_dg_incl_spec _ _) H1) as H1'.
    pose proof (proj1 (ax_dg_incl_spec _ _) H2) as H2'.
    apply (proj2 (ax_dg_incl_spec _ _)). auto.
Defined.

(** The reading: the claims of the fact table, in order. *)
Definition ax_dg_claims (s : hstate) : list ax_dg_claim := map ax_dg_blind (M.facts (M.core_of s)).

Lemma ax_dg_claims_reads : ax_reads_dg _ ax_dg_claim_pre ax_dg_claims.
Proof.
  intros s t (_ & Hf & _). unfold ax_dg_claims. rewrite Hf. split; apply bp_le_refl.
Qed.

(** The claims are not a level 2 reading: two states with the same six numbers
    and different claims. *)
Lemma ax_dg_claims_not_level2 : ~ @ax_reads_obs _ ax_dg_claim_pre ax_dg_claims.
Proof.
  intro H.
  set (sA := M.mkst (M.mkcore (fun _ => 0) (fun _ => 0) 1 [M.mkfact UC.PSlot 5 1] None false) 0 false : hstate).
  set (sB := M.mkst (M.mkcore (fun _ => 0) (fun _ => 0) 1 [M.mkfact UC.PSlot 6 1] None false) 0 false : hstate).
  assert (Ho : sm2_obs sA sB).
  { unfold sm2_obs, sA, sB. cbn. repeat split; reflexivity. }
  destruct (H sA sB Ho) as [H1 _]. unfold bp_le in H1. simpl in H1.
  unfold ax_dg_claims, sA, sB in H1. cbn in H1. vm_compute in H1. discriminate.
Qed.

(** The point: this claim is in the table. *)
Definition ax_dg_pt (r : nat) : list ax_dg_claim := [(UC.PSlot, r)].

Lemma ax_dg_pt_floor : forall r x,
  ax_reach ax_dg_claim_pre ax_dg_claims (ax_dg_pt r) (@sm_hstart UC.hprop x) = false.
Proof. intros r x. reflexivity. Qed.

(** A program that reaches it. *)
Definition ax_dg_pclaim (r : nat) : list hinstr := [M.INC r; M.CHECK UC.PSlot r; M.HALT].

Lemma ax_dg_step_check : forall Q s r pc v,
  ax_dg_clean s pc v -> M.fetch Q pc = Some (M.CHECK UC.PSlot r) ->
  UC.heval UC.PSlot (v r) = true ->
  M.facts (M.core_of (hstep Q s)) = [M.mkfact UC.PSlot r (M.vers (M.core_of s) r)] /\
  M.err (M.core_of (hstep Q s)) = false /\ M.pc (M.core_of (hstep Q s)) = S pc.
Proof.
  intros Q s r pc v (He & Hp & Hv & Hf & Hc & Hm & Hk) Hfe Hev.
  assert (Hn : M.next_instr Q (M.core_of s) = Some (M.CHECK UC.PSlot r))
    by (apply sm_next_intro; [exact He | rewrite Hp; exact Hfe | discriminate]).
  assert (Hok : M.check_ok UC.heval (M.core_of s) UC.PSlot r = true).
  { unfold M.check_ok. rewrite He, Hv, Hf. simpl. rewrite Hev. reflexivity. }
  unfold M.step. rewrite Hn. unfold M.exec, M.cexec. rewrite He. simpl.
  rewrite Hok. unfold M.record_fact, M.claim. simpl. rewrite Hf, Hp. repeat split; auto.
Qed.

Lemma ax_dg_pclaim_ends : forall r, exists s, hends (ax_dg_pclaim r) 0 s /\
  M.facts (M.core_of s) = [M.mkfact UC.PSlot r 1].
Proof.
  intro r.
  set (P := ax_dg_pclaim r).
  assert (S0 : ax_dg_clean (@sm_hstart UC.hprop 0) 1 (sm_hin 0)).
  { repeat split; reflexivity. }
  assert (F1 : M.fetch P 1 = Some (M.INC r)) by reflexivity.
  assert (F2 : M.fetch P 2 = Some (M.CHECK UC.PSlot r)) by reflexivity.
  assert (F3 : M.fetch P 3 = Some M.HALT) by reflexivity.
  set (s1 := hstep P (sm_hstart 0)).
  assert (S1 : ax_dg_clean s1 2 (M.upd (sm_hin 0) r (S (sm_hin 0 r)))).
  { exact (ax_dg_step_inc P _ r 1 _ S0 F1). }
  assert (Hver : M.vers (M.core_of s1) r = 1).
  { unfold s1, M.step.
    assert (Hn : M.next_instr P (M.core_of (sm_hstart 0)) = Some (M.INC r))
      by (apply sm_next_intro; [reflexivity | exact F1 | discriminate]).
    rewrite Hn. cbn [M.exec M.core_of]. unfold M.cexec.
    cbn [M.err M.core_of sm_hstart M.start M.start_core].
    rewrite M.multi_ver_write, Nat.eqb_refl. reflexivity. }
  assert (Hev : UC.heval UC.PSlot (M.upd (sm_hin 0) r (S (sm_hin 0 r)) r) = true).
  { unfold M.upd. rewrite Nat.eqb_refl. unfold sm_hin. destruct (Nat.eqb r 1); reflexivity. }
  destruct (ax_dg_step_check P _ r 2 _ S1 F2 Hev) as (Hf & He & Hp).
  exists (hstep P s1). split.
  - exists 2. split; [reflexivity |].
    unfold M.halted, M.next_instr. rewrite He, Hp, F3. reflexivity.
  - rewrite Hf, Hver. reflexivity.
Qed.

Lemma ax_dg_pclaim_reaches : forall r,
  ax_reaches ax_dg_claim_pre ax_dg_claims (ax_dg_pt r) (ax_dg_pclaim r).
Proof.
  intro r. destruct (ax_dg_pclaim_ends r) as [s [Hs Hf]].
  exists 0, s. split; [exact Hs |].
  unfold ax_reach, ax_dg_claims. rewrite Hf. vm_compute.
  destruct (UC.hprop_eqb UC.PSlot UC.PSlot) eqn:E; [| exfalso; rewrite (proj2 (UC.hprop_eqb_eq _ _) eq_refl) in E; discriminate].
  rewrite Nat.eqb_refl. reflexivity.
Qed.

(** The program that stops at once reaches no point but the floor. *)
Lemma ax_dg_halt_floor : forall r x s,
  hends [M.HALT] x s -> ax_reach ax_dg_claim_pre ax_dg_claims (ax_dg_pt r) s = false.
Proof.
  intros r x s [n [-> Hh]].
  assert (Hn : forall m, hrun_prog m [M.HALT] (@sm_hstart UC.hprop x) = @sm_hstart UC.hprop x).
  { induction m as [| m IH]; [reflexivity |]. simpl. rewrite <- IH at 2. reflexivity. }
  rewrite Hn. reflexivity.
Qed.

Theorem ax_dg_claim_undecidable : forall r,
  undecidable (ax_reaches ax_dg_claim_pre ax_dg_claims (ax_dg_pt r)).
Proof.
  intro r.
  apply (@ax_reach_undecidable _ ax_dg_claim_pre ax_dg_claims
           (ax_dg_reads_hagree _ _ _ ax_dg_claims_reads) (ax_dg_pt r) (ax_dg_pclaim r)
           (ax_dg_pclaim_reaches r) (ax_dg_pt_floor r)).
Qed.

Theorem ax_dg_claim_diagonal : forall r (d : list hinstr -> bool),
  (exists T, sm_computes_map T (fun p => if d p then [M.HALT] else ax_dg_pclaim r)) ->
  ~ (forall p, d p = true <-> ax_reaches ax_dg_claim_pre ax_dg_claims (ax_dg_pt r) p).
Proof.
  intros r d HT.
  apply (ax_dg_diagonal_threshold _ ax_dg_claim_pre ax_dg_claims ax_dg_claims_reads (ax_dg_pt r)
           (ax_reaches ax_dg_claim_pre ax_dg_claims (ax_dg_pt r)) (ax_dg_pclaim r) [M.HALT]).
  - intros p q Hpq Hp. exact (@ax_reaches_ext _ ax_dg_claim_pre ax_dg_claims (ax_dg_pt r) p q Hpq Hp).
  - exact (ax_dg_pclaim_reaches r).
  - intros [x [s [Hs Hr]]]. rewrite (ax_dg_halt_floor r x s Hs) in Hr. discriminate.
  - exact HT.
Qed.

Print Assumptions ax_dg_claims_not_level2.
Print Assumptions ax_dg_claim_undecidable.
Print Assumptions ax_dg_claim_diagonal.
