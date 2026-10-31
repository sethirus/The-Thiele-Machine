(** SmSmnAll.v: s-m-n for every host program.

    SmKleene.v proves [sm_smn] for programs whose CHECK and COMMIT never
    name register 2, because the specialising prefix c copies of INC 2 moves
    the version of register 2 from 0 to c, and a fact records a version.
    That restriction is not needed. Version c at the start of register 2
    shifts every later version of register 2 by c, in the run and in the
    facts the run records, and a CHECK or a COMMIT depends on versions only
    through equality of two versions of the same register.

    [sm2_wrel c k k'] relates the core k of the run after the prefix and
    the core k' of the clean run: same values, same program counter, same
    trap latch, versions of register 2 shifted by c, and facts and channel
    shifted by c on register 2. It is kept by every step.

    [sm2_smn_all]: for every host program V, every c, x and y, the program
    sm_spec c V computes y from x exactly when V, started with x in register
    1 and c in register 2, stops with y in register 0.

    Dependencies: as SmKleene.v, and SmLoops.v. No axioms and no unfinished proofs. *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is recursion theory on the host machine, here the s-m-n theorem on the host machine of EarnedMulti.v without a premise on register 2.
   The host machine's link to the abstract record (a CertificationSystem
   with the trace floor, a Thiele-complete machine, and the halting problem
   of U) lives in UniversalInterpreterLinks.v. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Minimal.EarnedMulti Minimal.UniversalCodes.
Require Import Minimal.SmHostBlocks Kernel.SmHostRice Minimal.SmCodes Minimal.SmInterp Kernel.SmKleene Minimal.SmLoops.
Module M := Minimal.EarnedMulti.
Module UC := Minimal.UniversalCodes.
Unset Implicit Arguments.

Local Notation hinstr := (@M.instr UC.hprop).
Local Notation hcore := (@M.core UC.hprop).
Local Notation hfact := (@M.fact UC.hprop).
Local Notation hstate := (@M.state UC.hprop).
Local Notation hstep := (M.step UC.hprop_eqb UC.heval).
Local Notation hrun_prog := (M.run_prog UC.hprop_eqb UC.heval).
Local Notation hcstep := (sm_cstep UC.hprop_eqb UC.heval).
Local Notation hfun := (sm_hfun UC.hprop_eqb UC.heval).

Definition sm2_delta (c r : nat) : nat := if Nat.eqb r 2 then c else 0.

Definition sm2_shf (c : nat) (f : hfact) : hfact :=
  M.mkfact (M.f_prop f) (M.f_reg f) (M.f_ver f + sm2_delta c (M.f_reg f)).

Definition sm2_wrel (c : nat) (k k' : hcore) : Prop :=
  (forall r, M.vals k r = M.vals k' r) /\
  (forall r, M.vers k r = M.vers k' r + sm2_delta c r) /\
  M.pc k = M.pc k' /\ M.facts k = map (sm2_shf c) (M.facts k') /\
  M.chan k = option_map (sm2_shf c) (M.chan k') /\ M.err k = M.err k'.

Lemma sm2_shf_inj : forall c (f g : hfact), sm2_shf c f = sm2_shf c g -> f = g.
Proof.
  intros c [p r v] [q s w] H. unfold sm2_shf in H. simpl in H. injection H as Hr Hv.
  subst s. destruct p, q. f_equal. lia.
Qed.

Lemma sm2_existsb_shf : forall c (a : hfact) (l : list hfact),
  existsb (M.fact_eqb UC.hprop_eqb (sm2_shf c a)) (map (sm2_shf c) l) =
  existsb (M.fact_eqb UC.hprop_eqb a) l.
Proof.
  intros c a l. induction l as [| g l IH]; [reflexivity |].
  simpl. rewrite IH. f_equal.
  apply Bool.eq_iff_eq_true. rewrite !(M.multi_fact_eqb_eq UC.hprop_eqb UC.hprop_eqb_eq).
  split; [apply sm2_shf_inj | intros ->; reflexivity].
Qed.

Lemma sm2_wrel_step : forall c (V : list hinstr) k k', sm2_wrel c k k' ->
  sm2_wrel c (hcstep V k) (hcstep V k').
Proof.
  intros c V k k' Hrel. pose proof Hrel as (Hv & Hw & Hp & Hf & Hch & He).
  assert (Hn : M.next_instr V k = M.next_instr V k') by (unfold M.next_instr; rewrite He, Hp; reflexivity).
  unfold sm_cstep. rewrite <- Hn.
  destruct (M.next_instr V k) as [i |] eqn:Hi; [| exact Hrel].
  destruct (sm_next_some V k i Hi) as (Ek & Hfe & _).
  assert (Ek' : M.err k' = false) by congruence.
  unfold M.cexec. rewrite Ek, Ek'.
  destruct i as [r | r j | | p r | p r |]; cbv beta iota.
  - unfold sm2_wrel. refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
    + intro q. rewrite !M.multi_val_write. rewrite (Hv r), (Hv q). reflexivity.
    + intro q. rewrite !M.multi_ver_write. rewrite (Hw q). destruct (Nat.eqb r q) eqn:E; [| reflexivity].
      apply Nat.eqb_eq in E. subst q. lia.
    + simpl. congruence.
    + simpl. exact Hf.
    + simpl. exact Hch.
    + simpl. exact He.
  - rewrite <- (Hv r). destruct (M.vals k r) as [| v].
    + unfold sm2_wrel. simpl. refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
      * exact Hv.
      * exact Hw.
      * congruence.
      * exact Hf.
      * exact Hch.
      * exact He.
    + unfold sm2_wrel. refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
      * intro q. rewrite !M.multi_val_write. destruct (Nat.eqb r q); [reflexivity | apply Hv].
      * intro q. rewrite !M.multi_ver_write. rewrite (Hw q). destruct (Nat.eqb r q) eqn:E; [| reflexivity].
        apply Nat.eqb_eq in E. subst q. lia.
      * reflexivity.
      * simpl. exact Hf.
      * simpl. exact Hch.
      * simpl. exact He.
  - exact Hrel.
  - assert (Hok : M.check_ok UC.heval k p r = M.check_ok UC.heval k' p r).
    { unfold M.check_ok. rewrite Ek, Ek', (Hv r), Hf, map_length. reflexivity. }
    rewrite Hok. destruct (M.check_ok UC.heval k' p r).
    + unfold sm2_wrel, M.record_fact, M.claim. simpl.
      refine (conj Hv (conj Hw (conj _ (conj _ (conj Hch He))))).
      * congruence.
      * rewrite Hf. simpl. f_equal. unfold sm2_shf. simpl. f_equal. rewrite (Hw r). reflexivity.
    + unfold sm2_wrel, M.trap. simpl. exact (conj Hv (conj Hw (conj Hp (conj Hf (conj Hch eq_refl))))).
  - assert (Hcl : M.claim k p r = sm2_shf c (M.claim k' p r)).
    { unfold M.claim, sm2_shf. simpl. rewrite (Hw r). reflexivity. }
    assert (Hok : M.commit_ok UC.hprop_eqb k p r = M.commit_ok UC.hprop_eqb k' p r).
    { unfold M.commit_ok. rewrite Ek, Ek', Hcl, Hf, sm2_existsb_shf. reflexivity. }
    rewrite Hok. destruct (M.commit_ok UC.hprop_eqb k' p r).
    + unfold sm2_wrel, M.commit_to. simpl.
      refine (conj Hv (conj Hw (conj _ (conj Hf (conj _ He))))).
      * congruence.
      * rewrite Hcl. reflexivity.
    + unfold sm2_wrel, M.trap. simpl. exact (conj Hv (conj Hw (conj Hp (conj Hf (conj Hch eq_refl))))).
  - assert (Hok : M.certify_ok k = M.certify_ok k').
    { unfold M.certify_ok. rewrite Ek, Ek', Hch. destruct (M.chan k'); reflexivity. }
    rewrite Hok. destruct (M.certify_ok k').
    + unfold sm2_wrel, M.goto. simpl. refine (conj Hv (conj Hw (conj _ (conj Hf (conj Hch He))))).
      congruence.
    + unfold sm2_wrel, M.trap. simpl. exact (conj Hv (conj Hw (conj Hp (conj Hf (conj Hch eq_refl))))).
Qed.

Lemma sm2_wrel_run : forall c (V : list hinstr) n k k', sm2_wrel c k k' ->
  sm2_wrel c (sm_crun n V k) (sm_crun n V k').
Proof.
  intros c V n. induction n as [| n IH]; intros k k' H; [exact H |].
  simpl. apply IH, sm2_wrel_step, H.
Qed.

Lemma sm2_wrel_halted : forall c (V : list hinstr) k k', sm2_wrel c k k' ->
  M.halted V k -> M.halted V k'.
Proof.
  intros c V k k' (_ & _ & Hp & _ & _ & He) H. unfold M.halted, M.next_instr in *.
  rewrite <- He, <- Hp. exact H.
Qed.

Lemma sm2_wrel_halted' : forall c (V : list hinstr) k k', sm2_wrel c k k' ->
  M.halted V k' -> M.halted V k.
Proof.
  intros c V k k' (_ & _ & Hp & _ & _ & He) H. unfold M.halted, M.next_instr in *.
  rewrite He, Hp. exact H.
Qed.

(* After the prefix, register 2 has version c. *)
Lemma sm2_incs_vers : forall (Q : list hinstr) r c off (s : hstate),
  (forall p, 1 <= p <= c -> M.fetch Q (p + off) = Some (M.INC r)) ->
  M.err (M.core_of s) = false -> M.pc (M.core_of s) = S off ->
  M.vers (M.core_of (hrun_prog c Q s)) r = M.vers (M.core_of s) r + c.
Proof.
  intros Q r c. induction c as [| c IH]; intros off s Hf He Hp; [simpl; lia |].
  assert (Hn : M.next_instr Q (M.core_of s) = Some (M.INC r)).
  { apply sm_next_intro; [exact He | | discriminate]. rewrite Hp. apply (Hf 1). lia. }
  rewrite sm_run_succ.
  assert (Hst : hstep Q s = M.exec UC.hprop_eqb UC.heval s (M.INC r)) by (unfold M.step; rewrite Hn; reflexivity).
  rewrite Hst.
  assert (Hc : M.core_of (M.exec UC.hprop_eqb UC.heval s (M.INC r)) =
               M.write (M.core_of s) r (S (M.vals (M.core_of s) r)) (S (M.pc (M.core_of s)))).
  { unfold M.exec, M.cexec. cbn [M.core_of]. rewrite He. reflexivity. }
  assert (He1 : M.err (M.core_of (M.exec UC.hprop_eqb UC.heval s (M.INC r))) = false)
    by (rewrite Hc; exact He).
  assert (Hp1 : M.pc (M.core_of (M.exec UC.hprop_eqb UC.heval s (M.INC r))) = S (S off))
    by (rewrite Hc; simpl; rewrite Hp; reflexivity).
  rewrite (IH (S off) _ ltac:(intros p Hp'; replace (p + S off) with (S p + off) by lia; apply Hf; lia) He1 Hp1).
  rewrite Hc, M.multi_ver_write, Nat.eqb_refl. lia.
Qed.

Lemma sm2_spec_vers2 : forall c V x,
  M.vers (M.core_of (sm_spec_s1 c V x)) 2 = c.
Proof.
  intros c V x. unfold sm_spec_s1.
  pose proof (sm2_incs_vers (sm_spec c V) 2 c 0 (sm_hstart x)) as H.
  rewrite H.
  - reflexivity.
  - intros p Hp. unfold sm_spec. rewrite Nat.add_0_r.
    rewrite sm_fetch_app_left by (rewrite sm_incs_length; lia).
    destruct p as [| p]; [lia |]. simpl. unfold sm_incs. apply nth_error_repeat. lia.
  - reflexivity.
  - reflexivity.
Qed.

Theorem sm2_smn_all : forall c V x y,
  hfun (sm_spec c V) x y <-> sm_hfun_from V (sm_in2 x c) y.
Proof.
  intros c V x y. rewrite sm_spec_hfun.
  destruct (sm_spec_phase1 c V x) as (Hv1 & Hw1 & Hf1 & Hc1 & He1 & _).
  pose proof (sm2_spec_vers2 c V x) as Hw2.
  assert (Hrel : sm2_wrel c (M.core_of (sm_at1 (sm_spec_s1 c V x))) (M.core_of (M.start (sm_in2 x c)))).
  { unfold sm2_wrel, sm_at1, M.goto. cbn [M.core_of M.vals M.vers M.pc M.facts M.chan M.err M.start M.start_core].
    refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
    - exact Hv1.
    - intro r. unfold sm2_delta. destruct (Nat.eqb_spec r 2) as [-> | Hr].
      + rewrite Hw2. lia.
      + rewrite (Hw1 r Hr). lia.
    - reflexivity.
    - exact Hf1.
    - exact Hc1.
    - exact He1. }
  unfold sm_hfun_from. split.
  - intros [n [Hh Hy]]. exists n.
    rewrite sm_core_run in *.
    pose proof (sm2_wrel_run c V n _ _ Hrel) as Hr.
    split; [exact (sm2_wrel_halted c V _ _ Hr Hh) |].
    destruct Hr as (Hv & _). rewrite <- Hv. exact Hy.
  - intros [n [Hh Hy]]. exists n.
    rewrite sm_core_run in *.
    pose proof (sm2_wrel_run c V n _ _ Hrel) as Hr.
    split; [exact (sm2_wrel_halted' c V _ _ Hr Hh) |].
    destruct Hr as (Hv & _). rewrite Hv. exact Hy.
Qed.

Print Assumptions sm2_smn_all.
