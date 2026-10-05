(** SmKleene.v: Kleene's recursion theorem for programs of the host machine.

    The host machine is EarnedMulti.v with the property PSlot of
    UniversalCodes.v: the machine the universal program U runs on, with a
    counter for every register number and the small machine's six kinds of
    instruction and prices. A program is run on one number x in register 1
    (every other register 0), and it computes y from x (sm_hfun P x y) when
    it stops with y in register 0. Programs have numbers: sm_hcode P, read
    back by sm_hdecode (SmCodes.v).

    What is proved:
      1. s-m-n [sm_smn]. sm_spec c V is c copies of INC 2 followed by V,
         moved down c lines. On x it computes what V computes when started
         with x in register 1 and c in register 2, for every V whose CHECK
         and COMMIT instructions do not name register 2.
      2. A universal program [sm_host_universal]. One fixed host program,
         started with x in register 1 and c in register 2, computes y
         exactly when the program numbered c computes y from x.
      3. The second recursion theorem [sm_second_recursion]. For every host
         program T there is a host program e such that, on every x, e
         computes y exactly when T sends the number of e to some d and the
         program numbered d computes y from x.
      4. Kleene's recursion theorem [sm_kleene]. For every map F from host
         programs to host programs that some host program T computes on
         numbers (T sends sm_hcode p to sm_hcode (F p), for every p), there
         is a program e that computes the same partial function as F e.
         The same with numbers in place of programs: [sm_kleene_codes].
      5. The diagonal, on this machine [sm_no_inside_decider]. Let Pi be a
         property of host programs that depends only on the partial
         function computed, holds of y and fails of n. Then no Boolean
         function d on programs whose flip (n where d says yes, y where it
         says no) some host program computes on numbers is correct for Pi.
         And Rice's theorem for this notion of behaviour
         [sm_host_rice_fun], from SmHostRice.v.

    How e is built. The evaluator sm_ev of SmInterp.v, for the fixed
    number t of T, takes x and c, runs the program numbered t on the number
    of sm_spec c (the program numbered c), and runs the program whose
    number comes out on x. SmFuel.v makes that relation a vendored Minsky
    program, and SmMMAHost.v makes it a host program VG, with x in
    register 1 and c in register 2. Let c0 be the number of VG and
    e = sm_spec c0 VG, which is VG with its own number loaded into
    register 2 (s-m-n). Run on x, e runs VG on x and c0; VG runs T on the
    number of sm_spec c0 VG, which is the number of e itself
    (self-application), and runs what comes out on x.

    The fixed point is a fixed point of the partial function computed
    (register 0 on stopping, and whether the program stops), not of the
    whole final state: e's ledger, flag and other registers are those of
    the evaluator.

    Dependencies: Coq standard library, the vendored coq-undecidability
    library, MetaCoq Template (through SmEvalL.v, for the extraction tactic
    only), EarnedCore.v, EarnedGeneric.v, EarnedMulti.v, UniversalCodes.v,
    SmMM2Compl.v, SmHostBlocks.v, SmHostRice.v, SmCodes.v, SmInterp.v,
    SmEvalL.v, SmFuel.v and SmMMAHost.v. No axioms, no Admitted.           *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Undecidability.Shared.Libs.DLW.Vec Require Import pos vec.
From Undecidability.Shared.Libs.DLW.Code Require Import subcode sss.
From Undecidability.MinskyMachines Require Import MM MMA.
From Undecidability.Synthetic Require Import Undecidability.
Require Minimal.EarnedMulti Minimal.UniversalCodes.
Require Import Sm.SmHostBlocks Sm.SmHostRice Sm.SmCodes Sm.SmInterp Sm.SmFuel Sm.SmMMAHost.
Module M := Minimal.EarnedMulti.
Module UC := Minimal.UniversalCodes.
Unset Implicit Arguments.

Local Notation hinstr := (@M.instr UC.hprop).
Local Notation hcore := (@M.core UC.hprop).
Local Notation hstate := (@M.state UC.hprop).
Local Notation hcexec := (M.cexec UC.hprop_eqb UC.heval).
Local Notation hstep := (M.step UC.hprop_eqb UC.heval).
Local Notation hrun_prog := (M.run_prog UC.hprop_eqb UC.heval).
Local Notation hfun := (sm_hfun UC.hprop_eqb UC.heval).
Local Notation hcstep := (sm_cstep UC.hprop_eqb UC.heval).
Local Notation srel := (sm_srel (prop := UC.hprop)).

(* ================================================================= *)
(* Two inputs.                                                        *)
(* ================================================================= *)

(* x in register 1 and c in register 2, every other register 0. *)
Definition sm_in2 (x c : nat) : nat -> nat :=
  fun r => if Nat.eqb r 1 then x else if Nat.eqb r 2 then c else 0.

(* P started on the register file vs stops with y in register 0. *)
Definition sm_hfun_from (P : list hinstr) (vs : nat -> nat) (y : nat) : Prop :=
  exists n, M.halted P (M.core_of (hrun_prog n P (M.start vs))) /\
            M.vals (M.core_of (hrun_prog n P (M.start vs))) 0 = y.

Lemma sm_vec_pos_const : forall n (a : nat) (p : pos n), vec_pos (Vector.const a n) p = a.
Proof.
  induction n as [| n IH]; intros a p.
  - exact (pos_O_invert _ p).
  - pattern p. apply pos_S_invert; cbv beta.
    + rewrite vec_pos0. reflexivity.
    + clear p. intro p. rewrite <- vec_pos_tail. apply IH.
Qed.

(* The start vector of a two-input MMA program, read by position. *)
Lemma sm_v0_pos : forall nn x c (p : pos (S (S (S nn)))),
  @vec_pos nat (S (S (S nn))) (Vector.append (Vector.cons nat 0 2 (Vector.cons nat x 1 (Vector.cons nat c 0 (Vector.nil nat))))
             (Vector.const 0 nn)) p = sm_in2 x c (pos2nat p).
Proof.
  intros nn x c p. pattern p. apply pos_S_invert; cbv beta; [reflexivity | clear p; intro p].
  pattern p. apply pos_S_invert; cbv beta; [reflexivity | clear p; intro p].
  pattern p. apply pos_S_invert; cbv beta; [reflexivity | clear p; intro p].
  simpl.
  rewrite sm_vec_pos_const. reflexivity.
Qed.

(* A core holding x and c as the MMA start vector. *)
Lemma sm_mmatch_in2 : forall nn x c (k : hcore),
  M.err k = false -> M.pc k = 1 -> (forall r, M.vals k r = sm_in2 x c r) ->
  sm_mmatch (S (S (S nn))) k
    (1, Vector.append (Vector.cons nat 0 2 (Vector.cons nat x 1 (Vector.cons nat c 0 (Vector.nil nat))))
          (Vector.const 0 nn)).
Proof.
  intros nn x c k He Hp Hv. unfold sm_mmatch. cbn [fst snd]. repeat split; auto.
  - intro p. rewrite Hv, sm_v0_pos. reflexivity.
  - intros r Hr. rewrite Hv. unfold sm_in2.
    replace (Nat.eqb r 1) with false by (symmetry; apply Nat.eqb_neq; lia).
    replace (Nat.eqb r 2) with false by (symmetry; apply Nat.eqb_neq; lia). reflexivity.
Qed.

(* ================================================================= *)
(* A run of sm_spec c V.                                              *)
(* ================================================================= *)

Definition sm_spec_s1 (c : nat) (V : list hinstr) (x : nat) : hstate :=
  hrun_prog c (sm_spec c V) (sm_hstart x).

Lemma sm_spec_phase1 : forall c V x,
  let s1 := sm_spec_s1 c V x in
  (forall q, M.vals (M.core_of s1) q = sm_in2 x c q) /\
  (forall q, q <> 2 -> M.vers (M.core_of s1) q = 0) /\
  M.facts (M.core_of s1) = [] /\ M.chan (M.core_of s1) = None /\
  M.err (M.core_of s1) = false /\ M.pc (M.core_of s1) = S c /\
  M.mu s1 = 0 /\ M.cert s1 = false.
Proof.
  intros c V x s1. unfold s1, sm_spec_s1.
  destruct (sm_incs_run UC.hprop_eqb UC.heval (sm_spec c V) 2 c 0 (sm_hstart x))
    as (Hv & Hw & Hf & Hc & He & Hp & Hm & Hk).
  - intros p Hp. unfold sm_spec. rewrite Nat.add_0_r.
    rewrite sm_fetch_app_left by (rewrite sm_incs_length; lia).
    destruct p as [| p]; [lia |]. simpl. unfold sm_incs. apply nth_error_repeat. lia.
  - reflexivity.
  - reflexivity.
  - split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]].
    + intro q. rewrite Hv. cbn [M.vals M.core_of sm_hstart M.start M.start_core].
      unfold sm_in2, sm_hin. destruct (Nat.eqb_spec q 2) as [-> | Hq]; [reflexivity |].
      destruct (Nat.eqb q 1); reflexivity.
    + intros q Hq. rewrite Hw by exact Hq. reflexivity.
    + exact Hf.
    + exact Hc.
    + exact He.
    + rewrite Hp. lia.
    + exact Hm.
    + exact Hk.
Qed.

Lemma sm_spec_embeds : forall c V, sm_embeds (sm_spec c V) V c.
Proof.
  intros c V. unfold sm_spec. rewrite <- (app_nil_r (sm_reloc c V)).
  rewrite <- (@sm_incs_length UC.hprop 2 c) at 2 3. apply sm_embeds_app.
Qed.

Lemma sm_spec_length : forall c V, length (sm_spec c V) = c + length V.
Proof. intros. unfold sm_spec. rewrite app_length, sm_incs_length, sm_reloc_length. reflexivity. Qed.

(* sm_spec c V computes y from x exactly when V, started from the state the
   prefix leaves (with the program counter put back to 1), stops with y. *)
Lemma sm_spec_hfun : forall c V x y,
  hfun (sm_spec c V) x y <->
  exists n, M.halted V (M.core_of (hrun_prog n V (sm_at1 (sm_spec_s1 c V x)))) /\
            M.vals (M.core_of (hrun_prog n V (sm_at1 (sm_spec_s1 c V x)))) 0 = y.
Proof.
  intros c V x y.
  destruct (sm_spec_phase1 c V x) as (_ & _ & _ & _ & _ & Hp1 & _).
  set (s1 := sm_spec_s1 c V x) in *.
  assert (Hrel : forall n, srel (fun _ => True) c (length V) (hrun_prog n V (sm_at1 s1))
                              (hrun_prog (c + n) (sm_spec c V) (sm_hstart x))).
  { intro n. rewrite sm_run_add. fold (sm_spec_s1 c V x). fold s1.
    apply (sm_block_run_final UC.hprop_eqb UC.heval (fun _ => True) (sm_spec c V) V c
             (sm_spec_embeds c V) (sm_within_all V) (sm_spec_length c V)).
    apply sm_at1_rel. exact Hp1. }
  split.
  - intros [s [[N [-> HN]] Hy]].
    set (m := N - c).
    assert (Es : hrun_prog (c + m) (sm_spec c V) (sm_hstart x) = hrun_prog N (sm_spec c V) (sm_hstart x))
      by (apply sm_halted_after; [unfold m; lia | exact HN]).
    pose proof (Hrel m) as Hr. rewrite Es in Hr.
    exists m. split.
    + unfold M.halted. destruct (M.next_instr V (M.core_of (hrun_prog m V (sm_at1 s1)))) eqn:Hn;
        [| reflexivity].
      exfalso. apply (sm_block_not_halted UC.hprop_eqb UC.heval (fun _ => True) (sm_spec c V) V c _ _
                        (sm_spec_embeds c V) (sm_within_all V) Hr); [congruence | exact HN].
    + destruct Hr as ((Hv & _) & _). rewrite Hv. exact Hy.
  - intros [n [Hh Hy]].
    exists (hrun_prog (c + n) (sm_spec c V) (sm_hstart x)). split.
    + exists (c + n). split; [reflexivity |].
      apply (sm_block_halted (fun _ => True) (sm_spec c V) V c (M.core_of (hrun_prog n V (sm_at1 s1))));
        [apply sm_spec_embeds | apply sm_spec_length | apply (Hrel n) | exact Hh].
    + destruct (Hrel n) as ((Hv & _) & _). rewrite <- Hv. exact Hy.
Qed.

(* ================================================================= *)
(* Versions that no CHECK or COMMIT reads do not matter.              *)
(* ================================================================= *)

Definition sm_vrel (Sr : nat -> Prop) (k k' : hcore) : Prop :=
  (forall r, M.vals k r = M.vals k' r) /\ (forall r, Sr r -> M.vers k r = M.vers k' r) /\
  M.pc k = M.pc k' /\ M.facts k = M.facts k' /\ M.chan k = M.chan k' /\ M.err k = M.err k'.

Lemma sm_vrel_step : forall Sr (V : list hinstr) k k', sm_within Sr V -> sm_vrel Sr k k' ->
  sm_vrel Sr (hcstep V k) (hcstep V k').
Proof.
  intros Sr V k k' Hwin Hrel. pose proof Hrel as (Hv & Hw & Hp & Hf & Hc & He).
  assert (Hn : M.next_instr V k = M.next_instr V k') by (unfold M.next_instr; rewrite He, Hp; reflexivity).
  unfold sm_cstep. rewrite <- Hn.
  destruct (M.next_instr V k) as [i |] eqn:Hi; [| exact Hrel].
  destruct (sm_next_some V k i Hi) as (Ek & Hfe & _).
  assert (Hin : In i V).
  { destruct (M.pc k) as [| q]; [discriminate |]. simpl in Hfe. eapply nth_error_In; eauto. }
  assert (Ek' : M.err k' = false) by congruence.
  unfold M.cexec. rewrite Ek, Ek'.
  destruct i as [r | r j | | p r | p r |]; cbv beta iota.
  - unfold sm_vrel. rewrite <- (Hv r). repeat split.
    + intro q. rewrite !M.multi_val_write. destruct (Nat.eqb r q); auto.
    + intros q Hq'. rewrite !M.multi_ver_write. rewrite (Hw q Hq'). reflexivity.
    + simpl. congruence.
    + simpl. exact Hf.
    + simpl. exact Hc.
    + simpl. exact He.
  - rewrite <- (Hv r). destruct (M.vals k r) as [| v].
    + unfold sm_vrel. simpl. repeat split; auto.
    + unfold sm_vrel. repeat split.
      * intro q. rewrite !M.multi_val_write. destruct (Nat.eqb r q); auto.
      * intros q Hq'. rewrite !M.multi_ver_write. rewrite (Hw q Hq'). reflexivity.
      * simpl. exact Hf.
      * simpl. exact Hc.
      * simpl. exact He.
  - exact Hrel.
  - assert (Hs : Sr r) by (apply (Hwin _ r Hin); simpl; [apply Nat.eqb_refl | reflexivity]).
    assert (Hok : M.check_ok UC.heval k p r = M.check_ok UC.heval k' p r).
    { unfold M.check_ok. rewrite Ek, Ek', (Hv r), Hf. reflexivity. }
    rewrite Hok. destruct (M.check_ok UC.heval k' p r).
    + unfold sm_vrel, M.record_fact, M.claim. simpl. repeat split; auto.
      rewrite (Hw r Hs), Hf. reflexivity.
    + unfold sm_vrel, M.trap. simpl. repeat split; auto.
  - assert (Hs : Sr r) by (apply (Hwin _ r Hin); simpl; [apply Nat.eqb_refl | reflexivity]).
    assert (Hcl : M.claim k p r = M.claim k' p r) by (unfold M.claim; rewrite (Hw r Hs); reflexivity).
    assert (Hok : M.commit_ok UC.hprop_eqb k p r = M.commit_ok UC.hprop_eqb k' p r).
    { unfold M.commit_ok. rewrite Ek, Ek', Hcl, Hf. reflexivity. }
    rewrite Hok. destruct (M.commit_ok UC.hprop_eqb k' p r).
    + unfold sm_vrel, M.commit_to. simpl. rewrite Hcl. repeat split; auto.
    + unfold sm_vrel, M.trap. simpl. repeat split; auto.
  - assert (Hok : M.certify_ok k = M.certify_ok k').
    { unfold M.certify_ok. rewrite Ek, Ek', Hc. reflexivity. }
    rewrite Hok. destruct (M.certify_ok k').
    + unfold sm_vrel, M.goto. simpl. repeat split; auto.
    + unfold sm_vrel, M.trap. simpl. repeat split; auto.
Qed.

Lemma sm_vrel_run : forall Sr (V : list hinstr) n k k', sm_within Sr V -> sm_vrel Sr k k' ->
  sm_vrel Sr (sm_crun n V k) (sm_crun n V k').
Proof.
  intros Sr V n. induction n as [| n IH]; intros k k' Hw H; [exact H |].
  simpl. apply IH; [exact Hw | apply sm_vrel_step; assumption].
Qed.

Lemma sm_vrel_halted : forall Sr (V : list hinstr) k k', sm_vrel Sr k k' ->
  M.halted V k -> M.halted V k'.
Proof.
  intros Sr V k k' (_ & _ & Hp & _ & _ & He) H. unfold M.halted, M.next_instr in *.
  rewrite <- He, <- Hp. exact H.
Qed.

Lemma sm_vrel_sym : forall Sr k k', sm_vrel Sr k k' -> sm_vrel Sr k' k.
Proof.
  intros Sr k k' (Hv & Hw & Hp & Hf & Hc & He). unfold sm_vrel.
  split; [intro r; symmetry; apply Hv |].
  split; [intros r Hr; symmetry; apply Hw, Hr |]. repeat split; congruence.
Qed.

(* ================================================================= *)
(* 1. s-m-n.                                                          *)
(* ================================================================= *)

Theorem sm_smn : forall c V x y,
  sm_within (fun r => r <> 2) V ->
  (hfun (sm_spec c V) x y <-> sm_hfun_from V (sm_in2 x c) y).
Proof.
  intros c V x y Hwin. rewrite sm_spec_hfun.
  destruct (sm_spec_phase1 c V x) as (Hv1 & Hw1 & Hf1 & Hc1 & He1 & _).
  assert (Hrel : sm_vrel (fun r => r <> 2) (M.core_of (sm_at1 (sm_spec_s1 c V x)))
                   (M.core_of (M.start (sm_in2 x c)))).
  { unfold sm_vrel, sm_at1, M.goto. simpl.
    repeat split; auto; try (intros r Hr; rewrite Hw1 by exact Hr; reflexivity). }
  unfold sm_hfun_from. split.
  - intros [n [Hh Hy]]. exists n.
    rewrite sm_core_run in *.
    pose proof (sm_vrel_run _ V n _ _ Hwin Hrel) as Hr.
    split; [exact (sm_vrel_halted _ V _ _ Hr Hh) |].
    destruct Hr as (Hv & _). rewrite <- Hv. exact Hy.
  - intros [n [Hh Hy]]. exists n.
    rewrite sm_core_run in *.
    pose proof (sm_vrel_sym _ _ _ (sm_vrel_run _ V n _ _ Hwin Hrel)) as Hr.
    split; [exact (sm_vrel_halted _ V _ _ Hr Hh) |].
    destruct Hr as (Hv & _). rewrite <- Hv. exact Hy.
Qed.

(* ================================================================= *)
(* An MMA program for two inputs, read as a host program.             *)
(* ================================================================= *)

Lemma sm_mma_two : forall nn (Pm : list (mm_instr (pos (S (S (S nn)))))) (R : Vector.t nat 2 -> nat -> Prop),
  (forall v : Vector.t nat 2, forall m, R v m <->
     exists c (v' : Vector.t nat (2 + nn)),
       sss_output (@mma_sss (S (S (S nn)))) (1, Pm)
         (1, Vector.append (Vector.cons nat 0 2 v) (Vector.const 0 nn)) (c, Vector.cons nat m (2 + nn) v')) ->
  forall (k : hcore) x c m,
  M.err k = false -> M.pc k = 1 -> (forall r, M.vals k r = sm_in2 x c r) ->
  (R (Vector.cons nat x 1 (Vector.cons nat c 0 (Vector.nil nat))) m <->
   exists n, M.halted (sm_mma_host (S (S (S nn))) Pm) (sm_crun n (sm_mma_host (S (S (S nn))) Pm) k) /\
             M.vals (sm_crun n (sm_mma_host (S (S (S nn))) Pm) k) 0 = m).
Proof.
  intros nn Pm R HR k x c m He Hp Hv.
  rewrite HR. apply (sm_mma_host_out (S (S nn)) Pm k _ m).
  apply sm_mmatch_in2; assumption.
Qed.

Lemma sm_mma_plain : forall N (Pm : list (mm_instr (pos N))) Sr, sm_within Sr (sm_mma_host N Pm).
Proof.
  intros N Pm Sr i r Hin _ Hpl. exfalso. unfold sm_mma_host, sm_mma_prog in Hin.
  rewrite map_map in Hin. apply in_map_iff in Hin. destruct Hin as [[x | x j] [<- _]]; discriminate.
Qed.

(* ================================================================= *)
(* 2. A universal program.                                            *)
(* ================================================================= *)

Theorem sm_host_universal : exists Uh : list hinstr,
  (forall i, In i Uh -> M.plain i = true) /\
  forall c x y, sm_hfun_from Uh (sm_in2 x c) y <-> hfun (sm_hdecode c) x y.
Proof.
  destruct sm_uev_MMA as [nn [Pm HPm]].
  exists (sm_mma_host (S (S (S nn))) Pm). split.
  { intros i Hin. unfold sm_mma_host, sm_mma_prog in Hin. rewrite map_map in Hin.
    apply in_map_iff in Hin. destruct Hin as [[x | x j] [<- _]]; reflexivity. }
  intros c x y. rewrite <- sm_uev_spec.
  change (exists n, sm_uev n x c = Some y) with (sm_Ruev (Vector.cons nat x 1 (Vector.cons nat c 0 (Vector.nil nat))) y).
  rewrite (sm_mma_two nn Pm sm_Ruev HPm (M.core_of (M.start (sm_in2 x c))) x c y eq_refl eq_refl (fun r => eq_refl)).
  unfold sm_hfun_from. split; intros [n Hn]; exists n; rewrite sm_core_run in *; exact Hn.
Qed.

(* ================================================================= *)
(* 3. The second recursion theorem.                                   *)
(* ================================================================= *)

Theorem sm_second_recursion : forall T : list hinstr, exists e : list hinstr,
  forall x y, hfun e x y <-> exists d, hfun T (sm_hcode e) d /\ hfun (sm_hdecode d) x y.
Proof.
  intro T.
  set (t := sm_hcode T).
  destruct (sm_ev_MMA t) as [nn [Pm HPm]].
  set (VG := sm_mma_host (S (S (S nn))) Pm).
  set (c0 := sm_kpcode (sm_mma_prog (S (S (S nn))) Pm)).
  assert (HVG : sm_hdecode c0 = VG) by (unfold sm_hdecode, c0, VG, sm_mma_host; rewrite sm_kpdec_kpcode; reflexivity).
  set (e := sm_spec c0 VG).
  assert (Hcode : sm_kspec c0 = sm_hcode e) by (rewrite sm_kspec_code, HVG; reflexivity).
  exists e. intros x y.
  (* e computes what VG computes on x and c0. *)
  unfold e at 1. rewrite sm_spec_hfun.
  destruct (sm_spec_phase1 c0 VG x) as (Hv1 & _ & _ & _ & He1 & _).
  set (kB := M.core_of (sm_at1 (sm_spec_s1 c0 VG x))).
  transitivity (exists n, M.halted VG (sm_crun n VG kB) /\ M.vals (sm_crun n VG kB) 0 = y).
  { split; intros [n Hn]; exists n; rewrite sm_core_run in *; exact Hn. }
  (* VG computes the evaluator. *)
  transitivity (sm_Rev t (Vector.cons nat x 1 (Vector.cons nat c0 0 (Vector.nil nat))) y).
  { symmetry. exact (sm_mma_two nn Pm (sm_Rev t) HPm kB x c0 y He1 eq_refl Hv1). }
  change (sm_Rev t (Vector.cons nat x 1 (Vector.cons nat c0 0 (Vector.nil nat))) y)
    with (exists n, sm_ev t n x c0 = Some y).
  rewrite sm_ev_spec. unfold t. rewrite sm_hdecode_hcode, Hcode. reflexivity.
Qed.

(* ================================================================= *)
(* 4. Kleene's recursion theorem.                                     *)
(* ================================================================= *)

(* T computes F on numbers: on the number of p it stops with the number of
   F p. *)
Definition sm_computes_map (T : list hinstr) (F : list hinstr -> list hinstr) : Prop :=
  forall p, hfun T (sm_hcode p) (sm_hcode (F p)).

Theorem sm_kleene : forall (F : list hinstr -> list hinstr) (T : list hinstr),
  sm_computes_map T F ->
  exists e, forall x y, hfun e x y <-> hfun (F e) x y.
Proof.
  intros F T HT. destruct (sm_second_recursion T) as [e He].
  exists e. intros x y. rewrite He. split.
  - intros [d [Hd Hy]]. rewrite (sm_hfun_det UC.hprop_eqb UC.heval T _ d _ Hd (HT e)) in Hy.
    rewrite sm_hdecode_hcode in Hy. exact Hy.
  - intro Hy. exists (sm_hcode (F e)). split; [exact (HT e) |]. rewrite sm_hdecode_hcode. exact Hy.
Qed.

(* The same on numbers: a total map f on numbers computed by a host
   program has a number e whose program computes what the program numbered
   f e computes. *)
Theorem sm_kleene_codes : forall (f : nat -> nat) (T : list hinstr),
  (forall n, hfun T n (f n)) ->
  exists e, forall x y, hfun (sm_hdecode e) x y <-> hfun (sm_hdecode (f e)) x y.
Proof.
  intros f T HT. destruct (sm_second_recursion T) as [p Hp].
  exists (sm_hcode p). intros x y. rewrite sm_hdecode_hcode, Hp. split.
  - intros [d [Hd Hy]]. rewrite (sm_hfun_det UC.hprop_eqb UC.heval T _ d _ Hd (HT _)) in Hy. exact Hy.
  - intro Hy. exists (f (sm_hcode p)). split; [apply HT | exact Hy].
Qed.

(* ================================================================= *)
(* 5. The diagonal on this machine.                                   *)
(* ================================================================= *)

(* A property of programs that depends only on the partial function
   computed. *)
Definition sm_fun_ext (Pi : list hinstr -> Prop) : Prop :=
  forall p q, (forall x y, hfun p x y <-> hfun q x y) -> Pi p -> Pi q.

(* No decider whose flip the machine can compute is correct. *)
Theorem sm_no_inside_decider : forall (Pi : list hinstr -> Prop) yes no,
  sm_fun_ext Pi -> Pi yes -> ~ Pi no ->
  forall d : list hinstr -> bool,
  (exists T, sm_computes_map T (fun p => if d p then no else yes)) ->
  ~ (forall p, d p = true <-> Pi p).
Proof.
  intros Pi yes no Hext Hy Hn d [T HT] Hd.
  destruct (sm_kleene _ T HT) as [e He].
  assert (He' : forall x z, hfun e x z <-> hfun (if d e then no else yes) x z) by exact He.
  destruct (d e) eqn:Hde.
  - apply Hn. apply (Hext e no); [exact He' | apply Hd, Hde].
  - assert (HPe : Pi e).
    { apply (Hext yes e); [| exact Hy]. intros x z. rewrite He'. reflexivity. }
    apply Hd in HPe. congruence.
Qed.

(* Rice's theorem for properties of the partial function computed. *)
Theorem sm_host_rice_fun : forall (Pi : list hinstr -> Prop) yes no,
  sm_fun_ext Pi -> Pi yes -> ~ Pi no -> undecidable Pi.
Proof.
  intros Pi yes no Hext Hy Hn.
  apply (sm_host_rice UC.hprop_eqb UC.heval Pi yes no); [| exact Hy | exact Hn].
  intros p q Hpq Hp. apply (Hext p q); [| exact Hp].
  apply sm_hequiv_hfun. exact Hpq.
Qed.

(* ================================================================= *)
(* Assumption audit.                                                  *)
(* ================================================================= *)

Print Assumptions sm_smn.
Print Assumptions sm_host_universal.
Print Assumptions sm_second_recursion.
Print Assumptions sm_kleene.
Print Assumptions sm_kleene_codes.
Print Assumptions sm_no_inside_decider.
Print Assumptions sm_host_rice_fun.
