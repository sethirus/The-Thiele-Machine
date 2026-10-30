(** NeutralUnivShadow.v: a universal machine with no certification anywhere.

    U_N is U_P with every instruction read on the canonical neutral host CNH
    (NeutralUnivCanon.v): INC, DEC, HALT as themselves, CERTIFY as TICK, and CHECK,
    COMMIT, PAY as PAY.  Same lines, same registers.

      UP_never_traps    U_P's run from the load of any computably presented
                        machine never traps (its CHECKs, COMMITs and
                        CERTIFYs all pass);
      shadow_lockstep   so, on a run that has not trapped, U_N on CNH has the
                        same line, registers, record and ledger as U_P on
                        its host, step for step;
      UN_neutral_universal
                        U_N on CNH is a neutral universal machine (N0-N5, in
                        order) for every computably presented machine, with
                        surcharge at most 3, on a host that has registers,
                        INC/DEC/HALT, MARK r, TICK and PAY and nothing else:
                        no claims, no checker, no fact table, no channel.   *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Undecidability.FRACTRAN.Util Require Import prime_seq.
Require Import Kernel.UMachDef.
Require Import Kernel.NeutralUnivBase.
Require Import Kernel.NeutralUnivDef.
Require Import Kernel.NeutralUnivCanon.
Require Import Kernel.NeutralUnivTools.
Require Import Kernel.NeutralUnivUP.
Require Import Kernel.UniversalPCodes.
Require Import Kernel.UniversalPBridge.
Require Import Kernel.UniversalPBlocks.
Require Import Kernel.UniversalPLayout.
Require Import Kernel.UniversalPPhases.
Require Import Kernel.UniversalPSim.
Require Import Kernel.UniversalPRun.
Require Import Kernel.PresentedUniversal.
Require Import Minimal.Presented.
Require Import Kernel.Presentation.
Require Import Kernel.CompilerCodes.
Require Import Kernel.CompilerChecker.
Require Import Kernel.CompilerLifts.
Require Import Kernel.CompilerIcomp.
Require Import Kernel.CompilerGuest.
Require Import Kernel.CompilerGuestRun.

Definition kap (i : @M.pu_instr pu_hprop) : cmove :=
  match i with
  | M.INC r => CInc r | M.DEC r j => CDec r j | M.HALT => CHalt
  | M.CERTIFY => CTick | _ => CPay
  end.

Definition U_N : list cmove := map kap U_P.

Lemma U_N_nomark : forall l r, cfetch U_N l <> Some (CMark r).
Proof.
  intros [| l] r; simpl; [discriminate |]. unfold U_N. rewrite nth_error_map.
  destruct (nth_error U_P l) as [[] |]; simpl; discriminate.
Qed.

(* ================================================================= *)
(* Lockstep on untrapped runs.                                        *)
(* ================================================================= *)

Definition srel (h : @M.pu_state pu_hprop) (c : cst) : Prop :=
  cpc c = M.pc (M.core_of h) /\ (forall x, creg c x = M.vals (M.core_of h) x) /\
  cflag c = M.cert h /\ M.err (M.core_of h) = false.

Lemma next_agree : forall h c, srel h c ->
  cnext U_N c = option_map kap (M.pu_next_instr U_P (M.core_of h)).
Proof.
  intros h c (Hp & _ & _ & He). unfold cnext, M.pu_next_instr. rewrite He, Hp.
  unfold cfetch, M.pu_fetch. destruct (M.pc (M.core_of h)) as [| l]; [reflexivity |].
  unfold U_N. rewrite nth_error_map. destruct (nth_error U_P l) as [[] |]; reflexivity.
Qed.

Lemma step_agree : forall h c i, srel h c -> M.pu_next_instr U_P (M.core_of h) = Some i ->
  M.err (M.core_of (M.pu_exec pu_hprop_eqb pu_heval h i)) = false ->
  srel (M.pu_exec pu_hprop_eqb pu_heval h i) (cstep c (kap i)) /\ ccost (kap i) = M.pu_cost i.
Proof.
  intros h c i (Hp & Hr & Hf & He) Hn Ha.
  destruct h as [[vs vr p f ch e] m ce]. destruct c as [cp cr cf cl]. simpl in *. subst e.
  unfold M.pu_exec, M.pu_cexec in *. simpl in *.
  destruct i as [r | r j | | q r | q r | |]; simpl in *.
  all: unfold srel, M.pu_write, M.pu_goto, M.pu_record_fact, M.pu_commit_to, M.pu_trap in *; simpl in *.
  - split; [| reflexivity]. split; [lia |]. split.
    + intros x. unfold upd, M.pu_upd. destruct (Nat.eqb x r); [rewrite Hr |]; auto.
    + split; [rewrite orb_false_r; exact Hf | reflexivity].
  - rewrite Hr. destruct (vs r) as [| n] eqn:V; simpl.
    + split; [| reflexivity]. split; [lia |]. split; [exact Hr |]. split; [rewrite orb_false_r; exact Hf | reflexivity].
    + split; [| reflexivity]. split; [reflexivity |]. split.
      * intros x. unfold upd, M.pu_upd. destruct (Nat.eqb x r); auto.
      * split; [rewrite orb_false_r; exact Hf | reflexivity].
  - unfold M.pu_next_instr in Hn. simpl in Hn. destruct (M.pu_fetch U_P p) as [[] |]; discriminate.
  - destruct (M.pu_check_ok pu_heval _ q r); simpl in *; [| discriminate Ha].
    split; [| reflexivity]. split; [lia |]. split; [exact Hr |]. split; [rewrite orb_false_r; exact Hf | reflexivity].
  - destruct (M.pu_commit_ok pu_hprop_eqb _ q r); simpl in *; [| discriminate Ha].
    split; [| reflexivity]. split; [lia |]. split; [exact Hr |]. split; [rewrite orb_false_r; exact Hf | reflexivity].
  - unfold M.pu_fires. destruct (M.pu_certify_ok _) eqn:C; simpl in *; [| discriminate Ha].
    split; [| reflexivity]. split; [lia |]. split; [exact Hr |]. split; [rewrite orb_true_r; reflexivity | reflexivity].
  - split; [| reflexivity]. split; [lia |]. split; [exact Hr |]. split; [rewrite orb_false_r; exact Hf | reflexivity].
Qed.

Theorem shadow_lockstep : forall n h c, srel h c ->
  M.err (M.core_of (hr (H:=UP_host) U_P h n)) = false ->
  srel (hr (H:=UP_host) U_P h n) (hr (H:=CNH) U_N c n) /\
  hl (H:=UP_host) U_P h n = hl (H:=CNH) U_N c n.
Proof.
  induction n as [| n IH]; intros h c R He; [split; [exact R | reflexivity] |].
  pose proof (next_agree h c R) as N. simpl in He |- *.
  change (hnext CNH U_N c) with (cnext U_N c). rewrite N.
  destruct (M.pu_next_instr U_P (M.core_of h)) as [i |] eqn:Hn; simpl; [| split; [exact R | reflexivity]].
  assert (Ha : M.err (M.core_of (M.pu_exec pu_hprop_eqb pu_heval h i)) = false).
  { exact (err_back UP_host UP_reg U_P n _ He). }
  destruct (step_agree h c i R Hn Ha) as [R' Hc].
  change (hstep CNH c (kap i)) with (cstep c (kap i)).
  destruct (IH _ _ R' He) as [A B]. split; [exact A |].
  change (hcost CNH (kap i)) with (ccost (kap i)). rewrite Hc, B. reflexivity.
Qed.

(* ================================================================= *)
(* U_P never traps on a presented machine.                            *)
(* ================================================================= *)

Lemma err_mono : forall (h : @M.pu_state pu_hprop) a b, a <= b ->
  M.err (M.core_of (hr (H:=UP_host) U_P h b)) = false -> M.err (M.core_of (hr (H:=UP_host) U_P h a)) = false.
Proof.
  intros h a b Hab Hb. replace b with (a + (b - a)) in Hb by lia. rewrite hr_add in Hb.
  exact (err_back UP_host UP_reg U_P (b - a) _ Hb).
Qed.

Lemma cg_yhalt_err : forall Mp pc s0 n N, cg_yhalt Mp pc s0 n N ->
  G.err (G.core_of (P.pr_run_prog cg_uprop_eqb cg_ueval N (cg_guest Mp pc) (cg_ystart Mp pc s0))) = false.
Proof.
  intros Mp pc s0 n N ([e a] & [He Ha] & Hpc & Hsim).
  destruct Hsim as (_ & _ & _ & _ & _ & H6 & _). exact H6.
Qed.

Theorem UP_never_traps : forall (i : pinst) t,
  M.err (M.core_of (hr (H:=UP_host) U_P (M.pu_start (UP_code i)) t)) = false.
Proof.
  intros [Mp [pc s0]] t. rewrite UP_load. simpl fst; simpl snd; simpl projT1.
  rewrite UP_hr. fold (pu_hrun (cg_guest Mp pc) 0 (pu_guest_b Mp pc s0) t).
  fold (pu_host_at Mp pc s0 t). rewrite <- UP_hr.
  destruct (UP_presented_order Mp pc s0) as (f & Hinc & HD).
  destruct (Lp_dec Mp s0 (S t)) as [HL | HL].
  - (* live through t + 1 steps: the matching time f t >= t is untrapped *)
    assert (Hge : forall k, k <= t -> k <= f k).
    { induction k as [| k IHk]; intros Hk; [lia |].
      pose proof (Hinc k (fun m Hm => HL m ltac:(lia))). pose proof (IHk ltac:(lia)). lia. }
    destruct (HD t (fun m Hm => HL m ltac:(lia))) as (_ & _ & _ & He).
    unfold pu_host_at, pu_hrun in He. rewrite <- UP_hr in He.
    exact (err_mono _ t (f t) (Hge t (le_n t)) He).
  - (* the machine stops at some n0 <= t: the host halts there untrapped *)
    assert (Hfirst : exists n0, n0 <= t /\ Lp Mp s0 n0 /\ pm_next Mp (presented_run Mp s0 n0) = None).
    { clear Hinc HD f. induction t as [| t IH].
      - exists 0. split; [lia |]. split; [intros m Hm; lia |].
        destruct (pm_next Mp (presented_run Mp s0 0)) eqn:E; [| reflexivity].
        exfalso. apply HL. intros m Hm. replace m with 0 by lia. rewrite E. discriminate.
      - destruct (Lp_dec Mp s0 (S t)) as [HL' | HL'].
        + exists (S t). split; [lia |]. split; [exact HL' |].
          destruct (pm_next Mp (presented_run Mp s0 (S t))) eqn:E; [| reflexivity].
          exfalso. apply HL. intros m Hm. destruct (Nat.eq_dec m (S t)) as [-> | Hne]; [rewrite E; discriminate |].
          apply HL'. lia.
        + destruct (IH HL') as (n0 & Hn0 & HL0 & Hs). exists n0. split; [lia | auto]. }
    destruct Hfirst as (n0 & _ & HL0 & Hs).
    destruct (cg_y_head Mp pc s0 n0 HL0) as (N0 & _ & Hp).
    destruct (cg_y_stop Mp pc s0 n0 N0 Hp Hs) as (N & _ & Hh).
    pose proof (cg_yhalt_err Mp pc s0 n0 N Hh) as Herr.
    destruct (cg_yhalt_facts Mp pc s0 n0 N Hh) as (Hhalt & _).
    destruct (pu_halt_point (cg_guest Mp pc) 0 (pu_guest_b Mp pc s0) N Hhalt) as (T & RH).
    destruct RH as (_ & HT & _ & _ & HeT & _).
    assert (HeT' : M.err (M.core_of (hr (H:=UP_host) U_P (pu_host_start Mp pc s0) T)) = false).
    { rewrite UP_hr.
      change (M.err (M.core_of (pu_hrun (cg_guest Mp pc) 0 (pu_guest_b Mp pc s0) T)) = false).
      rewrite HeT. exact Herr. }
    destruct (le_lt_dec t T) as [Hle | Hlt].
    + exact (err_mono _ t T Hle HeT').
    + rewrite (hr_stopped_stays UP_host U_P _ T t ltac:(lia)); [exact HeT' |].
      simpl. rewrite UP_hr. exact HT.
Qed.

(* ================================================================= *)
(* U_N on CNH.                                                        *)
(* ================================================================= *)

Lemma start_rel : forall rho, srel (M.pu_start rho) (ctpl rho).
Proof. intros rho. repeat split. Qed.

Theorem UN_neutral_universal :
  neutral_universal presented_class CNH (fun i => option (Minimal.ThieleComplete.cs_state (pm_sys (projT1 i))))
    pobs 3.
Proof.
  exists U_N, cnh_reg, (fun l => tick_at (cfetch U_N l)), ctpl, UP_code, UP_dec.
  split; [exact cnh_host_nc |]. split; [exact (cnh_line_raise_nomark U_N U_N_nomark) |].
  split; [exact ctpl_clean |].
  intros i.
  assert (L : forall n, srel (hr (H:=UP_host) U_P (M.pu_start (UP_code i)) n) (hr (H:=CNH) U_N (ctpl (UP_code i)) n) /\
                        hl (H:=UP_host) U_P (M.pu_start (UP_code i)) n = hl (H:=CNH) U_N (ctpl (UP_code i)) n).
  { intros n. apply shadow_lockstep; [apply start_rel | apply UP_never_traps]. }
  assert (Nx : forall n, hnext CNH U_N (hr (H:=CNH) U_N (ctpl (UP_code i)) n) = None <->
                         hnext UP_host U_P (hr (H:=UP_host) U_P (M.pu_start (UP_code i)) n) = None).
  { intros n. change (hnext CNH U_N) with (cnext U_N). rewrite (next_agree _ _ (proj1 (L n))).
    simpl. destruct (M.pu_next_instr U_P _); simpl; split; intros; congruence. }
  assert (Mt : forall K n m, match_at presented_class UP_host _ pobs K U_P (M.pu_start (UP_code i)) i
                               (fun h => UP_dec i (b_reg UP_reg h)) n m ->
                             match_at presented_class CNH _ pobs K U_N (ctpl (UP_code i)) i
                               (fun h => UP_dec i (b_reg cnh_reg h)) n m).
  { intros K n m (D & F & s & Hs & Hl). destruct (L n) as [(Hp & Hr & Hf & _) Hle].
    split; [| split; [| exists s; split; [exact Hs | rewrite <- Hle; exact Hl]]].
    - simpl. unfold UP_dec in *. rewrite Hr. exact D.
    - simpl. rewrite Hf. exact F. }
  destruct (UP_halt i) as [[H1a H1b] H1c]. destruct (UP_in_order i) as (f & Hinc & Hm).
  split; [split |].
  - split.
    + intros [n Hn]. apply H1a. exists n. apply Nx, Hn.
    + intros Hg. destruct (H1b Hg) as [n Hn]. exists n. apply Nx, Hn.
  - intros m0 Hl Hs. destruct (H1c m0 Hl Hs) as (n & Hn & HM). exists n. split; [apply Nx, Hn | apply Mt, HM].
  - exists f. split; [exact Hinc | intros m Hl; apply Mt, Hm, Hl].
Qed.

Print Assumptions shadow_lockstep.
Print Assumptions UP_never_traps.
Print Assumptions UN_neutral_universal.
