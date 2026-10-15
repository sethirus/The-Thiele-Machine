(** NeutralUnivUP.v: U_P is a neutral universal machine (all of N0-N5, IN ORDER)
    for every computably presented machine, with surcharge at most 3.

    Built only on the theorems about U_P in UniversalPRun.v,
    UniversalPSim.v, PresentedUniversal.v and CompilerGuestRun.v, redoing
    two of their inductions with the order kept:

      UP_host_nc        (N0) U_P's host is neutral-complete (it is
                        Thiele-complete: pu_host_thiele_complete_with, and
                        NeutralComplete.tc_to_nc), its computing moves being
                        exactly INC, DEC, HALT;
      UP_line_raise     (N3) every record move of U_P traps or sets
                        record := record || [the line holds CERTIFY], from
                        every state;
      UP_reg            (N4) U_P's host is a register host;
      UP_clean          (N5) U_P's loads are M.pu_start of a register file;
      UP_halt           (N1) with the halted state matched;
      UP_chain          finite increasing chains of matching times
                        (compiled-guest level: ychain; host level: hchain);
      UP_in_order       (N2) one strictly increasing matching function;
      UP_neutral_universal  the whole definition, K = 3.

    (The guests here are all computably presented machines; the neutral
    ones among them are a subclass, for which the bound is 2 once their
    record is up and 0 before: NeutralHost.unit_raise_surcharge_two.)     *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Undecidability.FRACTRAN.Util Require Import prime_seq.
Require Import Kernel.UMachDef.
Require Import Kernel.NeutralUnivBase.
Require Import Kernel.NeutralUnivDef.
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
Require Minimal.ThieleComplete.
Require Minimal.NeutralComplete.
Module T := Minimal.ThieleComplete.

(* ================================================================= *)
(* The class and the host (as in UMachCheatPresented.v and UMachMeetsUP.v).     *)
(* ================================================================= *)

Definition pinst : Type :=
  { Mp : presented_machine & (cg_presentation Mp * T.cs_state (pm_sys Mp))%type }.

Definition presented_class : gclass :=
  mk_gclass pinst
    (fun i => T.cs_state (pm_sys (projT1 i)))
    (fun i => T.cs_instr (pm_sys (projT1 i)))
    (fun i => pm_next (projT1 i))
    (fun i => T.cs_step (pm_sys (projT1 i)))
    (fun i => T.cs_cost (pm_sys (projT1 i)))
    (fun i => T.cs_cert (pm_sys (projT1 i)))
    (fun i => T.cs_cert_costs (pm_sys (projT1 i)))
    (fun i => snd (projT2 i)).

Definition pobs (i : pinst) (s : T.cs_state (pm_sys (projT1 i))) : option (T.cs_state (pm_sys (projT1 i))) :=
  Some s.

Definition UP_host : host :=
  mk_host (@M.pu_state pu_hprop) (@M.pu_instr pu_hprop) (M.pu_exec pu_hprop_eqb pu_heval)
    (@M.pu_cost pu_hprop) (@M.cert pu_hprop)
    (fun s i => M.pu_multi_a2 pu_hprop_eqb pu_heval s i)
    (list (@M.pu_instr pu_hprop)) (fun P s => M.pu_next_instr P (M.core_of s)).

Lemma UP_hr : forall Q n s,
  hr (H:=UP_host) Q s n = M.pu_run_prog pu_hprop_eqb pu_heval n Q s.
Proof.
  intros Q n. induction n as [| n IH]; intros s; [reflexivity |].
  simpl. unfold M.pu_step. destruct (M.pu_next_instr Q (M.core_of s)) eqn:E.
  - apply IH.
  - symmetry. apply M.pu_multi_run_prog_halted. exact E.
Qed.

Lemma UP_hl : forall Q n s,
  M.mu (M.pu_run_prog pu_hprop_eqb pu_heval n Q s) = M.mu s + hl (H:=UP_host) Q s n.
Proof.
  intros Q n. induction n as [| n IH]; intros s; [simpl; lia |].
  simpl. unfold M.pu_step. destruct (M.pu_next_instr Q (M.core_of s)) eqn:E.
  - rewrite IH. simpl. lia.
  - rewrite M.pu_multi_run_prog_halted by exact E. lia.
Qed.

Section Inst.
Variable i : pinst.
Local Notation Mp := (projT1 i).

Lemma pgr : forall n s, gr (C:=presented_class) (i:=i) s n = presented_run Mp s n.
Proof.
  induction n as [| n IH]; intros s; [reflexivity |].
  simpl. destruct (pm_next (projT1 i) s); [apply IH | reflexivity].
Qed.

Lemma pgl : forall n s, gl (C:=presented_class) (i:=i) s n = mledger Mp s n.
Proof.
  induction n as [| n IH]; intros s; [reflexivity |].
  simpl. destruct (pm_next (projT1 i) s); [rewrite IH; reflexivity | reflexivity].
Qed.

Lemma glatch_iff : forall n s,
  glatch (C:=presented_class) (i:=i) s n = true <->
  exists m, m <= n /\ T.cs_cert (pm_sys Mp) (gr (C:=presented_class) (i:=i) s m) = true.
Proof.
  induction n as [| n IH]; intros s.
  - simpl. split; [intros H; exists 0; split; [lia | exact H] |].
    intros [m [Hm H]]. replace m with 0 in H by lia. exact H.
  - change (glatch s (S n)) with (glatch s n || gread presented_class i (gr s (S n))).
    rewrite orb_true_iff, IH. split.
    + intros [[m [Hm H]] | H].
      * exists m. split; [lia | exact H].
      * exists (S n). split; [lia | exact H].
    + intros [m [Hm H]]. destruct (Nat.eq_dec m (S n)) as [-> | Hne]; [right; exact H |].
      left. exists m. split; [lia | exact H].
Qed.

Lemma pglat : forall n, glat (C:=presented_class) i n = mlatch Mp (snd (projT2 i)) n.
Proof.
  intros n. apply Bool.eq_true_iff_eq. unfold glat. rewrite glatch_iff, presented_mlatch_iff.
  simpl gstart. split; intros [m [Hm H]]; exists m; (split; [exact Hm |]).
  - rewrite <- pgr. exact H.
  - rewrite pgr. exact H.
Qed.

End Inst.

(* ================================================================= *)
(* (N4) the register host; (N0) neutral-complete; (N3); (N5).         *)
(* ================================================================= *)

Definition pkind (i : @M.pu_instr pu_hprop) : rkind :=
  match i with M.INC r => RInc r | M.DEC r j => RDec r j | M.HALT => RHalt | _ => RRec end.

Definition UP_reg : reg_host UP_host.
Proof.
  refine (mk_rh UP_host (fun s => M.pc (M.core_of s)) (fun s => M.vals (M.core_of s))
            (fun s => M.err (M.core_of s)) pkind _ _ _ _ _ _ _ _).
  - intros [r | r j | | p r | p r | |]; reflexivity.
  - intros s m E. simpl. unfold M.pu_cexec. rewrite E. auto.
  - intros s m r E K. destruct m; simpl in K; try discriminate. injection K as ->.
    simpl. unfold M.pu_cexec. rewrite E. simpl. auto.
  - intros s m r j E K. destruct m; simpl in K; try discriminate. injection K as -> ->.
    simpl. unfold M.pu_cexec. rewrite E. destruct (M.vals (M.core_of s) r); simpl; auto.
  - intros s m K. destruct m; simpl in K; try discriminate.
    simpl. unfold M.pu_cexec. destruct (M.err (M.core_of s)) eqn:E; simpl; repeat split; auto.
  - intros s m E K. simpl. unfold M.pu_cexec. rewrite E.
    destruct m; simpl in K; try discriminate.
    + destruct (M.pu_check_ok pu_heval (M.core_of s) p r); simpl; auto.
    + destruct (M.pu_commit_ok pu_hprop_eqb (M.core_of s) p r); simpl; auto.
    + destruct (M.pu_certify_ok (M.core_of s)); simpl; auto.
    + simpl. auto.
  - intros P s1 s2 E Pc. simpl. unfold M.pu_next_instr. rewrite E, Pc. reflexivity.
  - intros P s E. simpl. unfold M.pu_next_instr. rewrite E. reflexivity.
Defined.

Definition UP_iface : NeutralComplete.neutral_interface (hmach UP_host) :=
  NeutralComplete.neutralize pu_host_interface.

Theorem UP_host_nc : host_nc UP_host UP_reg.
Proof.
  exists UP_iface. split.
  - exact (NeutralComplete.tc_to_nc pu_host_machine pu_host_interface pu_host_thiele_complete_with).
  - intros [r | r j | | p r | p r | |]; reflexivity.
Qed.

Definition UP_raise (l : nat) : bool :=
  match M.pu_fetch U_P l with Some M.CERTIFY => true | _ => false end.

Theorem UP_line_raise : line_raise UP_host UP_reg U_P UP_raise.
Proof.
  intros s m E Hn K. simpl in *. unfold M.pu_next_instr in Hn. rewrite E in Hn.
  unfold UP_raise. destruct (M.pu_fetch U_P (M.pc (M.core_of s))) as [o |] eqn:F; [| discriminate].
  destruct o; try (injection Hn as <-); try discriminate; simpl in K; try discriminate.
  - right. simpl. rewrite orb_false_r. reflexivity.
  - right. simpl. rewrite orb_false_r. reflexivity.
  - unfold M.pu_cexec. rewrite E. simpl. destruct (M.pu_certify_ok (M.core_of s)) eqn:C.
    + right. rewrite orb_true_r. reflexivity.
    + left. reflexivity.
  - right. simpl. rewrite orb_false_r. reflexivity.
Qed.


(* The same for EVERY program on this host: a CERTIFY either raises or traps,
   and nothing else raises.  (N3) is automatic on the certified host. *)
Theorem multi_line_raise : forall P, line_raise UP_host UP_reg P
  (fun l => match M.pu_fetch P l with Some M.CERTIFY => true | _ => false end).
Proof.
  intros P s m E Hn K. simpl in *. unfold M.pu_next_instr in Hn. rewrite E in Hn.
  destruct (M.pu_fetch P (M.pc (M.core_of s))) as [o |] eqn:F; [| discriminate].
  destruct o; try (injection Hn as <-); try discriminate; simpl in K; try discriminate.
  - right. simpl. rewrite orb_false_r. reflexivity.
  - right. simpl. rewrite orb_false_r. reflexivity.
  - unfold M.pu_cexec. rewrite E. simpl. destruct (M.pu_certify_ok (M.core_of s)) eqn:C.
    + right. rewrite orb_true_r. reflexivity.
    + left. reflexivity.
  - right. simpl. rewrite orb_false_r. reflexivity.
Qed.

Lemma UP_clean : clean_template UP_host UP_reg M.pu_start.
Proof. repeat split. Qed.

(* The guest enters only through a register file. *)
Definition UP_code (i : pinst) : nat -> nat :=
  pu_hregs (cg_guest (projT1 i) (fst (projT2 i))) 0
    (pu_guest_b (projT1 i) (fst (projT2 i)) (snd (projT2 i))).

Lemma UP_load : forall i, M.pu_start (UP_code i) =
  pu_host_start (projT1 i) (fst (projT2 i)) (snd (projT2 i)).
Proof. reflexivity. Qed.

Definition UP_dec (i : pinst) (rho : nat -> nat) : option (T.cs_state (pm_sys (projT1 i))) :=
  pu_decode (projT1 i) (rho pu_RB).

(* ================================================================= *)
(* (N1).                                                              *)
(* ================================================================= *)

Theorem UP_halt : forall i,
  halt_clause presented_class UP_host (fun i => option (T.cs_state (pm_sys (projT1 i)))) pobs 3
    U_P (M.pu_start (UP_code i)) i (fun h => UP_dec i (b_reg UP_reg h)).
Proof.
  intros [Mp [pc s0]]. rewrite UP_load. simpl fst; simpl snd; simpl projT1. split.
  - unfold clause1. split.
    + intros [n Hn]. simpl in Hn. rewrite UP_hr in Hn.
      destruct (proj1 (presented_universal_halting Mp pc s0) (ex_intro _ n Hn)) as [m Hm].
      exists m. unfold grun. simpl. rewrite (pgr (existT _ Mp (pc, s0))). exact Hm.
    + intros [m Hm]. unfold grun in Hm. simpl in Hm.
      rewrite (pgr (existT _ Mp (pc, s0))) in Hm.
      destruct (proj2 (presented_universal_halting Mp pc s0) (ex_intro _ m Hm)) as [n Hn].
      exists n. simpl. rewrite UP_hr. exact Hn.
  - intros m0 Hl Hs.
    assert (Hl' : forall k, k < m0 -> pm_next Mp (presented_run Mp s0 k) <> None).
    { intros k Hk. pose proof (Hl k Hk) as X. unfold grun in X. simpl in X.
      rewrite (pgr (existT _ Mp (pc, s0))) in X. exact X. }
    assert (Hs' : pm_next Mp (presented_run Mp s0 m0) = None).
    { unfold grun in Hs. simpl in Hs. rewrite (pgr (existT _ Mp (pc, s0))) in Hs. exact Hs. }
    destruct (presented_universal_halt_point Mp pc s0 m0 Hl' Hs') as (t & Hh & Hd & Hmu & Hc).
    exists t. unfold pu_host_at, pu_hrun in *. fold (pu_host_start Mp pc s0) in Hh, Hd, Hmu, Hc.
    split; [simpl; rewrite UP_hr; exact Hh |].
    pose proof (UP_hl U_P t (pu_host_start Mp pc s0)) as Hh'.
    split; [| split].
    + simpl. rewrite UP_hr. unfold UP_dec. cbn [projT1]. rewrite Hd. unfold pobs, grun. simpl.
      rewrite (pgr (existT _ Mp (pc, s0))). reflexivity.
    + simpl. rewrite UP_hr, Hc. symmetry. apply (pglat (existT _ Mp (pc, s0))).
    + exists (surcharge Mp s0 m0). split; [unfold surcharge; destruct (mlatch Mp s0 m0); lia |].
      unfold gledger. simpl gstart. rewrite (pgl (existT _ Mp (pc, s0))).
      assert (H0 : M.mu (pu_host_start Mp pc s0) = 0) by reflexivity. simpl in *. lia.
Qed.

(* ================================================================= *)
(* The order: finite chains, then one increasing function.            *)
(* ================================================================= *)

(* Host level: along a guest prefix that has not stopped, related host
   times can be chosen strictly increasing. *)
Lemma hchain : forall Q x y N0, ~ E.halted Q (E.core_of (pu_grun Q x y N0)) ->
  exists lh : nat -> nat, (forall k, k < N0 -> lh k < lh (S k)) /\
    forall k, k <= N0 -> exists sg rho, pu_rel_with Q sg rho (pu_grun Q x y k) (pu_hrun Q x y (lh k)).
Proof.
  intros Q x y N0. induction N0 as [| N IH]; intros Hnh.
  (* SAFE: a chain over the single step 0 has nothing to increase;
     time 0 is the load, which is related to the guest's start. *)
  - exists (fun _ => 0). split; [intros; lia |]. intros k Hk. replace k with 0 by lia.
    exists [], None. exact (pu_hload_rel Q x y).
  - assert (Hnh' : ~ E.halted Q (E.core_of (pu_grun Q x y N))).
    { intros Hh. apply Hnh. rewrite (pu_grun_halted_succ Q x y N Hh). exact Hh. }
    destruct (IH Hnh') as (lh & Hinc & Hrel).
    destruct (Hrel N (le_n N)) as (sg & rho & R).
    destruct (pu_U_step_with Q sg rho _ _ R) as [[Hh _] | [_ (d & h' & Hd & [(sg' & rho' & R' & _) | (Herr & _)])]].
    + exfalso. exact (Hnh' Hh).
    + exists (fun k => if Nat.leb k N then lh k else lh N + S d). split.
      * intros k Hk. destruct (Nat.leb k N) eqn:E1; destruct (Nat.leb (S k) N) eqn:E2;
          apply Nat.leb_le in E1 || apply Nat.leb_gt in E1;
          apply Nat.leb_le in E2 || apply Nat.leb_gt in E2; try lia.
        -- apply Hinc. lia.
        -- replace k with N by lia. lia.
      * intros k Hk. destruct (Nat.leb k N) eqn:E1.
        -- apply Nat.leb_le in E1. apply Hrel, E1.
        -- apply Nat.leb_gt in E1. replace k with (S N) by lia.
           exists sg', rho'.
           assert (Hg : pu_grun Q x y (S N) = E.step Q (pu_grun Q x y N))
             by (unfold pu_grun; apply pu_grun_succ).
           assert (Hhh : pu_hrun Q x y (lh N + S d) = h') by (rewrite pu_hrun_add; exact Hd).
           rewrite Hg, Hhh. exact R'.
    + exfalso. apply Hnh.
      assert (Hg : pu_grun Q x y (S N) = E.step Q (pu_grun Q x y N))
        by (unfold pu_grun; apply pu_grun_succ).
      rewrite Hg. unfold E.halted, P.pr_halted, P.pr_next_instr. rewrite Herr. reflexivity.
Qed.

Section Presented.
Variable Mp : presented_machine.
Variable pc : cg_presentation Mp.
Variable s0 : T.cs_state (pm_sys Mp).

Local Notation Yrun N := (P.pr_run_prog cg_uprop_eqb cg_ueval N (cg_guest Mp pc) (cg_ystart Mp pc s0)).

(* Compiled-guest level, the order kept in cg_y_head's induction. *)
Lemma ychain : forall n0, (forall m, m < n0 -> pm_next Mp (presented_run Mp s0 m) <> None) ->
  exists lg : nat -> nat, (forall k, k < n0 -> lg k < lg (S k)) /\
    forall k, k <= n0 -> cg_ypoint Mp pc s0 k (lg k).
Proof.
  induction n0 as [| n IH]; intros Hn.
  - destruct (cg_x_prologue Mp pc s0) as (x & Hinv & Hx).
    destruct (cg_y_phase Mp pc 1 _ 2 x _ Hx (cg_ystart_simul Mp pc s0)
                (eq_sym (cg_link_start (1, cg_SRC Mp pc) 1)))
      as (q & w & _ & Hrun & Hpc & Hsim).
    exists (fun _ => q). split; [intros; lia |]. intros k Hk. replace k with 0 by lia.
    exists x. rewrite Hrun. auto.
  - destruct (IH (fun m Hm => Hn m ltac:(lia))) as (lg & Hinc & Hp).
    destruct (Hp n (le_n n)) as (x & Hinv & Hpc & Hsim).
    destruct (pm_next Mp (presented_run Mp s0 n)) as [i |] eqn:E;
      [| exfalso; exact (Hn n ltac:(lia) E)].
    destruct (cg_x_step Mp pc s0 n x i Hinv E) as (x' & Hinv' & Hx).
    destruct (cg_y_phase Mp pc 2 x 2 x' _ Hx Hsim Hpc) as (q & w & Hq & Hrun & Hpc' & Hsim').
    exists (fun k => if Nat.leb k n then lg k else lg n + q). split.
    + intros k Hk. destruct (Nat.leb k n) eqn:E1; destruct (Nat.leb (S k) n) eqn:E2;
        apply Nat.leb_le in E1 || apply Nat.leb_gt in E1;
        apply Nat.leb_le in E2 || apply Nat.leb_gt in E2; try lia.
      * apply Hinc. lia.
      * replace k with n by lia. lia.
    + intros k Hk. destruct (Nat.leb k n) eqn:E1.
      * apply Nat.leb_le in E1. apply Hp, E1.
      * apply Nat.leb_gt in E1. replace k with (S n) by lia.
        exists x'. rewrite cg_run_prog_add, Hrun. auto.
Qed.

Lemma cg_point_code : forall n N, cg_ypoint Mp pc s0 n N ->
  cg_expo (qs 0) (G.cb (G.core_of (Yrun N))) = pm_scode Mp (presented_run Mp s0 n).
Proof.
  intros n N ([e a] & [He Ha] & _ & Hsim). cbn [fst snd] in He, Ha. subst a.
  destruct Hsim as (H1 & H2 & H3 & _). rewrite H2, cg_expo_gk_zero by exact H3. rewrite He. reflexivity.
Qed.

(* The decidable matching predicate at the presented level. *)
Definition Dp (n t : nat) : Prop :=
  cg_expo (qs 0) (hv (pu_host_at Mp pc s0 t) pu_RB) = pm_scode Mp (presented_run Mp s0 n) /\
  M.mu (pu_host_at Mp pc s0 t) = mledger Mp s0 n + surcharge Mp s0 n /\
  M.cert (pu_host_at Mp pc s0 t) = mlatch Mp s0 n /\
  M.err (M.core_of (pu_host_at Mp pc s0 t)) = false.

Lemma Dp_dec : forall n t, {Dp n t} + {~ Dp n t}.
Proof.
  intros n t. unfold Dp.
  destruct (Nat.eq_dec (cg_expo (qs 0) (hv (pu_host_at Mp pc s0 t) pu_RB)) (pm_scode Mp (presented_run Mp s0 n)));
    [| right; tauto].
  destruct (Nat.eq_dec (M.mu (pu_host_at Mp pc s0 t)) (mledger Mp s0 n + surcharge Mp s0 n)); [| right; tauto].
  destruct (Bool.bool_dec (M.cert (pu_host_at Mp pc s0 t)) (mlatch Mp s0 n)); [| right; tauto].
  destruct (Bool.bool_dec (M.err (M.core_of (pu_host_at Mp pc s0 t))) false); [left; auto | right; tauto].
Defined.

Definition Lp (n : nat) : Prop := forall m, m < n -> pm_next Mp (presented_run Mp s0 m) <> None.

Lemma Lp_dec : forall n, {Lp n} + {~ Lp n}.
Proof.
  intros n. induction n as [| n IH].
  - left. intros m Hm. lia.
  - destruct IH as [Hl | Hl].
    + destruct (pm_next Mp (presented_run Mp s0 n)) eqn:E.
      * left. intros m Hm. destruct (Nat.eq_dec m n) as [-> | Hne]; [rewrite E; discriminate |].
        apply Hl. lia.
      * right. intros Hl'. exact (Hl' n ltac:(lia) E).
    + right. intros Hl'. apply Hl. intros m Hm. apply Hl'. lia.
Defined.

Lemma pchains : forall n0, Lp n0 -> exists l : nat -> nat,
  (forall k, k < n0 -> l k < l (S k)) /\ (forall k, k <= n0 -> Dp k (l k)).
Proof.
  intros n0 Hl. destruct (ychain n0 Hl) as (lg & Hg & Hyp).
  set (Q := cg_guest Mp pc). set (b := pu_guest_b Mp pc s0).
  assert (Hnh : ~ E.halted Q (E.core_of (pu_grun Q 0 b (lg n0)))).
  { exact (cg_point_live Mp pc s0 n0 (lg n0) (Hyp n0 (le_n n0))). }
  destruct (hchain Q 0 b (lg n0) Hnh) as (lh & Hh & Hrel).
  assert (Hmono : forall a c, a <= c -> c <= n0 -> lg a <= lg c).
  { intros a c Hac Hc. induction c as [| c IHc]; [replace a with 0 by lia; lia |].
    destruct (Nat.eq_dec a (S c)) as [-> | Hne]; [lia |].
    pose proof (Hg c ltac:(lia)). pose proof (IHc ltac:(lia) ltac:(lia)). lia. }
  assert (Hhmono : forall a c, a < c -> c <= lg n0 -> lh a < lh c).
  { intros a c Hac Hc. induction c as [| c IHc]; [lia |].
    destruct (Nat.eq_dec a c) as [-> | Hne]; [apply Hh; lia |].
    pose proof (Hh c ltac:(lia)). pose proof (IHc ltac:(lia) ltac:(lia)). lia. }
  exists (fun k => lh (lg k)). split.
  - intros k Hk. apply Hhmono; [apply Hg, Hk |]. apply Hmono; lia.
  - intros k Hk. pose proof (Hyp k Hk) as Yp.
    destruct (Hrel (lg k) (Hmono k n0 Hk (le_n n0))) as (sg & rho & R).
    destruct (cg_point_facts Mp pc s0 k (lg k) Yp) as (_ & _ & _ & Hmu & Hc & _).
    pose proof (cg_point_code k (lg k) Yp) as Hcode.
    unfold Dp, pu_host_at. fold Q b.
    rewrite (pu_R_rb Q sg rho _ _ R), (pu_rw_mu _ _ _ _ _ R), (pu_rw_cert _ _ _ _ _ R).
    split; [exact Hcode |]. split; [exact Hmu |]. split; [exact Hc |].
    destruct (pu_rw_head _ _ _ _ _ R) as (_ & Herr & _). exact Herr.
Qed.

Theorem UP_presented_order : exists f : nat -> nat,
  (forall n, Lp (S n) -> f n < f (S n)) /\ (forall n, Lp n -> Dp n (f n)).
Proof.
  apply (chains_to_fun Dp Dp_dec Lp Lp_dec).
  - intros m Hl k Hk. apply Hl. lia.
  - exact pchains.
Qed.

End Presented.

Theorem UP_in_order : forall i, exists f,
  in_order presented_class UP_host (fun i => option (T.cs_state (pm_sys (projT1 i)))) pobs 3
    U_P (M.pu_start (UP_code i)) i (fun h => UP_dec i (b_reg UP_reg h)) f.
Proof.
  intros [Mp [pc s0]]. destruct (UP_presented_order Mp pc s0) as (f & Hinc & HD).
  assert (Hl : forall n, live_before (C:=presented_class) (existT _ Mp (pc, s0)) n -> Lp Mp s0 n).
  { intros n Hn k Hk. pose proof (Hn k Hk) as X. unfold grun in X. simpl in X.
    rewrite (pgr (existT _ Mp (pc, s0))) in X. exact X. }
  exists f. split.
  - intros m Hm. apply Hinc, Hl, Hm.
  - intros m Hm. destruct (HD m (Hl m Hm)) as (Hcode & Hmu & Hc & _).
    rewrite UP_load. simpl fst; simpl snd; simpl projT1.
    unfold pu_host_at, pu_hrun in Hcode, Hmu, Hc. fold (pu_host_start Mp pc s0) in Hcode, Hmu, Hc.
    pose proof (UP_hl U_P (f m) (pu_host_start Mp pc s0)) as Hh.
    split; [| split].
    + simpl. rewrite UP_hr. unfold UP_dec, pu_decode. cbn [projT1]. rewrite Hcode, pm_sdec_scode.
      unfold pobs, grun. simpl. rewrite (pgr (existT _ Mp (pc, s0))). reflexivity.
    + simpl. rewrite UP_hr, Hc. symmetry. apply (pglat (existT _ Mp (pc, s0))).
    + exists (surcharge Mp s0 m). split; [unfold surcharge; destruct (mlatch Mp s0 m); lia |].
      unfold gledger. simpl gstart. rewrite (pgl (existT _ Mp (pc, s0))).
      assert (H0 : M.mu (pu_host_start Mp pc s0) = 0) by reflexivity. simpl in *. lia.
Qed.

Theorem UP_neutral_universal :
  neutral_universal presented_class UP_host (fun i => option (T.cs_state (pm_sys (projT1 i)))) pobs 3.
Proof.
  exists U_P, UP_reg, UP_raise, M.pu_start, UP_code, UP_dec.
  split; [exact UP_host_nc |]. split; [exact UP_line_raise |]. split; [exact UP_clean |].
  intros i. split; [apply UP_halt | apply UP_in_order].
Qed.

Print Assumptions UP_host_nc.
Print Assumptions UP_line_raise.
Print Assumptions multi_line_raise.
Print Assumptions UP_halt.
Print Assumptions hchain.
Print Assumptions ychain.
Print Assumptions UP_in_order.
Print Assumptions UP_neutral_universal.
