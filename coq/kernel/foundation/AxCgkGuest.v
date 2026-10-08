(** AxCgkGuest: the guest of a chain machine, as a source program, and its
    phases in the source language X with a record that can be earned many
    times.

    A chain machine (AxChain.v) has a height h; level j is reached when
    j <= h s.  Its presentation gives the driver, the step and the cost as in
    the compiler of the repository (CompilerGuest.v), and the reading as one
    recursive algorithm of two inputs, a state code and a level.

    How this file was made: it was derived from CompilerGuest.v by a text
    transformation, once. The subroutines, the move and the generic facts are
    kept (names changed from cg_ to cgk_); the section header, the layout of
    the check, the check itself, the phases that follow the move and the
    invariant are replaced by their chain versions, and the compiler's
    presentation is replaced by the chain presentation of AxChain.v. The
    result is the file you are reading and is checked as it stands; nothing
    is generated at build time.

    The source program is that of CompilerGuest.v up to the end of the move
    (NEXT, STEP, COST, the clean-up, the jump to CHK), and a different check:

      CHK     register 7 (the latched height m) moves to register 1 and goes
              up by one: register 1 is the level asked about;
      LOOP    erase T; READ counted in T, which puts 1 in B when the level in
              register 1 is at most the height of the state, else 0;
              DEC B EXIT: with B = 0 leave;
              XEARN: earn this level (the fixed checker re-runs the routine on
              the registers, with the level in register 1);
              INC 1: the next level; DEC C three times: the earned level pays
              3 out of the cost of the move; jump to LOOP;
      EXIT    DEC 1; register 1 moves back into register 7: it is the new
              latched height;
      NORAISE erase T; pay what is left of C; back to HEAD.
      HALTB   XHALT.

    Phases proved in X (all for a chain machine whose heights are at most 16,
    so the fact table, which holds 16, is never full when a level is earned):

      ax_cgk_x_prologue   from address 1 to HEAD with the invariant at 0;
      ax_cgk_x_step       from HEAD with the invariant at n, when the driver
                       moves, to HEAD with the invariant at n + 1;
      ax_cgk_x_stop       from HEAD, when the driver halts, to HALTB;
      ax_cgk_x_loop       the loop: it earns exactly the levels from the latched
                       height up to the height of the state;
      ax_cgk_x_check      the whole check of one state.

    The invariant at HEAD after n driven steps: S holds the code of the state
    after n steps, E the latched height, every other register 0; the record is
    (ax_cm_gledger, flag up exactly when the latched height is positive, the
    earned count the latched height). *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is part of the compiler pipeline for chain machines, built on the
   repository's compiler files (CompilerGuest.v and the files it uses). The
   statements that connect it to the axis and to the host that runs the chain
   are AxCgkAxis.v and AxCgkHost.v. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Undecidability.Shared.Libs.DLW Require Import utils pos vec subcode sss.
From Undecidability.FRACTRAN.Util Require Import prime_seq.
From Undecidability.MinskyMachines Require Import MM.
From Undecidability.MinskyMachines.MMenv Require Import env mme_defs mme_utils.
Require Undecidability.MuRec.Util.recalg Undecidability.MuRec.Util.ra_mm_env.
Module RA := Undecidability.MuRec.Util.ra_mm_env.
Require Minimal.EarnedGeneric Minimal.EarnedPriced Minimal.ThieleComplete.
Module G := Minimal.EarnedGeneric.
Module P := Minimal.EarnedPriced.
Module T := Minimal.ThieleComplete.
Require Import Kernel.CompilerCodes Kernel.CompilerChecker Kernel.CompilerInstrument
  Kernel.CompilerLifts.
From Kernel Require Import AxChain AxCgkLang.

(* ================================================================= *)
(* Generic facts.                                                      *)
(* ================================================================= *)

Definition ax_cgk_maxreg (l : list (mm_instr nat)) : nat :=
  fold_right (fun J m => max (cg_reg_of J) m) 0 l.

Lemma ax_cgk_maxreg_in : forall l J, In J l -> cg_reg_of J <= ax_cgk_maxreg l.
Proof.
  induction l as [| J' l IH]; intros J H; [destruct H |].
  destruct H as [-> | H]; simpl; [lia |]. specialize (IH J H). lia.
Qed.

Definition ax_cgk_xmax (l : list cg_xinstr) : nat :=
  fold_right (fun J m => max (match J with XMM J0 => cg_reg_of J0 | _ => 0 end) m) 0 l.

Lemma ax_cgk_xmax_in : forall l J, In (XMM J) l -> cg_reg_of J <= ax_cgk_xmax l.
Proof.
  induction l as [| J' l IH]; intros J H; [destruct H |].
  destruct H as [-> | H]; simpl; [lia |]. specialize (IH J H). lia.
Qed.

Lemma ax_cgk_sc_cons : forall (X : Type) (Pc : nat * list X) n x l,
  Pc <sc (S n, l) -> Pc <sc (n, x :: l).
Proof. intros X Pc n x l H. apply subcode_cons. exact H. Qed.

Lemma ax_cgk_sc_app : forall (X : Type) (Pc : nat * list X) n l r,
  Pc <sc (n + length l, r) -> Pc <sc (n, l ++ r).
Proof.
  intros X [a q] n l r (l1 & r1 & H1 & H2). exists (l ++ l1), r1. split.
  - rewrite H1, app_assoc. reflexivity.
  - rewrite app_length. lia.
Qed.

Lemma ax_cgk_sc_here1 : forall (X : Type) a n (x : X) l, a = n -> (a, [x]) <sc (n, x :: l).
Proof. intros X a n x l ->. exists [], l. split; [reflexivity | simpl; lia]. Qed.

Lemma ax_cgk_sc_here : forall (X : Type) a n (l r : list X), a = n -> (a, l) <sc (n, l ++ r).
Proof. intros X a n l r ->. apply subcode_left. reflexivity. Qed.

Lemma ax_cgk_sc_in : forall (X : Type) a (l : list X) n L x, (a, l) <sc (n, L) -> In x l -> In x L.
Proof.
  intros X a l n L x (l1 & r1 & -> & _) H. apply in_or_app. right. apply in_or_app. left. exact H.
Qed.

Lemma ax_cgk_set_rf : forall (w w' : env nat nat) (f g : nat -> nat) o v,
  (forall y, w y = f y) ->
  (forall y, w' y = set_env eq_nat_dec w o v y) ->
  g o = v -> (forall y, y <> o -> g y = f y) ->
  forall y, w' y = g y.
Proof.
  intros w w' f g o v Hw Hw' Ho Hn y. rewrite Hw'. unfold set_env.
  destruct (eq_nat_dec o y) as [<- | Hne]; [symmetry; exact Ho |].
  rewrite Hn by auto. apply Hw.
Qed.

Section Guest.

Variable C : ax_chain_mach.
Variable cp : ax_chain_pres C.

Local Notation st := (ax_cm_st C).
Local Notation mv := (ax_cm_mv C).
Local Notation cstep := (ax_cm_step C).
Local Notation ccost := (ax_cm_cost C).
Local Notation hh := (ax_cm_h C).
Local Notation next := (ax_cm_next C).
Local Notation sc := (ax_cm_scode C).
Local Notation ic := (ax_cm_icode C).

(* ================================================================= *)
(* The subroutines and the layout.                                     *)
(* ================================================================= *)

(* NEXT at HEAD = 2: input S = 0, answer H = 2. *)
Definition ax_cgk_Pn : list (mm_instr nat) :=
  proj1_sig (@RA.ra_compiler 1 (ax_cp_next_ra C cp) 2 0 2 16 ltac:(lia) ltac:(lia) ltac:(lia)).

Lemma ax_cgk_Pn_spec : RA.ra_compiled (ax_cp_next_ra C cp) 2 0 2 16 ax_cgk_Pn.
Proof. unfold ax_cgk_Pn. exact (proj2_sig _). Qed.

Definition ax_cgk_a_step : nat := 6 + length ax_cgk_Pn.

(* STEP: inputs S = 0 and I = 1, answer S' = 4. *)
Definition ax_cgk_Ps : list (mm_instr nat) :=
  proj1_sig (@RA.ra_compiler 2 (ax_cp_step_ra C cp) ax_cgk_a_step 0 4 16 ltac:(lia) ltac:(lia) ltac:(lia)).

Lemma ax_cgk_Ps_spec : RA.ra_compiled (ax_cp_step_ra C cp) ax_cgk_a_step 0 4 16 ax_cgk_Ps.
Proof. unfold ax_cgk_Ps. exact (proj2_sig _). Qed.

(* SAFE: a code address in the compiled guest (the address after the STEP
   block), not a price. *)
Definition ax_cgk_a_cost : nat := ax_cgk_a_step + length ax_cgk_Ps.

(* COST: input I = 1, answer C = 3. *)
Definition ax_cgk_Pc : list (mm_instr nat) :=
  proj1_sig (@RA.ra_compiler 1 (ax_cp_cost_ra C cp) ax_cgk_a_cost 1 3 16 ltac:(lia) ltac:(lia) ltac:(lia)).

Lemma ax_cgk_Pc_spec : RA.ra_compiled (ax_cp_cost_ra C cp) ax_cgk_a_cost 1 3 16 ax_cgk_Pc.
Proof. unfold ax_cgk_Pc. exact (proj2_sig _). Qed.

Definition ax_cgk_a_erI : nat := ax_cgk_a_cost + length ax_cgk_Pc.
Definition ax_cgk_CHK : nat := ax_cgk_a_erI + 8.
Definition ax_cgk_LOOP : nat := ax_cgk_CHK + 4.
Definition ax_cgk_a_read : nat := ax_cgk_LOOP + 2.

(* READ, at its own address 0: inputs S = 0 and the level in register 1,
   answer B = 5. *)
(* SAFE: the code address 0 of the READ block, not an unset quantity. *)
Definition ax_cgk_ig : nat := 0.

Definition ax_cgk_Pr : list (mm_instr nat) :=
  proj1_sig (@RA.ra_compiler 2 (ax_cp_read_ra C cp) ax_cgk_ig 0 5 16 ltac:(lia) ltac:(lia) ltac:(lia)).

Lemma ax_cgk_Pr_spec : RA.ra_compiled (ax_cp_read_ra C cp) ax_cgk_ig 0 5 16 ax_cgk_Pr.
Proof. unfold ax_cgk_Pr. exact (proj2_sig _). Qed.

(* The counting register: above 16 and above every register READ names. *)
Definition ax_cgk_T : nat := 16 + ax_cgk_maxreg ax_cgk_Pr.

Lemma ax_cgk_T_ge : 16 <= ax_cgk_T.
Proof. unfold ax_cgk_T. lia. Qed.

Lemma ax_cgk_T_fresh : cg_fresh ax_cgk_T ax_cgk_Pr.
Proof.
  intros J HJ. generalize (ax_cgk_maxreg_in ax_cgk_Pr J HJ). unfold ax_cgk_T. lia.
Qed.

Definition ax_cgk_a_tail : nat := ax_cgk_a_read + 2 * length ax_cgk_Pr.
Definition ax_cgk_EXIT : nat := ax_cgk_a_tail + 7.
Definition ax_cgk_NORAISE : nat := ax_cgk_a_tail + 11.
Definition ax_cgk_PL : nat := ax_cgk_a_tail + 13.
Definition ax_cgk_HALTB : nat := ax_cgk_a_tail + 16.

Definition ax_cgk_SRC : list cg_xinstr :=
  XMM (mm_dec 8 ax_cgk_CHK) ::
  map XMM ax_cgk_Pn ++
  XMM (mm_dec 2 ax_cgk_HALTB) ::
  map XMM (mm_transfert 2 1 8 (3 + length ax_cgk_Pn)) ++
  map XMM ax_cgk_Ps ++
  map XMM ax_cgk_Pc ++
  map XMM (mm_erase 1 8 ax_cgk_a_erI) ++
  map XMM (mm_erase 0 8 (ax_cgk_a_erI + 2)) ++
  map XMM (mm_transfert 4 0 8 (ax_cgk_a_erI + 4)) ++
  XMM (mm_dec 8 ax_cgk_CHK) ::
  map XMM (mm_transfert 7 1 8 ax_cgk_CHK) ++
  XMM (mm_inc 1) ::
  map XMM (mm_erase ax_cgk_T 8 ax_cgk_LOOP) ++
  map XMM (cg_count_code ax_cgk_T ax_cgk_Pr ax_cgk_ig ax_cgk_a_read) ++
  XMM (mm_dec 5 ax_cgk_EXIT) :: XEARN :: XMM (mm_inc 1) ::
  XMM (mm_dec 3 (ax_cgk_a_tail + 4)) :: XMM (mm_dec 3 (ax_cgk_a_tail + 5)) ::
  XMM (mm_dec 3 (ax_cgk_a_tail + 6)) ::
  XMM (mm_dec 8 ax_cgk_LOOP) ::
  XMM (mm_dec 1 (ax_cgk_a_tail + 8)) ::
  map XMM (mm_transfert 1 7 8 (ax_cgk_a_tail + 8)) ++
  map XMM (mm_erase ax_cgk_T 8 ax_cgk_NORAISE) ++
  XMM (mm_dec 3 2) :: XPAY :: XMM (mm_dec 8 ax_cgk_PL) :: XHALT :: [].

(* Registers below k are coded; every register the program names is below k. *)
Definition ax_cgk_k : nat := S (ax_cgk_xmax ax_cgk_SRC).

(* The code of the reading routine for the fixed checker. *)
Definition ax_cgk_r : nat := cg_renc ax_cgk_ig ax_cgk_Pr 0 5 ax_cgk_T 16.

Local Notation X := (ax_cgk_xstep ax_cgk_k ax_cgk_r).
Local Notation Xc := (sss_compute X (1, ax_cgk_SRC)).
Local Notation Xp := (sss_progress X (1, ax_cgk_SRC)).

Lemma ax_cgk_src_reg : forall J, In (XMM J) ax_cgk_SRC -> cg_xreg J < ax_cgk_k.
Proof.
  intros J H. unfold ax_cgk_k. generalize (ax_cgk_xmax_in ax_cgk_SRC J H).
  destruct J; simpl; lia.
Qed.

(* ================================================================= *)
(* Locating the blocks.                                                *)
(* ================================================================= *)

Ltac ax_cgk_addr :=
  unfold ax_cgk_HALTB, ax_cgk_PL, ax_cgk_NORAISE, ax_cgk_EXIT, ax_cgk_a_tail, ax_cgk_a_read, ax_cgk_LOOP, ax_cgk_CHK, ax_cgk_a_erI,
    ax_cgk_a_cost, ax_cgk_a_step;
  rewrite ?app_length, ?map_length, ?mm_transfert_length, ?mm_erase_length,
    ?cg_count_code_length; cbn [length]; lia.

Ltac ax_cgk_sc :=
  match goal with
  | |- (_, [?x]) <sc (_, ?x :: _) =>
      (apply ax_cgk_sc_here1; ax_cgk_addr) || (apply ax_cgk_sc_cons; ax_cgk_sc)
  | |- (_, ?l) <sc (_, ?l ++ _) =>
      (apply ax_cgk_sc_here; ax_cgk_addr) || (apply ax_cgk_sc_app; ax_cgk_sc)
  | |- _ <sc (_, _ :: _) => apply ax_cgk_sc_cons; ax_cgk_sc
  | |- _ <sc (_, _ ++ _) => apply ax_cgk_sc_app; ax_cgk_sc
  end.

Lemma ax_cgk_sc_jmp0 : (1, [XMM (mm_dec 8 ax_cgk_CHK)]) <sc (1, ax_cgk_SRC).
Proof. unfold ax_cgk_SRC. ax_cgk_sc. Qed.
Lemma ax_cgk_sc_next : (2, map XMM ax_cgk_Pn) <sc (1, ax_cgk_SRC).
Proof. unfold ax_cgk_SRC. ax_cgk_sc. Qed.
Lemma ax_cgk_sc_dech : (2 + length ax_cgk_Pn, [XMM (mm_dec 2 ax_cgk_HALTB)]) <sc (1, ax_cgk_SRC).
Proof. unfold ax_cgk_SRC. ax_cgk_sc. Qed.
Lemma ax_cgk_sc_tr1 :
  (3 + length ax_cgk_Pn, map XMM (mm_transfert 2 1 8 (3 + length ax_cgk_Pn))) <sc (1, ax_cgk_SRC).
Proof. unfold ax_cgk_SRC. ax_cgk_sc. Qed.
Lemma ax_cgk_sc_step : (ax_cgk_a_step, map XMM ax_cgk_Ps) <sc (1, ax_cgk_SRC).
Proof. unfold ax_cgk_SRC. ax_cgk_sc. Qed.
Lemma ax_cgk_sc_cost : (ax_cgk_a_cost, map XMM ax_cgk_Pc) <sc (1, ax_cgk_SRC).
Proof. unfold ax_cgk_SRC. ax_cgk_sc. Qed.
Lemma ax_cgk_sc_erI : (ax_cgk_a_erI, map XMM (mm_erase 1 8 ax_cgk_a_erI)) <sc (1, ax_cgk_SRC).
Proof. unfold ax_cgk_SRC. ax_cgk_sc. Qed.
Lemma ax_cgk_sc_erS : (ax_cgk_a_erI + 2, map XMM (mm_erase 0 8 (ax_cgk_a_erI + 2))) <sc (1, ax_cgk_SRC).
Proof. unfold ax_cgk_SRC. ax_cgk_sc. Qed.
Lemma ax_cgk_sc_tr2 : (ax_cgk_a_erI + 4, map XMM (mm_transfert 4 0 8 (ax_cgk_a_erI + 4))) <sc (1, ax_cgk_SRC).
Proof. unfold ax_cgk_SRC. ax_cgk_sc. Qed.
Lemma ax_cgk_sc_jmp1 : (ax_cgk_a_erI + 7, [XMM (mm_dec 8 ax_cgk_CHK)]) <sc (1, ax_cgk_SRC).
Proof. unfold ax_cgk_SRC. ax_cgk_sc. Qed.
Lemma ax_cgk_sc_trE : (ax_cgk_CHK, map XMM (mm_transfert 7 1 8 ax_cgk_CHK)) <sc (1, ax_cgk_SRC).
Proof. unfold ax_cgk_SRC. ax_cgk_sc. Qed.
Lemma ax_cgk_sc_incI0 : (ax_cgk_CHK + 3, [XMM (mm_inc 1)]) <sc (1, ax_cgk_SRC).
Proof. unfold ax_cgk_SRC. ax_cgk_sc. Qed.
Lemma ax_cgk_sc_erT : (ax_cgk_LOOP, map XMM (mm_erase ax_cgk_T 8 ax_cgk_LOOP)) <sc (1, ax_cgk_SRC).
Proof. unfold ax_cgk_SRC. ax_cgk_sc. Qed.
Lemma ax_cgk_sc_read :
  (ax_cgk_a_read, map XMM (cg_count_code ax_cgk_T ax_cgk_Pr ax_cgk_ig ax_cgk_a_read)) <sc (1, ax_cgk_SRC).
Proof. unfold ax_cgk_SRC. ax_cgk_sc. Qed.
Lemma ax_cgk_sc_decB : (ax_cgk_a_tail, [XMM (mm_dec 5 ax_cgk_EXIT)]) <sc (1, ax_cgk_SRC).
Proof. unfold ax_cgk_SRC. ax_cgk_sc. Qed.
Lemma ax_cgk_sc_earn : (ax_cgk_a_tail + 1, [XEARN]) <sc (1, ax_cgk_SRC).
Proof. unfold ax_cgk_SRC. ax_cgk_sc. Qed.
Lemma ax_cgk_sc_incI : (ax_cgk_a_tail + 2, [XMM (mm_inc 1)]) <sc (1, ax_cgk_SRC).
Proof. unfold ax_cgk_SRC. ax_cgk_sc. Qed.
Lemma ax_cgk_sc_decC1 : (ax_cgk_a_tail + 3, [XMM (mm_dec 3 (ax_cgk_a_tail + 4))]) <sc (1, ax_cgk_SRC).
Proof. unfold ax_cgk_SRC. ax_cgk_sc. Qed.
Lemma ax_cgk_sc_decC2 : (ax_cgk_a_tail + 4, [XMM (mm_dec 3 (ax_cgk_a_tail + 5))]) <sc (1, ax_cgk_SRC).
Proof. unfold ax_cgk_SRC. ax_cgk_sc. Qed.
Lemma ax_cgk_sc_decC3 : (ax_cgk_a_tail + 5, [XMM (mm_dec 3 (ax_cgk_a_tail + 6))]) <sc (1, ax_cgk_SRC).
Proof. unfold ax_cgk_SRC. ax_cgk_sc. Qed.
Lemma ax_cgk_sc_jmpL : (ax_cgk_a_tail + 6, [XMM (mm_dec 8 ax_cgk_LOOP)]) <sc (1, ax_cgk_SRC).
Proof. unfold ax_cgk_SRC. ax_cgk_sc. Qed.
Lemma ax_cgk_sc_decI : (ax_cgk_EXIT, [XMM (mm_dec 1 (ax_cgk_a_tail + 8))]) <sc (1, ax_cgk_SRC).
Proof. unfold ax_cgk_SRC. ax_cgk_sc. Qed.
Lemma ax_cgk_sc_trX : (ax_cgk_a_tail + 8, map XMM (mm_transfert 1 7 8 (ax_cgk_a_tail + 8))) <sc (1, ax_cgk_SRC).
Proof. unfold ax_cgk_SRC. ax_cgk_sc. Qed.
Lemma ax_cgk_sc_erT2 : (ax_cgk_NORAISE, map XMM (mm_erase ax_cgk_T 8 ax_cgk_NORAISE)) <sc (1, ax_cgk_SRC).
Proof. unfold ax_cgk_SRC. ax_cgk_sc. Qed.
Lemma ax_cgk_sc_pl : (ax_cgk_PL, [XMM (mm_dec 3 2)]) <sc (1, ax_cgk_SRC).
Proof. unfold ax_cgk_SRC. ax_cgk_sc. Qed.
Lemma ax_cgk_sc_pay : (ax_cgk_PL + 1, [XPAY]) <sc (1, ax_cgk_SRC).
Proof. unfold ax_cgk_SRC. ax_cgk_sc. Qed.
Lemma ax_cgk_sc_jmp3 : (ax_cgk_PL + 2, [XMM (mm_dec 8 ax_cgk_PL)]) <sc (1, ax_cgk_SRC).
Proof. unfold ax_cgk_SRC. ax_cgk_sc. Qed.
Lemma ax_cgk_sc_halt : (ax_cgk_HALTB, [XHALT]) <sc (1, ax_cgk_SRC).
Proof. unfold ax_cgk_SRC. ax_cgk_sc. Qed.

Lemma ax_cgk_k_gt : 8 < ax_cgk_k /\ ax_cgk_T < ax_cgk_k.
Proof.
  split.
  - apply (ax_cgk_src_reg (mm_dec 8 ax_cgk_CHK)). eapply ax_cgk_sc_in; [exact ax_cgk_sc_jmp0 | left; reflexivity].
  - apply (ax_cgk_src_reg (mm_dec ax_cgk_T (2 + ax_cgk_LOOP))).
    eapply ax_cgk_sc_in; [exact ax_cgk_sc_erT | left; reflexivity].
Qed.

(* ================================================================= *)
(* Register files.                                                     *)
(* ================================================================= *)

Definition ax_cgk_rf (vS vI vH vC vS' vB vE vT : nat) (y : nat) : nat :=
  if Nat.eqb y 0 then vS else if Nat.eqb y 1 then vI else
  if Nat.eqb y 2 then vH else if Nat.eqb y 3 then vC else
  if Nat.eqb y 4 then vS' else if Nat.eqb y 5 then vB else
  if Nat.eqb y 7 then vE else if Nat.eqb y ax_cgk_T then vT else 0.

Ltac ax_cgk_rf_tac :=
  generalize ax_cgk_T_ge; generalize ax_cgk_k_gt; unfold ax_cgk_rf;
  repeat (match goal with |- context [Nat.eqb ?a ?b] => destruct (Nat.eqb_spec a b) end;
          cbv beta iota);
  intros; first [reflexivity | lia].

Lemma ax_cgk_rf_high : forall vS vI vH vC vS' vB vE vT y,
  ax_cgk_k <= y -> ax_cgk_rf vS vI vH vC vS' vB vE vT y = 0.
Proof. intros. ax_cgk_rf_tac. Qed.

Lemma ax_cgk_rf_spare : forall vS vI vH vC vS' vB vE y,
  16 <= y -> ax_cgk_rf vS vI vH vC vS' vB vE 0 y = 0.
Proof. intros. ax_cgk_rf_tac. Qed.

Definition ax_cgk_eqv (e : env nat nat) (f : nat -> nat) : Prop := forall y, e y = f y.

Lemma ax_cgk_eqv_zero_high : forall e vS vI vH vC vS' vB vE vT,
  ax_cgk_eqv e (ax_cgk_rf vS vI vH vC vS' vB vE vT) -> forall y, ax_cgk_k <= y -> e y = 0.
Proof. intros e vS vI vH vC vS' vB vE vT H y Hy. rewrite H. apply ax_cgk_rf_high. exact Hy. Qed.

Lemma ax_cgk_eqv_spare : forall e vS vI vH vC vS' vB vE,
  ax_cgk_eqv e (ax_cgk_rf vS vI vH vC vS' vB vE 0) -> forall y, 16 <= y -> get_env e y = 0.
Proof. intros e vS vI vH vC vS' vB vE H y Hy. apply (eq_trans (H y)). apply ax_cgk_rf_spare. exact Hy. Qed.

(* Setting one register of a register file. *)
Ltac ax_cgk_set He He' :=
  apply (ax_cgk_set_rf _ _ _ _ _ _ He He'); [ax_cgk_rf_tac | intros; ax_cgk_rf_tac].

(* Reading one register of a register file. *)
Ltac ax_cgk_get He := rewrite ?cg_get_env, He; ax_cgk_rf_tac.

(* Inputs of one-input and two-input routines. *)
Lemma ax_cgk_in1 : forall (e : env nat nat) p x,
  e p = x -> forall q : pos 1, get_env e (pos2nat q + p) = vec_pos (x ## vec_nil) q.
Proof.
  intros e p x H q. invert pos q; [rewrite pos2nat_fst; exact H | invert pos q].
Qed.

Lemma ax_cgk_in2 : forall (e : env nat nat) x y,
  e 0 = x -> e 1 = y -> forall q : pos 2, get_env e (pos2nat q + 0) = vec_pos (x ## y ## vec_nil) q.
Proof.
  intros e x y H0 H1 q. invert pos q; [rewrite pos2nat_fst; exact H0 |].
  invert pos q; [rewrite pos2nat_nxt, pos2nat_fst; exact H1 | invert pos q].
Qed.

(* ================================================================= *)
(* Moves of X.                                                         *)
(* ================================================================= *)

Lemma ax_cgk_x_block : forall a Q i e j e' aux,
  (a, map XMM Q) <sc (1, ax_cgk_SRC) ->
  sss_compute (mm_sss_env eq_nat_dec) (a, Q) (i, e) (j, e') ->
  Xc (i, (e, aux)) (j, (e', aux)).
Proof.
  intros a Q i e j e' aux Hsc [q Hq]. exists q.
  apply subcode_sss_steps with (1 := Hsc). apply ax_cgk_lift_mm; [| exact Hq].
  intros J HJ. apply ax_cgk_src_reg. eapply ax_cgk_sc_in; [exact Hsc |]. apply in_map. exact HJ.
Qed.

Lemma ax_cgk_x_block_p : forall a Q i e j e' aux,
  (a, map XMM Q) <sc (1, ax_cgk_SRC) ->
  sss_progress (mm_sss_env eq_nat_dec) (a, Q) (i, e) (j, e') ->
  Xp (i, (e, aux)) (j, (e', aux)).
Proof.
  intros a Q i e j e' aux Hsc (q & Hq0 & Hq). exists q. split; [exact Hq0 |].
  apply subcode_sss_steps with (1 := Hsc). apply ax_cgk_lift_mm; [| exact Hq].
  intros J HJ. apply ax_cgk_src_reg. eapply ax_cgk_sc_in; [exact Hsc |]. apply in_map. exact HJ.
Qed.

Lemma ax_cgk_x_one : forall i J e j e' aux,
  (i, [XMM J]) <sc (1, ax_cgk_SRC) ->
  mm_sss_env eq_nat_dec J (i, e) (j, e') ->
  Xp (i, (e, aux)) (j, (e', aux)).
Proof.
  intros i J e j e' aux Hsc Hs. apply (ax_cgk_x_block_p i [J]); [exact Hsc |].
  exists 1. split; [lia |]. apply sss_steps_1.
  change (i, [J]) with (i, [] ++ J :: []). apply in_sss_step; [simpl; lia | exact Hs].
Qed.

Lemma ax_cgk_x_dec0 : forall i x j e aux,
  (i, [XMM (mm_dec x j)]) <sc (1, ax_cgk_SRC) -> e x = 0 ->
  Xp (i, (e, aux)) (j, (e, aux)).
Proof. intros. apply (ax_cgk_x_one i (mm_dec x j)); [assumption | constructor; assumption]. Qed.

Lemma ax_cgk_x_decS : forall i x j e u aux,
  (i, [XMM (mm_dec x j)]) <sc (1, ax_cgk_SRC) -> e x = S u ->
  Xp (i, (e, aux)) (1 + i, (set_env eq_nat_dec e x u, aux)).
Proof. intros. apply (ax_cgk_x_one i (mm_dec x j)); [assumption | constructor; assumption]. Qed.

Lemma ax_cgk_x_inc : forall i x e aux,
  (i, [XMM (mm_inc x)]) <sc (1, ax_cgk_SRC) ->
  Xp (i, (e, aux)) (1 + i, (set_env eq_nat_dec e x (S (e x)), aux)).
Proof. intros. apply (ax_cgk_x_one i (mm_inc x)); [assumption | constructor]. Qed.

Lemma ax_cgk_x_pay : forall i e aux,
  (i, [XPAY]) <sc (1, ax_cgk_SRC) -> Xp (i, (e, aux)) (S i, (e, ax_cgk_pay aux)).
Proof.
  intros i e aux Hsc. apply subcode_sss_progress with (1 := Hsc).
  exists 1. split; [lia |]. apply sss_steps_1.
  change (i, [XPAY]) with (i, [] ++ XPAY :: []). apply in_sss_step; [simpl; lia | constructor].
Qed.

Lemma ax_cgk_x_earn : forall i e aux,
  (i, [XEARN]) <sc (1, ax_cgk_SRC) ->
  cg_ueval (URun ax_cgk_r) (cg_gk ax_cgk_k e) = true -> ax_cgk_a_earned aux < 16 ->
  Xp (i, (e, aux)) (S i, (e, ax_cgk_earn aux)).
Proof.
  intros i e aux Hsc H1 H2. apply subcode_sss_progress with (1 := Hsc).
  exists 1. split; [lia |]. apply sss_steps_1.
  change (i, [XEARN]) with (i, [] ++ XEARN :: []).
  apply in_sss_step; [simpl; lia | constructor; assumption].
Qed.

(* A decrement that goes on to the next address either way. *)
Lemma ax_cgk_x_dec_next : forall i x e aux,
  (i, [XMM (mm_dec x (1 + i))]) <sc (1, ax_cgk_SRC) ->
  exists e', ax_cgk_eqv e' (set_env eq_nat_dec e x (e x - 1)) /\
    Xp (i, (e, aux)) (1 + i, (e', aux)).
Proof.
  intros i x e aux Hsc. destruct (e x) as [| u] eqn:Ex.
  - exists e. split.
    + intros y. unfold set_env. destruct (eq_nat_dec x y) as [<- | _]; [exact Ex | reflexivity].
    + apply ax_cgk_x_dec0 with (x := x); assumption.
  - exists (set_env eq_nat_dec e x u). split.
    + intros y. replace (S u - 1) with u by lia. reflexivity.
    + apply ax_cgk_x_decS with (x := x) (j := 1 + i); assumption.
Qed.

Lemma ax_cgk_x_erase : forall a x e aux,
  x <> 8 -> (a, map XMM (mm_erase x 8 a)) <sc (1, ax_cgk_SRC) -> e 8 = 0 ->
  exists e', ax_cgk_eqv e' (set_env eq_nat_dec e x 0) /\ Xp (a, (e, aux)) (2 + a, (e', aux)).
Proof.
  intros a x e aux Hx Hsc H8.
  destruct (@mm_erase_progress x 8 Hx a e H8) as (e' & He' & Hp).
  exists e'. split; [exact He' |]. apply (ax_cgk_x_block_p a _ _ _ _ _ _ Hsc Hp).
Qed.

Lemma ax_cgk_x_transfert : forall a src dst e aux,
  src <> dst -> src <> 8 -> dst <> 8 ->
  (a, map XMM (mm_transfert src dst 8 a)) <sc (1, ax_cgk_SRC) -> e dst = 0 -> e 8 = 0 ->
  exists e', ax_cgk_eqv e' (set_env eq_nat_dec (set_env eq_nat_dec e src 0) dst (e src)) /\
    Xp (a, (e, aux)) (3 + a, (e', aux)).
Proof.
  intros a src dst e aux H1 H2 H3 Hsc Hd H8.
  destruct (@mm_transfert_progress src dst 8 H1 H2 H3 a e Hd H8) as (e' & He' & Hp).
  exists e'. split; [exact He' |]. apply (ax_cgk_x_block_p a _ _ _ _ _ _ Hsc Hp).
Qed.

(* ================================================================= *)
(* The pay loop.                                                       *)
(* ================================================================= *)

Lemma ax_cgk_x_payloop : forall c vS vE e mu ct ea,
  ax_cgk_eqv e (ax_cgk_rf vS 0 0 c 0 0 vE 0) ->
  exists e', ax_cgk_eqv e' (ax_cgk_rf vS 0 0 0 0 0 vE 0) /\
    Xp (ax_cgk_PL, (e, ax_cgk_mkaux mu ct ea)) (2, (e', ax_cgk_mkaux (mu + c) ct ea)).
Proof.
  induction c as [| c IH]; intros vS vE e mu ct ea He.
  - exists e. split; [intros y; rewrite He; ax_cgk_rf_tac |].
    rewrite Nat.add_0_r. apply ax_cgk_x_dec0 with (x := 3); [exact ax_cgk_sc_pl | ax_cgk_get He].
  - set (e1 := set_env eq_nat_dec e 3 c).
    assert (He1 : ax_cgk_eqv e1 (ax_cgk_rf vS 0 0 c 0 0 vE 0))
      by (intros y; ax_cgk_set He (fun y : nat => eq_refl (e1 y))).
    destruct (IH vS vE e1 (S mu) ct ea He1) as (e' & He' & Hp).
    exists e'. split; [exact He' |].
    eapply sss_progress_trans.
    { apply ax_cgk_x_decS with (x := 3) (j := 2); [exact ax_cgk_sc_pl | ax_cgk_get He]. }
    eapply sss_progress_trans.
    { apply ax_cgk_x_pay. replace (1 + ax_cgk_PL) with (ax_cgk_PL + 1) by lia. exact ax_cgk_sc_pay. }
    eapply sss_progress_trans.
    { replace (S (1 + ax_cgk_PL)) with (ax_cgk_PL + 2) by lia.
      apply ax_cgk_x_dec0 with (x := 8); [exact ax_cgk_sc_jmp3 | ax_cgk_get He1]. }
    replace (mu + S c) with (S mu + c) by lia. exact Hp.
Qed.

Lemma ax_cgk_set2_rf : forall (w w' : env nat nat) (f g : nat -> nat) src dst,
  (forall y, w y = f y) ->
  (forall y, w' y = set_env eq_nat_dec (set_env eq_nat_dec w src 0) dst (w src) y) ->
  src <> dst -> g dst = f src -> g src = 0 ->
  (forall y, y <> src -> y <> dst -> g y = f y) ->
  forall y, w' y = g y.
Proof.
  intros w w' f g src dst Hw Hw' Hsd Hd Hs Ho y. rewrite Hw'. unfold set_env.
  destruct (eq_nat_dec dst y) as [<- | H1]; [rewrite Hw; symmetry; exact Hd |].
  destruct (eq_nat_dec src y) as [<- | H2]; [symmetry; exact Hs |].
  rewrite Ho by auto. apply Hw.
Qed.

Ltac ax_cgk_set2 He He' :=
  apply (ax_cgk_set2_rf _ _ _ _ _ _ He He'); [lia | ax_cgk_rf_tac | ax_cgk_rf_tac | intros; ax_cgk_rf_tac].

(* ================================================================= *)
(* From HEAD to CHK: one driven move.                                  *)
(* ================================================================= *)

Lemma ax_cgk_x_move : forall s i vE e aux,
  ax_cgk_eqv e (ax_cgk_rf (sc s) 0 0 0 0 0 vE 0) -> next s = Some i ->
  exists e', ax_cgk_eqv e' (ax_cgk_rf (sc (cstep s i)) 0 0 (ccost i) 0 0 vE 0) /\
    Xp (2, (e, aux)) (ax_cgk_CHK, (e', aux)).
Proof.
  intros s i vE e aux He Hn.
  (* NEXT: H := 1 + code of the move *)
  assert (Hv : ax_cm_next_val C s = S (ic i)) by (unfold ax_cm_next_val; rewrite Hn; reflexivity).
  pose proof (ax_cp_next_spec C cp s) as Hrel. rewrite Hv in Hrel.
  destruct (proj1 (ax_cgk_Pn_spec (sc s ## vec_nil) e (ax_cgk_eqv_spare _ _ _ _ _ _ _ _ He)
                     (ax_cgk_in1 e 0 (sc s) ltac:(ax_cgk_get He))) _ Hrel) as (e1 & He1 & Hc1).
  assert (E1 : ax_cgk_eqv e1 (ax_cgk_rf (sc s) 0 (S (ic i)) 0 0 0 vE 0)) by (intros y; ax_cgk_set He He1).
  assert (H1 : Xc (2, (e, aux)) (2 + length ax_cgk_Pn, (e1, aux))).
  { replace (2 + length ax_cgk_Pn) with (length ax_cgk_Pn + 2) by lia.
    exact (ax_cgk_x_block 2 ax_cgk_Pn _ _ _ _ aux ax_cgk_sc_next Hc1). }
  (* DEC H HALTB *)
  set (e2 := set_env eq_nat_dec e1 2 (ic i)).
  assert (E2 : ax_cgk_eqv e2 (ax_cgk_rf (sc s) 0 (ic i) 0 0 0 vE 0))
    by (intros y; ax_cgk_set E1 (fun y : nat => eq_refl (e2 y))).
  assert (H2 : Xp (2 + length ax_cgk_Pn, (e1, aux)) (3 + length ax_cgk_Pn, (e2, aux))).
  { replace (3 + length ax_cgk_Pn) with (1 + (2 + length ax_cgk_Pn)) by lia.
    apply ax_cgk_x_decS with (x := 2) (j := ax_cgk_HALTB); [exact ax_cgk_sc_dech | ax_cgk_get E1]. }
  (* H to I *)
  destruct (ax_cgk_x_transfert (3 + length ax_cgk_Pn) 2 1 e2 aux ltac:(lia) ltac:(lia) ltac:(lia)
              ax_cgk_sc_tr1 ltac:(ax_cgk_get E2) ltac:(ax_cgk_get E2)) as (e3 & He3 & H3).
  assert (E3 : ax_cgk_eqv e3 (ax_cgk_rf (sc s) (ic i) 0 0 0 0 vE 0)) by (intros y; ax_cgk_set2 E2 He3).
  (* STEP: S' := code of the next state *)
  pose proof (ax_cp_step_spec C cp s i) as Hrs.
  destruct (proj1 (ax_cgk_Ps_spec (sc s ## ic i ## vec_nil) e3 (ax_cgk_eqv_spare _ _ _ _ _ _ _ _ E3)
                     (ax_cgk_in2 e3 (sc s) (ic i) ltac:(ax_cgk_get E3) ltac:(ax_cgk_get E3))) _ Hrs)
    as (e4 & He4 & Hc4).
  assert (E4 : ax_cgk_eqv e4 (ax_cgk_rf (sc s) (ic i) 0 0 (sc (cstep s i)) 0 vE 0))
    by (intros y; ax_cgk_set E3 He4).
  assert (H4 : Xc (ax_cgk_a_step, (e3, aux)) (ax_cgk_a_cost, (e4, aux))).
  { unfold ax_cgk_a_cost. replace (ax_cgk_a_step + length ax_cgk_Ps) with (length ax_cgk_Ps + ax_cgk_a_step) by lia.
    exact (ax_cgk_x_block _ ax_cgk_Ps _ _ _ _ aux ax_cgk_sc_step Hc4). }
  (* COST: C := cost of the move *)
  pose proof (ax_cp_cost_spec C cp i) as Hrc.
  destruct (proj1 (ax_cgk_Pc_spec (ic i ## vec_nil) e4 (ax_cgk_eqv_spare _ _ _ _ _ _ _ _ E4)
                     (ax_cgk_in1 e4 1 (ic i) ltac:(ax_cgk_get E4))) _ Hrc) as (e5 & He5 & Hc5).
  assert (E5 : ax_cgk_eqv e5 (ax_cgk_rf (sc s) (ic i) 0 (ccost i) (sc (cstep s i)) 0 vE 0))
    by (intros y; ax_cgk_set E4 He5).
  assert (H5 : Xc (ax_cgk_a_cost, (e4, aux)) (ax_cgk_a_erI, (e5, aux))).
  { unfold ax_cgk_a_erI. replace (ax_cgk_a_cost + length ax_cgk_Pc) with (length ax_cgk_Pc + ax_cgk_a_cost) by lia.
    exact (ax_cgk_x_block _ ax_cgk_Pc _ _ _ _ aux ax_cgk_sc_cost Hc5). }
  (* erase I, erase S, S' to S, JMP CHK *)
  destruct (ax_cgk_x_erase ax_cgk_a_erI 1 e5 aux ltac:(lia) ax_cgk_sc_erI ltac:(ax_cgk_get E5)) as (e6 & He6 & H6).
  assert (E6 : ax_cgk_eqv e6 (ax_cgk_rf (sc s) 0 0 (ccost i) (sc (cstep s i)) 0 vE 0))
    by (intros y; ax_cgk_set E5 He6).
  destruct (ax_cgk_x_erase (ax_cgk_a_erI + 2) 0 e6 aux ltac:(lia) ax_cgk_sc_erS ltac:(ax_cgk_get E6))
    as (e7 & He7 & H7).
  assert (E7 : ax_cgk_eqv e7 (ax_cgk_rf 0 0 0 (ccost i) (sc (cstep s i)) 0 vE 0))
    by (intros y; ax_cgk_set E6 He7).
  destruct (ax_cgk_x_transfert (ax_cgk_a_erI + 4) 4 0 e7 aux ltac:(lia) ltac:(lia) ltac:(lia)
              ax_cgk_sc_tr2 ltac:(ax_cgk_get E7) ltac:(ax_cgk_get E7)) as (e8 & He8 & H8).
  assert (E8 : ax_cgk_eqv e8 (ax_cgk_rf (sc (cstep s i)) 0 0 (ccost i) 0 0 vE 0))
    by (intros y; ax_cgk_set2 E7 He8).
  assert (H9 : Xp (ax_cgk_a_erI + 7, (e8, aux)) (ax_cgk_CHK, (e8, aux)))
    by (apply ax_cgk_x_dec0 with (x := 8); [exact ax_cgk_sc_jmp1 | ax_cgk_get E8]).
  exists e8. split; [exact E8 |].
  replace (2 + ax_cgk_a_erI) with (ax_cgk_a_erI + 2) in H6 by lia.
  replace (2 + (ax_cgk_a_erI + 2)) with (ax_cgk_a_erI + 4) in H7 by lia.
  replace (3 + (ax_cgk_a_erI + 4)) with (ax_cgk_a_erI + 7) in H8 by lia.
  replace (3 + (3 + length ax_cgk_Pn)) with ax_cgk_a_step in H3 by (unfold ax_cgk_a_step; lia).
  eapply sss_compute_progress_trans; [exact H1 |].
  eapply sss_progress_trans; [exact H2 |].
  eapply sss_progress_trans; [exact H3 |].
  eapply sss_compute_progress_trans; [exact H4 |].
  eapply sss_compute_progress_trans; [exact H5 |].
  eapply sss_progress_trans; [exact H6 |].
  eapply sss_progress_trans; [exact H7 |].
  eapply sss_progress_trans; [exact H8 | exact H9].
Qed.

(* From HEAD, when the driver halts: to HALTB with the registers kept. *)
Lemma ax_cgk_x_halt : forall s vE e aux,
  ax_cgk_eqv e (ax_cgk_rf (sc s) 0 0 0 0 0 vE 0) -> next s = None ->
  exists e', ax_cgk_eqv e' (ax_cgk_rf (sc s) 0 0 0 0 0 vE 0) /\
    Xp (2, (e, aux)) (ax_cgk_HALTB, (e', aux)).
Proof.
  intros s vE e aux He Hn.
  assert (Hv : ax_cm_next_val C s = 0) by (unfold ax_cm_next_val; rewrite Hn; reflexivity).
  pose proof (ax_cp_next_spec C cp s) as Hrel. rewrite Hv in Hrel.
  destruct (proj1 (ax_cgk_Pn_spec (sc s ## vec_nil) e (ax_cgk_eqv_spare _ _ _ _ _ _ _ _ He)
                     (ax_cgk_in1 e 0 (sc s) ltac:(ax_cgk_get He))) _ Hrel) as (e1 & He1 & Hc1).
  assert (E1 : ax_cgk_eqv e1 (ax_cgk_rf (sc s) 0 0 0 0 0 vE 0)) by (intros y; ax_cgk_set He He1).
  exists e1. split; [exact E1 |].
  eapply sss_compute_progress_trans.
  { replace (length ax_cgk_Pn + 2) with (2 + length ax_cgk_Pn) in Hc1 by lia.
    exact (ax_cgk_x_block 2 ax_cgk_Pn _ _ _ _ aux ax_cgk_sc_next Hc1). }
  apply ax_cgk_x_dec0 with (x := 2); [exact ax_cgk_sc_dech | ax_cgk_get E1].
Qed.

(* ================================================================= *)
(* After the check.                                                    *)
(* ================================================================= *)

Lemma ax_cgk_x_noraise : forall vS c vE t w mu ct ea,
  ax_cgk_eqv w (ax_cgk_rf vS 0 0 c 0 0 vE t) ->
  exists e', ax_cgk_eqv e' (ax_cgk_rf vS 0 0 0 0 0 vE 0) /\
    Xp (ax_cgk_NORAISE, (w, ax_cgk_mkaux mu ct ea)) (2, (e', ax_cgk_mkaux (mu + c) ct ea)).
Proof.
  intros vS c vE t w mu ct ea Hw.
  destruct (ax_cgk_x_erase ax_cgk_NORAISE ax_cgk_T w (ax_cgk_mkaux mu ct ea) ltac:(generalize ax_cgk_T_ge; lia)
              ax_cgk_sc_erT2 ltac:(ax_cgk_get Hw)) as (w1 & Hw1 & H1).
  assert (W1 : ax_cgk_eqv w1 (ax_cgk_rf vS 0 0 c 0 0 vE 0)) by (intros y; ax_cgk_set Hw Hw1).
  destruct (ax_cgk_x_payloop c vS vE w1 mu ct ea W1) as (e' & He' & H2).
  exists e'. split; [exact He' |].
  replace (2 + ax_cgk_NORAISE) with ax_cgk_PL in H1 by (unfold ax_cgk_PL, ax_cgk_NORAISE; lia).
  eapply sss_progress_trans; [exact H1 | exact H2].
Qed.

(* ================================================================= *)
(* The reading at a level, counted.                                    *)
(* ================================================================= *)

Lemma ax_cgk_x_read2 : forall s l c vT e aux,
  ax_cgk_eqv e (ax_cgk_rf (sc s) l 0 c 0 0 0 vT) ->
  exists t w1, ax_cgk_eqv w1 (ax_cgk_rf (sc s) l 0 c 0 (if Nat.leb l (hh s) then 1 else 0) 0 t) /\
    Xp (ax_cgk_LOOP, (e, aux)) (ax_cgk_a_tail, (w1, aux)) /\
    (forall ex, ax_cgk_eqv ex (ax_cgk_rf (sc s) l 0 c 0 0 0 t) ->
       cg_ueval (URun ax_cgk_r) (cg_gk ax_cgk_k ex) = Nat.leb l (hh s)).
Proof.
  intros s l c vT e aux He.
  destruct (ax_cgk_x_erase ax_cgk_LOOP ax_cgk_T e aux ltac:(generalize ax_cgk_T_ge; lia) ax_cgk_sc_erT ltac:(ax_cgk_get He))
    as (e1 & He1 & H1).
  assert (E1 : ax_cgk_eqv e1 (ax_cgk_rf (sc s) l 0 c 0 0 0 0)) by (intros y; ax_cgk_set He He1).
  pose proof (ax_cp_read_spec C cp (sc s) l) as Hrel. rewrite ax_cm_read_val_code in Hrel.
  destruct (proj1 (ax_cgk_Pr_spec (sc s ## l ## vec_nil) e1 (ax_cgk_eqv_spare _ _ _ _ _ _ _ _ E1)
                     (ax_cgk_in2 e1 (sc s) l ltac:(ax_cgk_get E1) ltac:(ax_cgk_get E1))) _ Hrel)
    as (e2 & He2 & [t Ht]).
  assert (Hout : out_code (length ax_cgk_Pr + ax_cgk_ig) (ax_cgk_ig, ax_cgk_Pr))
    by (simpl; unfold code_end; simpl; lia).
  destruct (cg_read_T_spec ax_cgk_T ax_cgk_Pr ax_cgk_ig ax_cgk_a_read t e1 _ e2 e1 ax_cgk_T_fresh Ht Hout
              ltac:(ax_cgk_get E1) (fun _ _ => eq_refl)) as (w1 & [Hc _] & HT & Hw1).
  assert (W1 : ax_cgk_eqv w1 (ax_cgk_rf (sc s) l 0 c 0 (if Nat.leb l (hh s) then 1 else 0) 0 t)).
  { intros y. destruct (Nat.eq_dec y ax_cgk_T) as [-> | Hne].
    - rewrite HT. ax_cgk_rf_tac.
    - rewrite (Hw1 y Hne). change (e2 y) with (get_env e2 y). rewrite He2.
      unfold get_env, set_env. destruct (eq_nat_dec 5 y) as [<- | Hne5]; [ax_cgk_rf_tac |].
      rewrite E1. ax_cgk_rf_tac. }
  exists t, w1. split; [exact W1 |]. split.
  - eapply sss_progress_compute_trans; [exact H1 |].
    replace (2 + ax_cgk_LOOP) with ax_cgk_a_read by (unfold ax_cgk_a_read; lia).
    exact (ax_cgk_x_block _ _ _ _ _ _ aux ax_cgk_sc_read Hc).
  - intros ex Hex.
    assert (Hz : forall y, ax_cgk_k <= y -> ex y = 0) by (exact (ax_cgk_eqv_zero_high _ _ _ _ _ _ _ _ _ Hex)).
    cbn [cg_ueval]. unfold ax_cgk_r. rewrite cg_rdec_renc. unfold cg_run_check.
    rewrite (cg_expo_gk_zero ax_cgk_k ex ax_cgk_T Hz).
    replace (ex ax_cgk_T) with t by (symmetry; ax_cgk_get Hex).
    assert (Hpt : forall x, get_env (cg_env_chk 16 (cg_gk ax_cgk_k ex)) x = get_env e1 x).
    { intros x. rewrite (cg_env_chk_gk ax_cgk_k ex 16 x Hz). rewrite cg_get_env, E1.
      destruct (Nat.ltb_spec x 16); [rewrite Hex; ax_cgk_rf_tac | ax_cgk_rf_tac]. }
    destruct (cg_mme_run_ext t (ax_cgk_ig, ax_cgk_Pr) ax_cgk_ig _ _ Hpt) as [Hf Hs].
    rewrite (cg_mme_run_fuel_complete _ _ _ _ Ht Hout t (le_n t)) in Hf, Hs.
    cbn [fst] in Hf. cbv zeta. rewrite Hf.
    replace (cg_out_codeb (ax_cgk_ig, ax_cgk_Pr) (length ax_cgk_Pr + ax_cgk_ig)) with true
      by (symmetry; apply cg_out_codeb_spec; exact Hout).
    rewrite Hs. cbn [snd]. rewrite He2. unfold get_env, set_env.
    destruct (eq_nat_dec 5 5) as [_ | C0]; [| congruence].
    destruct (Nat.leb l (hh s)); reflexivity.
Qed.

(* ================================================================= *)
(* Setting up the loop and leaving it.                                 *)
(* ================================================================= *)

(* From CHK: the latch moves to register 1 and goes up by one. *)
Lemma ax_cgk_x_setup : forall vS c m e aux,
  ax_cgk_eqv e (ax_cgk_rf vS 0 0 c 0 0 m 0) ->
  exists e', ax_cgk_eqv e' (ax_cgk_rf vS (S m) 0 c 0 0 0 0) /\
    Xp (ax_cgk_CHK, (e, aux)) (ax_cgk_LOOP, (e', aux)).
Proof.
  intros vS c m e aux He.
  destruct (ax_cgk_x_transfert ax_cgk_CHK 7 1 e aux ltac:(lia) ltac:(lia) ltac:(lia) ax_cgk_sc_trE
              ltac:(ax_cgk_get He) ltac:(ax_cgk_get He)) as (e1 & He1 & H1).
  assert (E1 : ax_cgk_eqv e1 (ax_cgk_rf vS m 0 c 0 0 0 0)) by (intros y; ax_cgk_set2 He He1).
  set (e2 := set_env eq_nat_dec e1 1 (S (e1 1))).
  assert (E2 : ax_cgk_eqv e2 (ax_cgk_rf vS (S m) 0 c 0 0 0 0)).
  { intros y. assert (E : e1 1 = m) by (ax_cgk_get E1).
    apply (ax_cgk_set_rf _ _ _ _ _ _ E1 (fun y : nat => eq_refl (e2 y)));
      [rewrite E; ax_cgk_rf_tac | intros; ax_cgk_rf_tac]. }
  exists e2. split; [exact E2 |].
  eapply sss_progress_trans; [exact H1 |].
  replace (3 + ax_cgk_CHK) with (ax_cgk_CHK + 3) by lia.
  replace ax_cgk_LOOP with (1 + (ax_cgk_CHK + 3)) by (unfold ax_cgk_LOOP; lia).
  apply ax_cgk_x_inc. exact ax_cgk_sc_incI0.
Qed.

(* From EXIT: register 1 goes down by one and moves back to the latch. *)
Lemma ax_cgk_x_exit : forall vS l c t e aux, 1 <= l ->
  ax_cgk_eqv e (ax_cgk_rf vS l 0 c 0 0 0 t) ->
  exists e', ax_cgk_eqv e' (ax_cgk_rf vS 0 0 c 0 0 (l - 1) t) /\
    Xp (ax_cgk_EXIT, (e, aux)) (ax_cgk_NORAISE, (e', aux)).
Proof.
  intros vS l c t e aux Hl He.
  destruct l as [| u]; [lia |].
  set (e1 := set_env eq_nat_dec e 1 u).
  assert (E1 : ax_cgk_eqv e1 (ax_cgk_rf vS u 0 c 0 0 0 t))
    by (intros y; ax_cgk_set He (fun y : nat => eq_refl (e1 y))).
  assert (H1 : Xp (ax_cgk_EXIT, (e, aux)) (ax_cgk_a_tail + 8, (e1, aux))).
  { replace (ax_cgk_a_tail + 8) with (1 + ax_cgk_EXIT) by (unfold ax_cgk_EXIT; lia).
    apply ax_cgk_x_decS with (x := 1) (j := ax_cgk_a_tail + 8); [exact ax_cgk_sc_decI | ax_cgk_get He]. }
  destruct (ax_cgk_x_transfert (ax_cgk_a_tail + 8) 1 7 e1 aux ltac:(lia) ltac:(lia) ltac:(lia) ax_cgk_sc_trX
              ltac:(ax_cgk_get E1) ltac:(ax_cgk_get E1)) as (e2 & He2 & H2).
  assert (E2 : ax_cgk_eqv e2 (ax_cgk_rf vS 0 0 c 0 0 u t)) by (intros y; ax_cgk_set2 E1 He2).
  exists e2. split.
  - intros y. rewrite (E2 y). replace (S u - 1) with u by lia. reflexivity.
  - eapply sss_progress_trans; [exact H1 |].
    replace ax_cgk_NORAISE with (3 + (ax_cgk_a_tail + 8)) by (unfold ax_cgk_NORAISE; lia). exact H2.
Qed.

(* ================================================================= *)
(* The loop: earn one level at a time while the reading says yes.      *)
(* ================================================================= *)

Lemma ax_cgk_x_loop : forall d s m c mu ct vT e,
  hh s <= 16 -> d = hh s - m ->
  ax_cgk_eqv e (ax_cgk_rf (sc s) (S m) 0 c 0 0 0 vT) ->
  exists t e', ax_cgk_eqv e' (ax_cgk_rf (sc s) (S (m + d)) 0 (c - 3 * d) 0 0 0 t) /\
    Xp (ax_cgk_LOOP, (e, ax_cgk_mkaux mu ct m))
       (ax_cgk_EXIT, (e', ax_cgk_mkaux (mu + 3 * d) (ct || Nat.ltb 0 d) (m + d))).
Proof.
  induction d as [| d IH]; intros s m c mu ct vT e Hb Hd He.
  - assert (Hle : Nat.leb (S m) (hh s) = false) by (apply Nat.leb_gt; lia).
    destruct (ax_cgk_x_read2 s (S m) c vT e (ax_cgk_mkaux mu ct m) He) as (t & w1 & Hw1 & H1 & _).
    rewrite Hle in Hw1.
    exists t, w1. split.
    + intros y. rewrite (Hw1 y). replace (m + 0) with m by lia. replace (c - 3 * 0) with c by lia.
      ax_cgk_rf_tac.
    + eapply sss_progress_trans; [exact H1 |].
      replace (mu + 3 * 0) with mu by lia. replace (m + 0) with m by lia.
      replace (Nat.ltb 0 0) with false by reflexivity. rewrite orb_false_r.
      apply ax_cgk_x_dec0 with (x := 5); [exact ax_cgk_sc_decB | ax_cgk_get Hw1].
  - assert (Hle : Nat.leb (S m) (hh s) = true) by (apply Nat.leb_le; lia).
    destruct (ax_cgk_x_read2 s (S m) c vT e (ax_cgk_mkaux mu ct m) He) as (t & w1 & Hw1 & H1 & Hchk).
    rewrite Hle in Hw1.
    set (w2 := set_env eq_nat_dec w1 5 0).
    assert (W2 : ax_cgk_eqv w2 (ax_cgk_rf (sc s) (S m) 0 c 0 0 0 t))
      by (intros y; ax_cgk_set Hw1 (fun y : nat => eq_refl (w2 y))).
    assert (H2 : Xp (ax_cgk_a_tail, (w1, ax_cgk_mkaux mu ct m)) (1 + ax_cgk_a_tail, (w2, ax_cgk_mkaux mu ct m))).
    { apply ax_cgk_x_decS with (x := 5) (j := ax_cgk_EXIT); [exact ax_cgk_sc_decB | ax_cgk_get Hw1]. }
    pose proof (Hchk w2 W2) as Hck. rewrite Hle in Hck.
    assert (H3 : Xp (ax_cgk_a_tail + 1, (w2, ax_cgk_mkaux mu ct m))
                    (S (ax_cgk_a_tail + 1), (w2, ax_cgk_earn (ax_cgk_mkaux mu ct m)))).
    { apply ax_cgk_x_earn; [exact ax_cgk_sc_earn | exact Hck | simpl; lia]. }
    cbn [ax_cgk_earn ax_cgk_a_mu ax_cgk_a_earned] in H3.
    set (aux1 := ax_cgk_mkaux (mu + 3) true (S m)).
    set (w3 := set_env eq_nat_dec w2 1 (S (w2 1))).
    assert (W3 : ax_cgk_eqv w3 (ax_cgk_rf (sc s) (S (S m)) 0 c 0 0 0 t)).
    { intros y. assert (E : w2 1 = S m) by (ax_cgk_get W2).
      apply (ax_cgk_set_rf _ _ _ _ _ _ W2 (fun y : nat => eq_refl (w3 y)));
        [rewrite E; ax_cgk_rf_tac | intros; ax_cgk_rf_tac]. }
    assert (H4 : Xp (ax_cgk_a_tail + 2, (w2, aux1)) (1 + (ax_cgk_a_tail + 2), (w3, aux1)))
      by (apply ax_cgk_x_inc; exact ax_cgk_sc_incI).
    destruct (ax_cgk_x_dec_next (ax_cgk_a_tail + 3) 3 w3 aux1 ltac:(
                replace (1 + (ax_cgk_a_tail + 3)) with (ax_cgk_a_tail + 4) by lia; exact ax_cgk_sc_decC1))
      as (x2 & Hx2 & H5).
    assert (X2 : ax_cgk_eqv x2 (ax_cgk_rf (sc s) (S (S m)) 0 (c - 1) 0 0 0 t)).
    { intros y. assert (E : w3 3 = c) by (ax_cgk_get W3). rewrite E in Hx2. ax_cgk_set W3 Hx2. }
    destruct (ax_cgk_x_dec_next (ax_cgk_a_tail + 4) 3 x2 aux1 ltac:(
                replace (1 + (ax_cgk_a_tail + 4)) with (ax_cgk_a_tail + 5) by lia; exact ax_cgk_sc_decC2))
      as (x3 & Hx3 & H6).
    assert (X3 : ax_cgk_eqv x3 (ax_cgk_rf (sc s) (S (S m)) 0 (c - 1 - 1) 0 0 0 t)).
    { intros y. assert (E : x2 3 = c - 1) by (ax_cgk_get X2). rewrite E in Hx3. ax_cgk_set X2 Hx3. }
    destruct (ax_cgk_x_dec_next (ax_cgk_a_tail + 5) 3 x3 aux1 ltac:(
                replace (1 + (ax_cgk_a_tail + 5)) with (ax_cgk_a_tail + 6) by lia; exact ax_cgk_sc_decC3))
      as (x4 & Hx4 & H7).
    assert (X4 : ax_cgk_eqv x4 (ax_cgk_rf (sc s) (S (S m)) 0 (c - 1 - 1 - 1) 0 0 0 t)).
    { intros y. assert (E : x3 3 = c - 1 - 1) by (ax_cgk_get X3). rewrite E in Hx4. ax_cgk_set X3 Hx4. }
    assert (H8 : Xp (ax_cgk_a_tail + 6, (x4, aux1)) (ax_cgk_LOOP, (x4, aux1)))
      by (apply ax_cgk_x_dec0 with (x := 8); [exact ax_cgk_sc_jmpL | ax_cgk_get X4]).
    destruct (IH s (S m) (c - 1 - 1 - 1) (mu + 3) true t x4 Hb ltac:(lia) X4)
      as (t' & e' & He' & Hp).
    exists t', e'. split.
    + intros y. rewrite (He' y).
      replace (S m + d) with (m + S d) by lia.
      replace (c - 1 - 1 - 1 - 3 * d) with (c - 3 * S d) by lia. reflexivity.
    + replace (1 + ax_cgk_a_tail) with (ax_cgk_a_tail + 1) in H2 by lia.
      replace (S (ax_cgk_a_tail + 1)) with (ax_cgk_a_tail + 2) in H3 by lia.
      replace (1 + (ax_cgk_a_tail + 2)) with (ax_cgk_a_tail + 3) in H4 by lia.
      replace (1 + (ax_cgk_a_tail + 3)) with (ax_cgk_a_tail + 4) in H5 by lia.
      replace (1 + (ax_cgk_a_tail + 4)) with (ax_cgk_a_tail + 5) in H6 by lia.
      replace (1 + (ax_cgk_a_tail + 5)) with (ax_cgk_a_tail + 6) in H7 by lia.
      eapply sss_progress_trans; [exact H1 |].
      eapply sss_progress_trans; [exact H2 |].
      eapply sss_progress_trans; [exact H3 |].
      eapply sss_progress_trans; [exact H4 |].
      eapply sss_progress_trans; [exact H5 |].
      eapply sss_progress_trans; [exact H6 |].
      eapply sss_progress_trans; [exact H7 |].
      eapply sss_progress_trans; [exact H8 |].
      replace (mu + 3 * S d) with (mu + 3 + 3 * d) by lia.
      replace (m + S d) with (S m + d) by lia.
      replace (ct || Nat.ltb 0 (S d)) with (true || Nat.ltb 0 d)
        by (replace (Nat.ltb 0 (S d)) with true by reflexivity; rewrite orb_true_r; reflexivity).
      exact Hp.
Qed.

(* ================================================================= *)
(* From CHK to HEAD: the whole check of one state.                     *)
(* ================================================================= *)

Lemma ax_cgk_ltb_sub : forall a b, Nat.ltb 0 (a - b) = Nat.ltb b a.
Proof. intros a b. apply eq_true_iff_eq. rewrite !Nat.ltb_lt. lia. Qed.

Lemma ax_cgk_x_check : forall s c m mu ct e,
  hh s <= 16 ->
  ax_cgk_eqv e (ax_cgk_rf (sc s) 0 0 c 0 0 m 0) ->
  exists e', ax_cgk_eqv e' (ax_cgk_rf (sc s) 0 0 0 0 0 (max (hh s) m) 0) /\
    Xp (ax_cgk_CHK, (e, ax_cgk_mkaux mu ct m))
       (2, (e', ax_cgk_mkaux (mu + max c (3 * (hh s - m))) (ct || Nat.ltb m (hh s)) (max (hh s) m))).
Proof.
  intros s c m mu ct e Hb He.
  destruct (ax_cgk_x_setup (sc s) c m e (ax_cgk_mkaux mu ct m) He) as (e1 & E1 & H1).
  destruct (ax_cgk_x_loop (hh s - m) s m c mu ct 0 e1 Hb eq_refl E1) as (t & e2 & E2 & H2).
  destruct (ax_cgk_x_exit (sc s) (S (m + (hh s - m))) (c - 3 * (hh s - m)) t e2
              (ax_cgk_mkaux (mu + 3 * (hh s - m)) (ct || Nat.ltb 0 (hh s - m)) (m + (hh s - m)))
              ltac:(lia) E2) as (e3 & E3 & H3).
  destruct (ax_cgk_x_noraise (sc s) (c - 3 * (hh s - m)) (S (m + (hh s - m)) - 1) t e3
              (mu + 3 * (hh s - m)) (ct || Nat.ltb 0 (hh s - m)) (m + (hh s - m)) E3)
    as (e4 & E4 & H4).
  exists e4. split.
  - intros y. rewrite (E4 y). replace (S (m + (hh s - m)) - 1) with (max (hh s) m) by lia.
    reflexivity.
  - replace (mu + 3 * (hh s - m) + (c - 3 * (hh s - m))) with (mu + max c (3 * (hh s - m))) in H4
      by lia.
    rewrite ax_cgk_ltb_sub in H2, H3, H4.
    replace (m + (hh s - m)) with (max (hh s) m) in H2, H3, H4 by lia.
    eapply sss_progress_trans; [exact H1 |].
    eapply sss_progress_trans; [exact H2 |].
    eapply sss_progress_trans; [exact H3 |].
    exact H4.
Qed.

(* ================================================================= *)
(* The invariant at HEAD, and the three phases.                        *)
(* ================================================================= *)

(* The guest's registers at the start: S holds the code of s0. *)
Definition ax_cgk_e0 (s0 : st) : env nat nat := fun y => if Nat.eqb y 0 then sc s0 else 0.

Lemma ax_cgk_e0_rf : forall s0, ax_cgk_eqv (ax_cgk_e0 s0) (ax_cgk_rf (sc s0) 0 0 0 0 0 0 0).
Proof. intros s0 y. unfold ax_cgk_e0. ax_cgk_rf_tac. Qed.

Lemma ax_cgk_e0_high : forall s0 y, ax_cgk_k <= y -> ax_cgk_e0 s0 y = 0.
Proof. intros s0 y H. rewrite ax_cgk_e0_rf. apply ax_cgk_rf_high. exact H. Qed.

Lemma ax_cgk_cert_max : forall a b,
  (Nat.ltb 0 a || Nat.ltb a b) = Nat.ltb 0 (Nat.max a b).
Proof. intros a b. apply eq_true_iff_eq. rewrite orb_true_iff, !Nat.ltb_lt. lia. Qed.

(* inv_head n: S holds the code of the state after n driven steps, E the
   latched height, every other register 0; the record is (the guest's
   ledger, flag up when the latched height is positive, earned count the
   latched height). *)
Definition ax_cgk_inv_head (s0 : st) (n : nat) (x : ax_cgk_xstate) : Prop :=
  ax_cgk_eqv (fst x) (ax_cgk_rf (sc (ax_cm_run C s0 n)) 0 0 0 0 0 (ax_cm_lat C s0 n) 0) /\
  snd x = ax_cgk_mkaux (ax_cm_gledger C s0 n) (Nat.ltb 0 (ax_cm_lat C s0 n)) (ax_cm_lat C s0 n).

Theorem ax_cgk_x_prologue : forall s0, hh s0 <= 16 ->
  exists x, ax_cgk_inv_head s0 0 x /\ Xp (1, (ax_cgk_e0 s0, ax_cgk_mkaux 0 false 0)) (2, x).
Proof.
  intros s0 Hb.
  destruct (ax_cgk_x_check s0 0 0 0 false (ax_cgk_e0 s0) Hb (ax_cgk_e0_rf s0)) as (e' & He' & H).
  exists (e', ax_cgk_mkaux (0 + max 0 (3 * (hh s0 - 0))) (false || Nat.ltb 0 (hh s0)) (max (hh s0) 0)).
  split; [split |].
  - cbn [fst ax_cm_lat ax_cm_run]. intros y. rewrite (He' y). replace (max (hh s0) 0) with (hh s0) by lia.
    reflexivity.
  - cbn [snd ax_cm_gledger ax_cm_lat].
    replace (max (hh s0) 0) with (hh s0) by lia.
    replace (0 + max 0 (3 * (hh s0 - 0))) with (3 * hh s0) by lia.
    reflexivity.
  - eapply sss_progress_trans; [| exact H].
    apply ax_cgk_x_dec0 with (x := 8); [exact ax_cgk_sc_jmp0 | ax_cgk_get (ax_cgk_e0_rf s0)].
Qed.

Theorem ax_cgk_x_step : forall s0 n x i, hh (cstep (ax_cm_run C s0 n) i) <= 16 ->
  ax_cgk_inv_head s0 n x -> next (ax_cm_run C s0 n) = Some i ->
  exists x', ax_cgk_inv_head s0 (S n) x' /\ Xp (2, x) (2, x').
Proof.
  intros s0 n [e a] i Hb [He Ha] Hn. cbn [fst snd] in He, Ha. subst a.
  destruct (ax_cgk_x_move _ i _ e (ax_cgk_mkaux (ax_cm_gledger C s0 n) (Nat.ltb 0 (ax_cm_lat C s0 n)) (ax_cm_lat C s0 n))
              He Hn) as (e1 & He1 & H1).
  destruct (ax_cgk_x_check (cstep (ax_cm_run C s0 n) i) (ccost i) (ax_cm_lat C s0 n) (ax_cm_gledger C s0 n)
              (Nat.ltb 0 (ax_cm_lat C s0 n)) e1 Hb He1) as (e2 & He2 & H2).
  assert (Hr : ax_cm_run C s0 (S n) = cstep (ax_cm_run C s0 n) i)
    by (rewrite ax_cm_run_succ, Hn; reflexivity).
  assert (Hl : ax_cm_lat C s0 (S n) = max (hh (cstep (ax_cm_run C s0 n) i)) (ax_cm_lat C s0 n)).
  { rewrite ax_cm_lat_succ, Hr. lia. }
  exists (e2, ax_cgk_mkaux (ax_cm_gledger C s0 n + max (ccost i) (3 * (hh (cstep (ax_cm_run C s0 n) i) - ax_cm_lat C s0 n)))
                         (Nat.ltb 0 (ax_cm_lat C s0 n) || Nat.ltb (ax_cm_lat C s0 n) (hh (cstep (ax_cm_run C s0 n) i)))
                         (max (hh (cstep (ax_cm_run C s0 n) i)) (ax_cm_lat C s0 n))).
  split; [split |].
  - cbn [fst]. rewrite Hr, Hl. exact He2.
  - cbn [snd].
    assert (Hg : ax_cm_gledger C s0 (S n) = ax_cm_gledger C s0 n +
                 max (ccost i) (3 * (hh (cstep (ax_cm_run C s0 n) i) - ax_cm_lat C s0 n))).
    { cbn [ax_cm_gledger]. unfold ax_cm_step_cost. rewrite Hn, Hl.
      replace (max (hh (cstep (ax_cm_run C s0 n) i)) (ax_cm_lat C s0 n) - ax_cm_lat C s0 n)
        with (hh (cstep (ax_cm_run C s0 n) i) - ax_cm_lat C s0 n) by lia.
      reflexivity. }
    assert (Hc : (Nat.ltb 0 (ax_cm_lat C s0 n) || Nat.ltb (ax_cm_lat C s0 n) (hh (cstep (ax_cm_run C s0 n) i)))
                 = Nat.ltb 0 (max (hh (cstep (ax_cm_run C s0 n) i)) (ax_cm_lat C s0 n))).
    { apply eq_true_iff_eq. rewrite orb_true_iff, !Nat.ltb_lt. lia. }
    rewrite Hg, Hl, Hc. reflexivity.
  - eapply sss_progress_trans; [exact H1 | exact H2].
Qed.

Theorem ax_cgk_x_stop : forall s0 n x,
  ax_cgk_inv_head s0 n x -> next (ax_cm_run C s0 n) = None ->
  exists x', ax_cgk_inv_head s0 n x' /\ Xp (2, x) (ax_cgk_HALTB, x').
Proof.
  intros s0 n [e a] [He Ha] Hn. cbn [fst snd] in He, Ha.
  destruct (ax_cgk_x_halt _ _ e a He Hn) as (e1 & He1 & H1).
  exists (e1, a). split; [split; [exact He1 | exact Ha] | exact H1].
Qed.

End Guest.

Print Assumptions ax_cgk_x_read2.
Print Assumptions ax_cgk_x_loop.
Print Assumptions ax_cgk_x_check.
Print Assumptions ax_cgk_x_prologue.
Print Assumptions ax_cgk_x_step.
Print Assumptions ax_cgk_x_stop.
