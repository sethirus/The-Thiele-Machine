(** CompilerGuest.v: the source program of the guest of a computably
    presented machine, and its phases in the source language X.

    For a presented machine M with a presentation pc (Presentation.v), the
    vendored compiler from recursive algorithms to counter programs gives
    four counter subroutines: NEXT (input register S, answer in H), STEP
    (inputs S and I, answer in S'), COST (input I, answer in C) and READ
    (input S, answer in B), each with spare registers from 16 on. READ is
    instrumented (CompilerInstrument.v) to count its steps in a register T
    above every register READ names and above 16.

    Register layout: S = 0, I = 1, H = 2, C = 3, S' = 4, B = 5, E = 7,
    Z = 8 (always 0), T as above, spares from 16 on. The source program
    cg_SRC, placed at address 1, is

      1      JMP CHK                       (prologue: check s0 with C = 0)
      HEAD   NEXT; DEC H HALTB; move H to I; STEP; COST; erase I; erase S;
             move S' to S; JMP CHK
      CHK    erase T; READ counted in T; DEC B NORAISE; DEC E NEW; INC E;
             JMP NORAISE
      NEW    XEARN; INC E; DEC C three times (C := C - 3)
      NORAISE erase T
      PL     DEC C HEAD; XPAY; JMP PL
      HALTB  XHALT

    where JMP j is DEC Z j and DEC x j jumps to j when x is 0.

    Invariant at HEAD after n driven steps from s0 [cg_inv_head]: S holds
    the code of the state after n steps, E holds the latch bit, every
    other register is 0; the guest's record is (ledger + surcharge, latch,
    latch).

    Phases proved in X:
      cg_x_prologue  from address 1 to HEAD with the invariant at 0;
      cg_x_step      from HEAD with the invariant at n, when the driver
                     moves, to HEAD with the invariant at n + 1, in at least
                     one step;
      cg_x_stop      from HEAD with the invariant at n, when the driver
                     halts, to HALTB with the same registers and record;
      cg_x_move, cg_x_to_new
                     from HEAD to CHK, and from CHK to NEW at the first
                     raise, where the fixed checker accepts the routine of
                     READ on the code of the registers.

    Dependencies: Coq standard library, the vendored coq-undecidability
    library, EarnedGeneric.v, EarnedPriced.v, ThieleComplete.v,
    Presented.v, Presentation.v and the Compiler*.v files. No axioms and no
    unfinished proofs. *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this
   file is one step of the presented universal machine of
   PresentedUniversal.v and imports only the Coq standard library, the
   vendored coq-undecidability library and the standard-library files under
   minimal/. Its link to the abstract record (the priced host as a
   CertificationSystem, the cost floor of its runs, and the undecidability
   of U_P's halting problem) lives in PricedHostLinks.v. *)

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
Require Import Minimal.Presented Kernel.Presentation.
Require Import Kernel.CompilerCodes Kernel.CompilerChecker Kernel.CompilerInstrument
  Kernel.CompilerLifts.

(* ================================================================= *)
(* Generic facts.                                                      *)
(* ================================================================= *)

Definition cg_maxreg (l : list (mm_instr nat)) : nat :=
  fold_right (fun J m => max (cg_reg_of J) m) 0 l.

Lemma cg_maxreg_in : forall l J, In J l -> cg_reg_of J <= cg_maxreg l.
Proof.
  induction l as [| J' l IH]; intros J H; [destruct H |].
  destruct H as [-> | H]; simpl; [lia |]. specialize (IH J H). lia.
Qed.

Definition cg_xmax (l : list cg_xinstr) : nat :=
  fold_right (fun J m => max (match J with XMM J0 => cg_reg_of J0 | _ => 0 end) m) 0 l.

Lemma cg_xmax_in : forall l J, In (XMM J) l -> cg_reg_of J <= cg_xmax l.
Proof.
  induction l as [| J' l IH]; intros J H; [destruct H |].
  destruct H as [-> | H]; simpl; [lia |]. specialize (IH J H). lia.
Qed.

Lemma cg_sc_cons : forall (X : Type) (Pc : nat * list X) n x l,
  Pc <sc (S n, l) -> Pc <sc (n, x :: l).
Proof. intros X Pc n x l H. apply subcode_cons. exact H. Qed.

Lemma cg_sc_app : forall (X : Type) (Pc : nat * list X) n l r,
  Pc <sc (n + length l, r) -> Pc <sc (n, l ++ r).
Proof.
  intros X [a q] n l r (l1 & r1 & H1 & H2). exists (l ++ l1), r1. split.
  - rewrite H1, app_assoc. reflexivity.
  - rewrite app_length. lia.
Qed.

Lemma cg_sc_here1 : forall (X : Type) a n (x : X) l, a = n -> (a, [x]) <sc (n, x :: l).
Proof. intros X a n x l ->. exists [], l. split; [reflexivity | simpl; lia]. Qed.

Lemma cg_sc_here : forall (X : Type) a n (l r : list X), a = n -> (a, l) <sc (n, l ++ r).
Proof. intros X a n l r ->. apply subcode_left. reflexivity. Qed.

Lemma cg_sc_in : forall (X : Type) a (l : list X) n L x, (a, l) <sc (n, L) -> In x l -> In x L.
Proof.
  intros X a l n L x (l1 & r1 & -> & _) H. apply in_or_app. right. apply in_or_app. left. exact H.
Qed.

Lemma cg_set_rf : forall (w w' : env nat nat) (f g : nat -> nat) o v,
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

Variable M : presented_machine.
Variable pc : cg_presentation M.

Local Notation st := (T.cs_state (pm_sys M)).
Local Notation mv := (T.cs_instr (pm_sys M)).
Local Notation cstep := (T.cs_step (pm_sys M)).
Local Notation ccost := (T.cs_cost (pm_sys M)).
Local Notation rd := (T.cs_cert (pm_sys M)).
Local Notation sc := (pm_scode M).
Local Notation ic := (pm_icode M).

(* ================================================================= *)
(* The subroutines and the layout.                                     *)
(* ================================================================= *)

(* NEXT at HEAD = 2: input S = 0, answer H = 2. *)
Definition cg_Pn : list (mm_instr nat) :=
  proj1_sig (@RA.ra_compiler 1 (cg_next_ra pc) 2 0 2 16 ltac:(lia) ltac:(lia) ltac:(lia)).

Lemma cg_Pn_spec : RA.ra_compiled (cg_next_ra pc) 2 0 2 16 cg_Pn.
Proof. unfold cg_Pn. exact (proj2_sig _). Qed.

Definition cg_a_step : nat := 6 + length cg_Pn.

(* STEP: inputs S = 0 and I = 1, answer S' = 4. *)
Definition cg_Ps : list (mm_instr nat) :=
  proj1_sig (@RA.ra_compiler 2 (cg_step_ra pc) cg_a_step 0 4 16 ltac:(lia) ltac:(lia) ltac:(lia)).

Lemma cg_Ps_spec : RA.ra_compiled (cg_step_ra pc) cg_a_step 0 4 16 cg_Ps.
Proof. unfold cg_Ps. exact (proj2_sig _). Qed.

(* SAFE: a code address in the compiled guest (the address after the STEP
   block), not a price. *)
Definition cg_a_cost : nat := cg_a_step + length cg_Ps.

(* COST: input I = 1, answer C = 3. *)
Definition cg_Pc : list (mm_instr nat) :=
  proj1_sig (@RA.ra_compiler 1 (cg_cost_ra pc) cg_a_cost 1 3 16 ltac:(lia) ltac:(lia) ltac:(lia)).

Lemma cg_Pc_spec : RA.ra_compiled (cg_cost_ra pc) cg_a_cost 1 3 16 cg_Pc.
Proof. unfold cg_Pc. exact (proj2_sig _). Qed.

Definition cg_a_erI : nat := cg_a_cost + length cg_Pc.
Definition cg_CHK : nat := cg_a_erI + 8.
Definition cg_a_read : nat := cg_a_erI + 10.

(* READ, at its own address 0: input S = 0, answer B = 5. *)
(* SAFE: the code address 0 of the READ block, not an unset quantity. *)
Definition cg_ig : nat := 0.

Definition cg_Pr : list (mm_instr nat) :=
  proj1_sig (@RA.ra_compiler 1 (cg_read_ra pc) cg_ig 0 5 16 ltac:(lia) ltac:(lia) ltac:(lia)).

Lemma cg_Pr_spec : RA.ra_compiled (cg_read_ra pc) cg_ig 0 5 16 cg_Pr.
Proof. unfold cg_Pr. exact (proj2_sig _). Qed.

(* The counting register: above 16 and above every register READ names. *)
Definition cg_T : nat := 16 + cg_maxreg cg_Pr.

Lemma cg_T_ge : 16 <= cg_T.
Proof. unfold cg_T. lia. Qed.

Lemma cg_T_fresh : cg_fresh cg_T cg_Pr.
Proof.
  intros J HJ. generalize (cg_maxreg_in cg_Pr J HJ). unfold cg_T. lia.
Qed.

Definition cg_a_tail : nat := cg_a_read + 2 * length cg_Pr.
Definition cg_NEW : nat := cg_a_tail + 4.
Definition cg_NORAISE : nat := cg_a_tail + 9.
Definition cg_PL : nat := cg_a_tail + 11.
Definition cg_HALTB : nat := cg_a_tail + 14.

Definition cg_SRC : list cg_xinstr :=
  XMM (mm_dec 8 cg_CHK) ::
  map XMM cg_Pn ++
  XMM (mm_dec 2 cg_HALTB) ::
  map XMM (mm_transfert 2 1 8 (3 + length cg_Pn)) ++
  map XMM cg_Ps ++
  map XMM cg_Pc ++
  map XMM (mm_erase 1 8 cg_a_erI) ++
  map XMM (mm_erase 0 8 (cg_a_erI + 2)) ++
  map XMM (mm_transfert 4 0 8 (cg_a_erI + 4)) ++
  XMM (mm_dec 8 cg_CHK) ::
  map XMM (mm_erase cg_T 8 cg_CHK) ++
  map XMM (cg_count_code cg_T cg_Pr cg_ig cg_a_read) ++
  XMM (mm_dec 5 cg_NORAISE) :: XMM (mm_dec 7 cg_NEW) :: XMM (mm_inc 7) ::
  XMM (mm_dec 8 cg_NORAISE) :: XEARN :: XMM (mm_inc 7) ::
  XMM (mm_dec 3 (cg_NEW + 3)) :: XMM (mm_dec 3 (cg_NEW + 4)) ::
  XMM (mm_dec 3 (cg_NEW + 5)) ::
  map XMM (mm_erase cg_T 8 cg_NORAISE) ++
  XMM (mm_dec 3 2) :: XPAY :: XMM (mm_dec 8 cg_PL) :: XHALT :: [].

(* Registers below k are coded; every register the program names is below k. *)
Definition cg_k : nat := S (cg_xmax cg_SRC).

(* The code of the reading routine for the fixed checker. *)
Definition cg_r : nat := cg_renc cg_ig cg_Pr 0 5 cg_T 16.

Local Notation X := (cg_xstep cg_k cg_r).
Local Notation Xc := (sss_compute X (1, cg_SRC)).
Local Notation Xp := (sss_progress X (1, cg_SRC)).

Lemma cg_src_reg : forall J, In (XMM J) cg_SRC -> cg_xreg J < cg_k.
Proof.
  intros J H. unfold cg_k. generalize (cg_xmax_in cg_SRC J H).
  destruct J; simpl; lia.
Qed.

(* ================================================================= *)
(* Locating the blocks.                                                *)
(* ================================================================= *)

Ltac cg_addr :=
  unfold cg_HALTB, cg_PL, cg_NORAISE, cg_NEW, cg_a_tail, cg_a_read, cg_CHK, cg_a_erI,
    cg_a_cost, cg_a_step;
  rewrite ?app_length, ?map_length, ?mm_transfert_length, ?mm_erase_length,
    ?cg_count_code_length; cbn [length]; lia.

Ltac cg_sc :=
  match goal with
  | |- (_, [?x]) <sc (_, ?x :: _) =>
      (apply cg_sc_here1; cg_addr) || (apply cg_sc_cons; cg_sc)
  | |- (_, ?l) <sc (_, ?l ++ _) =>
      (apply cg_sc_here; cg_addr) || (apply cg_sc_app; cg_sc)
  | |- _ <sc (_, _ :: _) => apply cg_sc_cons; cg_sc
  | |- _ <sc (_, _ ++ _) => apply cg_sc_app; cg_sc
  end.

Lemma cg_sc_jmp0 : (1, [XMM (mm_dec 8 cg_CHK)]) <sc (1, cg_SRC).
Proof. unfold cg_SRC. cg_sc. Qed.
Lemma cg_sc_next : (2, map XMM cg_Pn) <sc (1, cg_SRC).
Proof. unfold cg_SRC. cg_sc. Qed.
Lemma cg_sc_dech : (2 + length cg_Pn, [XMM (mm_dec 2 cg_HALTB)]) <sc (1, cg_SRC).
Proof. unfold cg_SRC. cg_sc. Qed.
Lemma cg_sc_tr1 :
  (3 + length cg_Pn, map XMM (mm_transfert 2 1 8 (3 + length cg_Pn))) <sc (1, cg_SRC).
Proof. unfold cg_SRC. cg_sc. Qed.
Lemma cg_sc_step : (cg_a_step, map XMM cg_Ps) <sc (1, cg_SRC).
Proof. unfold cg_SRC. cg_sc. Qed.
Lemma cg_sc_cost : (cg_a_cost, map XMM cg_Pc) <sc (1, cg_SRC).
Proof. unfold cg_SRC. cg_sc. Qed.
Lemma cg_sc_erI : (cg_a_erI, map XMM (mm_erase 1 8 cg_a_erI)) <sc (1, cg_SRC).
Proof. unfold cg_SRC. cg_sc. Qed.
Lemma cg_sc_erS : (cg_a_erI + 2, map XMM (mm_erase 0 8 (cg_a_erI + 2))) <sc (1, cg_SRC).
Proof. unfold cg_SRC. cg_sc. Qed.
Lemma cg_sc_tr2 : (cg_a_erI + 4, map XMM (mm_transfert 4 0 8 (cg_a_erI + 4))) <sc (1, cg_SRC).
Proof. unfold cg_SRC. cg_sc. Qed.
Lemma cg_sc_jmp1 : (cg_a_erI + 7, [XMM (mm_dec 8 cg_CHK)]) <sc (1, cg_SRC).
Proof. unfold cg_SRC. cg_sc. Qed.
Lemma cg_sc_erT : (cg_CHK, map XMM (mm_erase cg_T 8 cg_CHK)) <sc (1, cg_SRC).
Proof. unfold cg_SRC. cg_sc. Qed.
Lemma cg_sc_read :
  (cg_a_read, map XMM (cg_count_code cg_T cg_Pr cg_ig cg_a_read)) <sc (1, cg_SRC).
Proof. unfold cg_SRC. cg_sc. Qed.
Lemma cg_sc_decB : (cg_a_tail, [XMM (mm_dec 5 cg_NORAISE)]) <sc (1, cg_SRC).
Proof. unfold cg_SRC. cg_sc. Qed.
Lemma cg_sc_decE : (cg_a_tail + 1, [XMM (mm_dec 7 cg_NEW)]) <sc (1, cg_SRC).
Proof. unfold cg_SRC. cg_sc. Qed.
Lemma cg_sc_incE1 : (cg_a_tail + 2, [XMM (mm_inc 7)]) <sc (1, cg_SRC).
Proof. unfold cg_SRC. cg_sc. Qed.
Lemma cg_sc_jmp2 : (cg_a_tail + 3, [XMM (mm_dec 8 cg_NORAISE)]) <sc (1, cg_SRC).
Proof. unfold cg_SRC. cg_sc. Qed.
Lemma cg_sc_earn : (cg_NEW, [XEARN]) <sc (1, cg_SRC).
Proof. unfold cg_SRC. cg_sc. Qed.
Lemma cg_sc_incE2 : (cg_NEW + 1, [XMM (mm_inc 7)]) <sc (1, cg_SRC).
Proof. unfold cg_SRC. cg_sc. Qed.
Lemma cg_sc_decC1 : (cg_NEW + 2, [XMM (mm_dec 3 (cg_NEW + 3))]) <sc (1, cg_SRC).
Proof. unfold cg_SRC. cg_sc. Qed.
Lemma cg_sc_decC2 : (cg_NEW + 3, [XMM (mm_dec 3 (cg_NEW + 4))]) <sc (1, cg_SRC).
Proof. unfold cg_SRC. cg_sc. Qed.
Lemma cg_sc_decC3 : (cg_NEW + 4, [XMM (mm_dec 3 (cg_NEW + 5))]) <sc (1, cg_SRC).
Proof. unfold cg_SRC. cg_sc. Qed.
Lemma cg_sc_erT2 : (cg_NORAISE, map XMM (mm_erase cg_T 8 cg_NORAISE)) <sc (1, cg_SRC).
Proof. unfold cg_SRC. cg_sc. Qed.
Lemma cg_sc_pl : (cg_PL, [XMM (mm_dec 3 2)]) <sc (1, cg_SRC).
Proof. unfold cg_SRC. cg_sc. Qed.
Lemma cg_sc_pay : (cg_PL + 1, [XPAY]) <sc (1, cg_SRC).
Proof. unfold cg_SRC. cg_sc. Qed.
Lemma cg_sc_jmp3 : (cg_PL + 2, [XMM (mm_dec 8 cg_PL)]) <sc (1, cg_SRC).
Proof. unfold cg_SRC. cg_sc. Qed.
Lemma cg_sc_halt : (cg_HALTB, [XHALT]) <sc (1, cg_SRC).
Proof. unfold cg_SRC. cg_sc. Qed.

Lemma cg_k_gt : 8 < cg_k /\ cg_T < cg_k.
Proof.
  split.
  - apply (cg_src_reg (mm_dec 8 cg_CHK)). eapply cg_sc_in; [exact cg_sc_jmp0 | left; reflexivity].
  - apply (cg_src_reg (mm_dec cg_T (2 + cg_CHK))).
    eapply cg_sc_in; [exact cg_sc_erT | left; reflexivity].
Qed.

(* ================================================================= *)
(* Register files.                                                     *)
(* ================================================================= *)

Definition cg_rf (vS vI vH vC vS' vB vE vT : nat) (y : nat) : nat :=
  if Nat.eqb y 0 then vS else if Nat.eqb y 1 then vI else
  if Nat.eqb y 2 then vH else if Nat.eqb y 3 then vC else
  if Nat.eqb y 4 then vS' else if Nat.eqb y 5 then vB else
  if Nat.eqb y 7 then vE else if Nat.eqb y cg_T then vT else 0.

Ltac cg_rf_tac :=
  generalize cg_T_ge; generalize cg_k_gt; unfold cg_rf;
  repeat (match goal with |- context [Nat.eqb ?a ?b] => destruct (Nat.eqb_spec a b) end;
          cbv beta iota);
  intros; first [reflexivity | lia].

Lemma cg_rf_high : forall vS vI vH vC vS' vB vE vT y,
  cg_k <= y -> cg_rf vS vI vH vC vS' vB vE vT y = 0.
Proof. intros. cg_rf_tac. Qed.

Lemma cg_rf_spare : forall vS vI vH vC vS' vB vE y,
  16 <= y -> cg_rf vS vI vH vC vS' vB vE 0 y = 0.
Proof. intros. cg_rf_tac. Qed.

Definition cg_eqv (e : env nat nat) (f : nat -> nat) : Prop := forall y, e y = f y.

Lemma cg_eqv_zero_high : forall e vS vI vH vC vS' vB vE vT,
  cg_eqv e (cg_rf vS vI vH vC vS' vB vE vT) -> forall y, cg_k <= y -> e y = 0.
Proof. intros e vS vI vH vC vS' vB vE vT H y Hy. rewrite H. apply cg_rf_high. exact Hy. Qed.

Lemma cg_eqv_spare : forall e vS vI vH vC vS' vB vE,
  cg_eqv e (cg_rf vS vI vH vC vS' vB vE 0) -> forall y, 16 <= y -> get_env e y = 0.
Proof. intros e vS vI vH vC vS' vB vE H y Hy. apply (eq_trans (H y)). apply cg_rf_spare. exact Hy. Qed.

(* Setting one register of a register file. *)
Ltac cg_set He He' :=
  apply (cg_set_rf _ _ _ _ _ _ He He'); [cg_rf_tac | intros; cg_rf_tac].

(* Reading one register of a register file. *)
Ltac cg_get He := rewrite ?cg_get_env, He; cg_rf_tac.

(* Inputs of one-input and two-input routines. *)
Lemma cg_in1 : forall (e : env nat nat) p x,
  e p = x -> forall q : pos 1, get_env e (pos2nat q + p) = vec_pos (x ## vec_nil) q.
Proof.
  intros e p x H q. invert pos q; [rewrite pos2nat_fst; exact H | invert pos q].
Qed.

Lemma cg_in2 : forall (e : env nat nat) x y,
  e 0 = x -> e 1 = y -> forall q : pos 2, get_env e (pos2nat q + 0) = vec_pos (x ## y ## vec_nil) q.
Proof.
  intros e x y H0 H1 q. invert pos q; [rewrite pos2nat_fst; exact H0 |].
  invert pos q; [rewrite pos2nat_nxt, pos2nat_fst; exact H1 | invert pos q].
Qed.

(* ================================================================= *)
(* Moves of X.                                                         *)
(* ================================================================= *)

Lemma cg_x_block : forall a Q i e j e' aux,
  (a, map XMM Q) <sc (1, cg_SRC) ->
  sss_compute (mm_sss_env eq_nat_dec) (a, Q) (i, e) (j, e') ->
  Xc (i, (e, aux)) (j, (e', aux)).
Proof.
  intros a Q i e j e' aux Hsc [q Hq]. exists q.
  apply subcode_sss_steps with (1 := Hsc). apply cg_lift_mm; [| exact Hq].
  intros J HJ. apply cg_src_reg. eapply cg_sc_in; [exact Hsc |]. apply in_map. exact HJ.
Qed.

Lemma cg_x_block_p : forall a Q i e j e' aux,
  (a, map XMM Q) <sc (1, cg_SRC) ->
  sss_progress (mm_sss_env eq_nat_dec) (a, Q) (i, e) (j, e') ->
  Xp (i, (e, aux)) (j, (e', aux)).
Proof.
  intros a Q i e j e' aux Hsc (q & Hq0 & Hq). exists q. split; [exact Hq0 |].
  apply subcode_sss_steps with (1 := Hsc). apply cg_lift_mm; [| exact Hq].
  intros J HJ. apply cg_src_reg. eapply cg_sc_in; [exact Hsc |]. apply in_map. exact HJ.
Qed.

Lemma cg_x_one : forall i J e j e' aux,
  (i, [XMM J]) <sc (1, cg_SRC) ->
  mm_sss_env eq_nat_dec J (i, e) (j, e') ->
  Xp (i, (e, aux)) (j, (e', aux)).
Proof.
  intros i J e j e' aux Hsc Hs. apply (cg_x_block_p i [J]); [exact Hsc |].
  exists 1. split; [lia |]. apply sss_steps_1.
  change (i, [J]) with (i, [] ++ J :: []). apply in_sss_step; [simpl; lia | exact Hs].
Qed.

Lemma cg_x_dec0 : forall i x j e aux,
  (i, [XMM (mm_dec x j)]) <sc (1, cg_SRC) -> e x = 0 ->
  Xp (i, (e, aux)) (j, (e, aux)).
Proof. intros. apply (cg_x_one i (mm_dec x j)); [assumption | constructor; assumption]. Qed.

Lemma cg_x_decS : forall i x j e u aux,
  (i, [XMM (mm_dec x j)]) <sc (1, cg_SRC) -> e x = S u ->
  Xp (i, (e, aux)) (1 + i, (set_env eq_nat_dec e x u, aux)).
Proof. intros. apply (cg_x_one i (mm_dec x j)); [assumption | constructor; assumption]. Qed.

Lemma cg_x_inc : forall i x e aux,
  (i, [XMM (mm_inc x)]) <sc (1, cg_SRC) ->
  Xp (i, (e, aux)) (1 + i, (set_env eq_nat_dec e x (S (e x)), aux)).
Proof. intros. apply (cg_x_one i (mm_inc x)); [assumption | constructor]. Qed.

Lemma cg_x_pay : forall i e aux,
  (i, [XPAY]) <sc (1, cg_SRC) -> Xp (i, (e, aux)) (S i, (e, cg_pay aux)).
Proof.
  intros i e aux Hsc. apply subcode_sss_progress with (1 := Hsc).
  exists 1. split; [lia |]. apply sss_steps_1.
  change (i, [XPAY]) with (i, [] ++ XPAY :: []). apply in_sss_step; [simpl; lia | constructor].
Qed.

Lemma cg_x_earn : forall i e aux,
  (i, [XEARN]) <sc (1, cg_SRC) ->
  cg_ueval (URun cg_r) (cg_gk cg_k e) = true -> cg_a_earned aux = false ->
  Xp (i, (e, aux)) (S i, (e, cg_earn aux)).
Proof.
  intros i e aux Hsc H1 H2. apply subcode_sss_progress with (1 := Hsc).
  exists 1. split; [lia |]. apply sss_steps_1.
  change (i, [XEARN]) with (i, [] ++ XEARN :: []).
  apply in_sss_step; [simpl; lia | constructor; assumption].
Qed.

(* A decrement that goes on to the next address either way. *)
Lemma cg_x_dec_next : forall i x e aux,
  (i, [XMM (mm_dec x (1 + i))]) <sc (1, cg_SRC) ->
  exists e', cg_eqv e' (set_env eq_nat_dec e x (e x - 1)) /\
    Xp (i, (e, aux)) (1 + i, (e', aux)).
Proof.
  intros i x e aux Hsc. destruct (e x) as [| u] eqn:Ex.
  - exists e. split.
    + intros y. unfold set_env. destruct (eq_nat_dec x y) as [<- | _]; [exact Ex | reflexivity].
    + apply cg_x_dec0 with (x := x); assumption.
  - exists (set_env eq_nat_dec e x u). split.
    + intros y. replace (S u - 1) with u by lia. reflexivity.
    + apply cg_x_decS with (x := x) (j := 1 + i); assumption.
Qed.

Lemma cg_x_erase : forall a x e aux,
  x <> 8 -> (a, map XMM (mm_erase x 8 a)) <sc (1, cg_SRC) -> e 8 = 0 ->
  exists e', cg_eqv e' (set_env eq_nat_dec e x 0) /\ Xp (a, (e, aux)) (2 + a, (e', aux)).
Proof.
  intros a x e aux Hx Hsc H8.
  destruct (@mm_erase_progress x 8 Hx a e H8) as (e' & He' & Hp).
  exists e'. split; [exact He' |]. apply (cg_x_block_p a _ _ _ _ _ _ Hsc Hp).
Qed.

Lemma cg_x_transfert : forall a src dst e aux,
  src <> dst -> src <> 8 -> dst <> 8 ->
  (a, map XMM (mm_transfert src dst 8 a)) <sc (1, cg_SRC) -> e dst = 0 -> e 8 = 0 ->
  exists e', cg_eqv e' (set_env eq_nat_dec (set_env eq_nat_dec e src 0) dst (e src)) /\
    Xp (a, (e, aux)) (3 + a, (e', aux)).
Proof.
  intros a src dst e aux H1 H2 H3 Hsc Hd H8.
  destruct (@mm_transfert_progress src dst 8 H1 H2 H3 a e Hd H8) as (e' & He' & Hp).
  exists e'. split; [exact He' |]. apply (cg_x_block_p a _ _ _ _ _ _ Hsc Hp).
Qed.

(* ================================================================= *)
(* The pay loop.                                                       *)
(* ================================================================= *)

Lemma cg_x_payloop : forall c vS vE e mu ct ea,
  cg_eqv e (cg_rf vS 0 0 c 0 0 vE 0) ->
  exists e', cg_eqv e' (cg_rf vS 0 0 0 0 0 vE 0) /\
    Xp (cg_PL, (e, cg_mkaux mu ct ea)) (2, (e', cg_mkaux (mu + c) ct ea)).
Proof.
  induction c as [| c IH]; intros vS vE e mu ct ea He.
  - exists e. split; [intros y; rewrite He; cg_rf_tac |].
    rewrite Nat.add_0_r. apply cg_x_dec0 with (x := 3); [exact cg_sc_pl | cg_get He].
  - set (e1 := set_env eq_nat_dec e 3 c).
    assert (He1 : cg_eqv e1 (cg_rf vS 0 0 c 0 0 vE 0))
      by (intros y; cg_set He (fun y : nat => eq_refl (e1 y))).
    destruct (IH vS vE e1 (S mu) ct ea He1) as (e' & He' & Hp).
    exists e'. split; [exact He' |].
    eapply sss_progress_trans.
    { apply cg_x_decS with (x := 3) (j := 2); [exact cg_sc_pl | cg_get He]. }
    eapply sss_progress_trans.
    { apply cg_x_pay. replace (1 + cg_PL) with (cg_PL + 1) by lia. exact cg_sc_pay. }
    eapply sss_progress_trans.
    { replace (S (1 + cg_PL)) with (cg_PL + 2) by lia.
      apply cg_x_dec0 with (x := 8); [exact cg_sc_jmp3 | cg_get He1]. }
    replace (mu + S c) with (S mu + c) by lia. exact Hp.
Qed.

Lemma cg_set2_rf : forall (w w' : env nat nat) (f g : nat -> nat) src dst,
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

Ltac cg_set2 He He' :=
  apply (cg_set2_rf _ _ _ _ _ _ He He'); [lia | cg_rf_tac | cg_rf_tac | intros; cg_rf_tac].

(* ================================================================= *)
(* From HEAD to CHK: one driven move.                                  *)
(* ================================================================= *)

Lemma cg_x_move : forall s i vE e aux,
  cg_eqv e (cg_rf (sc s) 0 0 0 0 0 vE 0) -> pm_next M s = Some i ->
  exists e', cg_eqv e' (cg_rf (sc (cstep s i)) 0 0 (ccost i) 0 0 vE 0) /\
    Xp (2, (e, aux)) (cg_CHK, (e', aux)).
Proof.
  intros s i vE e aux He Hn.
  (* NEXT: H := 1 + code of the move *)
  assert (Hv : cg_next_val M s = S (ic i)) by (unfold cg_next_val; rewrite Hn; reflexivity).
  pose proof (cg_next_spec pc s) as Hrel. rewrite Hv in Hrel.
  destruct (proj1 (cg_Pn_spec (sc s ## vec_nil) e (cg_eqv_spare _ _ _ _ _ _ _ _ He)
                     (cg_in1 e 0 (sc s) ltac:(cg_get He))) _ Hrel) as (e1 & He1 & Hc1).
  assert (E1 : cg_eqv e1 (cg_rf (sc s) 0 (S (ic i)) 0 0 0 vE 0)) by (intros y; cg_set He He1).
  assert (H1 : Xc (2, (e, aux)) (2 + length cg_Pn, (e1, aux))).
  { replace (2 + length cg_Pn) with (length cg_Pn + 2) by lia.
    exact (cg_x_block 2 cg_Pn _ _ _ _ aux cg_sc_next Hc1). }
  (* DEC H HALTB *)
  set (e2 := set_env eq_nat_dec e1 2 (ic i)).
  assert (E2 : cg_eqv e2 (cg_rf (sc s) 0 (ic i) 0 0 0 vE 0))
    by (intros y; cg_set E1 (fun y : nat => eq_refl (e2 y))).
  assert (H2 : Xp (2 + length cg_Pn, (e1, aux)) (3 + length cg_Pn, (e2, aux))).
  { replace (3 + length cg_Pn) with (1 + (2 + length cg_Pn)) by lia.
    apply cg_x_decS with (x := 2) (j := cg_HALTB); [exact cg_sc_dech | cg_get E1]. }
  (* H to I *)
  destruct (cg_x_transfert (3 + length cg_Pn) 2 1 e2 aux ltac:(lia) ltac:(lia) ltac:(lia)
              cg_sc_tr1 ltac:(cg_get E2) ltac:(cg_get E2)) as (e3 & He3 & H3).
  assert (E3 : cg_eqv e3 (cg_rf (sc s) (ic i) 0 0 0 0 vE 0)) by (intros y; cg_set2 E2 He3).
  (* STEP: S' := code of the next state *)
  pose proof (cg_step_spec pc s i) as Hrs.
  destruct (proj1 (cg_Ps_spec (sc s ## ic i ## vec_nil) e3 (cg_eqv_spare _ _ _ _ _ _ _ _ E3)
                     (cg_in2 e3 (sc s) (ic i) ltac:(cg_get E3) ltac:(cg_get E3))) _ Hrs)
    as (e4 & He4 & Hc4).
  assert (E4 : cg_eqv e4 (cg_rf (sc s) (ic i) 0 0 (sc (cstep s i)) 0 vE 0))
    by (intros y; cg_set E3 He4).
  assert (H4 : Xc (cg_a_step, (e3, aux)) (cg_a_cost, (e4, aux))).
  { unfold cg_a_cost. replace (cg_a_step + length cg_Ps) with (length cg_Ps + cg_a_step) by lia.
    exact (cg_x_block _ cg_Ps _ _ _ _ aux cg_sc_step Hc4). }
  (* COST: C := cost of the move *)
  pose proof (cg_cost_spec pc i) as Hrc.
  destruct (proj1 (cg_Pc_spec (ic i ## vec_nil) e4 (cg_eqv_spare _ _ _ _ _ _ _ _ E4)
                     (cg_in1 e4 1 (ic i) ltac:(cg_get E4))) _ Hrc) as (e5 & He5 & Hc5).
  assert (E5 : cg_eqv e5 (cg_rf (sc s) (ic i) 0 (ccost i) (sc (cstep s i)) 0 vE 0))
    by (intros y; cg_set E4 He5).
  assert (H5 : Xc (cg_a_cost, (e4, aux)) (cg_a_erI, (e5, aux))).
  { unfold cg_a_erI. replace (cg_a_cost + length cg_Pc) with (length cg_Pc + cg_a_cost) by lia.
    exact (cg_x_block _ cg_Pc _ _ _ _ aux cg_sc_cost Hc5). }
  (* erase I, erase S, S' to S, JMP CHK *)
  destruct (cg_x_erase cg_a_erI 1 e5 aux ltac:(lia) cg_sc_erI ltac:(cg_get E5)) as (e6 & He6 & H6).
  assert (E6 : cg_eqv e6 (cg_rf (sc s) 0 0 (ccost i) (sc (cstep s i)) 0 vE 0))
    by (intros y; cg_set E5 He6).
  destruct (cg_x_erase (cg_a_erI + 2) 0 e6 aux ltac:(lia) cg_sc_erS ltac:(cg_get E6))
    as (e7 & He7 & H7).
  assert (E7 : cg_eqv e7 (cg_rf 0 0 0 (ccost i) (sc (cstep s i)) 0 vE 0))
    by (intros y; cg_set E6 He7).
  destruct (cg_x_transfert (cg_a_erI + 4) 4 0 e7 aux ltac:(lia) ltac:(lia) ltac:(lia)
              cg_sc_tr2 ltac:(cg_get E7) ltac:(cg_get E7)) as (e8 & He8 & H8).
  assert (E8 : cg_eqv e8 (cg_rf (sc (cstep s i)) 0 0 (ccost i) 0 0 vE 0))
    by (intros y; cg_set2 E7 He8).
  assert (H9 : Xp (cg_a_erI + 7, (e8, aux)) (cg_CHK, (e8, aux)))
    by (apply cg_x_dec0 with (x := 8); [exact cg_sc_jmp1 | cg_get E8]).
  exists e8. split; [exact E8 |].
  replace (2 + cg_a_erI) with (cg_a_erI + 2) in H6 by lia.
  replace (2 + (cg_a_erI + 2)) with (cg_a_erI + 4) in H7 by lia.
  replace (3 + (cg_a_erI + 4)) with (cg_a_erI + 7) in H8 by lia.
  replace (3 + (3 + length cg_Pn)) with cg_a_step in H3 by (unfold cg_a_step; lia).
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
Lemma cg_x_halt : forall s vE e aux,
  cg_eqv e (cg_rf (sc s) 0 0 0 0 0 vE 0) -> pm_next M s = None ->
  exists e', cg_eqv e' (cg_rf (sc s) 0 0 0 0 0 vE 0) /\
    Xp (2, (e, aux)) (cg_HALTB, (e', aux)).
Proof.
  intros s vE e aux He Hn.
  assert (Hv : cg_next_val M s = 0) by (unfold cg_next_val; rewrite Hn; reflexivity).
  pose proof (cg_next_spec pc s) as Hrel. rewrite Hv in Hrel.
  destruct (proj1 (cg_Pn_spec (sc s ## vec_nil) e (cg_eqv_spare _ _ _ _ _ _ _ _ He)
                     (cg_in1 e 0 (sc s) ltac:(cg_get He))) _ Hrel) as (e1 & He1 & Hc1).
  assert (E1 : cg_eqv e1 (cg_rf (sc s) 0 0 0 0 0 vE 0)) by (intros y; cg_set He He1).
  exists e1. split; [exact E1 |].
  eapply sss_compute_progress_trans.
  { replace (length cg_Pn + 2) with (2 + length cg_Pn) in Hc1 by lia.
    exact (cg_x_block 2 cg_Pn _ _ _ _ aux cg_sc_next Hc1). }
  apply cg_x_dec0 with (x := 2); [exact cg_sc_dech | cg_get E1].
Qed.

(* ================================================================= *)
(* From CHK: the reading, counted.                                     *)
(* ================================================================= *)

Lemma cg_x_read : forall s c vE e aux,
  cg_eqv e (cg_rf (sc s) 0 0 c 0 0 vE 0) ->
  exists t w1, cg_eqv w1 (cg_rf (sc s) 0 0 c 0 (if rd s then 1 else 0) vE t) /\
    Xp (cg_CHK, (e, aux)) (cg_a_tail, (w1, aux)) /\
    (forall ex, cg_eqv ex (cg_rf (sc s) 0 0 c 0 0 vE t) ->
       cg_ueval (URun cg_r) (cg_gk cg_k ex) = rd s).
Proof.
  intros s c vE e aux He.
  destruct (cg_x_erase cg_CHK cg_T e aux ltac:(generalize cg_T_ge; lia) cg_sc_erT ltac:(cg_get He))
    as (e1 & He1 & H1).
  assert (E1 : cg_eqv e1 (cg_rf (sc s) 0 0 c 0 0 vE 0)) by (intros y; cg_set He He1).
  pose proof (cg_read_spec pc (sc s)) as Hrel. rewrite cg_read_val_code in Hrel.
  destruct (proj1 (cg_Pr_spec (sc s ## vec_nil) e1 (cg_eqv_spare _ _ _ _ _ _ _ _ E1)
                     (cg_in1 e1 0 (sc s) ltac:(cg_get E1))) _ Hrel) as (e2 & He2 & [t Ht]).
  assert (Hout : out_code (length cg_Pr + cg_ig) (cg_ig, cg_Pr))
    by (simpl; unfold code_end; simpl; lia).
  destruct (cg_read_T_spec cg_T cg_Pr cg_ig cg_a_read t e1 _ e2 e1 cg_T_fresh Ht Hout
              ltac:(cg_get E1) (fun _ _ => eq_refl)) as (w1 & [Hc _] & HT & Hw1).
  assert (W1 : cg_eqv w1 (cg_rf (sc s) 0 0 c 0 (if rd s then 1 else 0) vE t)).
  { intros y. destruct (Nat.eq_dec y cg_T) as [-> | Hne].
    - rewrite HT. cg_rf_tac.
    - rewrite (Hw1 y Hne). change (e2 y) with (get_env e2 y). rewrite He2.
      unfold get_env, set_env. destruct (eq_nat_dec 5 y) as [<- | Hne5]; [cg_rf_tac |].
      rewrite E1. cg_rf_tac. }
  exists t, w1. split; [exact W1 |]. split.
  - eapply sss_progress_compute_trans; [exact H1 |].
    replace (2 + cg_CHK) with cg_a_read by (unfold cg_a_read, cg_CHK; lia).
    exact (cg_x_block _ _ _ _ _ _ aux cg_sc_read Hc).
  - intros ex Hex.
    assert (Hz : forall y, cg_k <= y -> ex y = 0) by (exact (cg_eqv_zero_high _ _ _ _ _ _ _ _ _ Hex)).
    cbn [cg_ueval]. unfold cg_r. rewrite cg_rdec_renc. unfold cg_run_check.
    rewrite (cg_expo_gk_zero cg_k ex cg_T Hz).
    replace (ex cg_T) with t by (symmetry; cg_get Hex).
    assert (Hpt : forall x, get_env (cg_env_chk 16 (cg_gk cg_k ex)) x = get_env e1 x).
    { intros x. rewrite (cg_env_chk_gk cg_k ex 16 x Hz). rewrite cg_get_env, E1.
      destruct (Nat.ltb_spec x 16); [rewrite Hex; cg_rf_tac | cg_rf_tac]. }
    destruct (cg_mme_run_ext t (cg_ig, cg_Pr) cg_ig _ _ Hpt) as [Hf Hs].
    rewrite (cg_mme_run_fuel_complete _ _ _ _ Ht Hout t (le_n t)) in Hf, Hs.
    cbn [fst] in Hf. cbv zeta. rewrite Hf.
    replace (cg_out_codeb (cg_ig, cg_Pr) (length cg_Pr + cg_ig)) with true
      by (symmetry; apply cg_out_codeb_spec; exact Hout).
    rewrite Hs. cbn [snd]. rewrite He2. unfold get_env, set_env.
    destruct (eq_nat_dec 5 5) as [_ | C]; [| congruence].
    destruct (rd s); reflexivity.
Qed.

(* ================================================================= *)
(* After the reading.                                                  *)
(* ================================================================= *)

Lemma cg_x_noraise : forall vS c vE t w mu ct ea,
  cg_eqv w (cg_rf vS 0 0 c 0 0 vE t) ->
  exists e', cg_eqv e' (cg_rf vS 0 0 0 0 0 vE 0) /\
    Xp (cg_NORAISE, (w, cg_mkaux mu ct ea)) (2, (e', cg_mkaux (mu + c) ct ea)).
Proof.
  intros vS c vE t w mu ct ea Hw.
  destruct (cg_x_erase cg_NORAISE cg_T w (cg_mkaux mu ct ea) ltac:(generalize cg_T_ge; lia)
              cg_sc_erT2 ltac:(cg_get Hw)) as (w1 & Hw1 & H1).
  assert (W1 : cg_eqv w1 (cg_rf vS 0 0 c 0 0 vE 0)) by (intros y; cg_set Hw Hw1).
  destruct (cg_x_payloop c vS vE w1 mu ct ea W1) as (e' & He' & H2).
  exists e'. split; [exact He' |].
  replace (2 + cg_NORAISE) with cg_PL in H1 by (unfold cg_PL, cg_NORAISE; lia).
  eapply sss_progress_trans; [exact H1 | exact H2].
Qed.

(* At the first raise: from the end of the reading to NEW. *)
Lemma cg_x_tail_new : forall vS c t w aux,
  cg_eqv w (cg_rf vS 0 0 c 0 1 0 t) ->
  exists ex, cg_eqv ex (cg_rf vS 0 0 c 0 0 0 t) /\
    Xp (cg_a_tail, (w, aux)) (cg_NEW, (ex, aux)).
Proof.
  intros vS c t w aux Hw.
  set (w1 := set_env eq_nat_dec w 5 0).
  assert (W1 : cg_eqv w1 (cg_rf vS 0 0 c 0 0 0 t))
    by (intros y; cg_set Hw (fun y : nat => eq_refl (w1 y))).
  exists w1. split; [exact W1 |].
  eapply sss_progress_trans.
  { apply cg_x_decS with (x := 5) (j := cg_NORAISE); [exact cg_sc_decB | cg_get Hw]. }
  replace (1 + cg_a_tail) with (cg_a_tail + 1) by lia.
  apply cg_x_dec0 with (x := 7); [exact cg_sc_decE | cg_get W1].
Qed.

Lemma cg_x_tail : forall s c (l : bool) t w1 mu,
  cg_eqv w1 (cg_rf (sc s) 0 0 c 0 (if rd s then 1 else 0) (if l then 1 else 0) t) ->
  (forall ex, cg_eqv ex (cg_rf (sc s) 0 0 c 0 0 (if l then 1 else 0) t) ->
     cg_ueval (URun cg_r) (cg_gk cg_k ex) = rd s) ->
  exists e', cg_eqv e' (cg_rf (sc s) 0 0 0 0 0 (if l || rd s then 1 else 0) 0) /\
    Xp (cg_a_tail, (w1, cg_mkaux mu l l))
       (2, (e', cg_mkaux (mu + cg_chk_pay l (rd s) c) (l || rd s) (l || rd s))).
Proof.
  intros s c l t w1 mu Hw Hchk. unfold cg_chk_pay.
  destruct (rd s) eqn:Rd; destruct l; cbv beta iota delta [orb andb negb] in *.
  - (* latch up, reading yes *)
    set (w2 := set_env eq_nat_dec w1 5 0).
    assert (W2 : cg_eqv w2 (cg_rf (sc s) 0 0 c 0 0 1 t))
      by (intros y; cg_set Hw (fun y : nat => eq_refl (w2 y))).
    set (w3 := set_env eq_nat_dec w2 7 0).
    assert (W3 : cg_eqv w3 (cg_rf (sc s) 0 0 c 0 0 0 t))
      by (intros y; cg_set W2 (fun y : nat => eq_refl (w3 y))).
    set (w4 := set_env eq_nat_dec w3 7 (S (w3 7))).
    assert (W4 : cg_eqv w4 (cg_rf (sc s) 0 0 c 0 0 1 t)).
    { intros y. assert (E : w3 7 = 0) by (cg_get W3).
      apply (cg_set_rf _ _ _ _ _ _ W3 (fun y : nat => eq_refl (w4 y)));
        [rewrite E; cg_rf_tac | intros; cg_rf_tac]. }
    destruct (cg_x_noraise (sc s) c 1 t w4 mu true true W4) as (e' & He' & Hn).
    exists e'. split; [exact He' |].
    eapply sss_progress_trans.
    { apply cg_x_decS with (x := 5) (j := cg_NORAISE); [exact cg_sc_decB | cg_get Hw]. }
    eapply sss_progress_trans.
    { replace (1 + cg_a_tail) with (cg_a_tail + 1) by lia.
      apply cg_x_decS with (x := 7) (j := cg_NEW); [exact cg_sc_decE | cg_get W2]. }
    eapply sss_progress_trans.
    { replace (1 + (cg_a_tail + 1)) with (cg_a_tail + 2) by lia.
      apply cg_x_inc. exact cg_sc_incE1. }
    eapply sss_progress_trans; [| exact Hn].
    replace (1 + (cg_a_tail + 2)) with (cg_a_tail + 3) by lia.
    apply cg_x_dec0 with (x := 8); [exact cg_sc_jmp2 | cg_get W4].
  - (* first raise *)
    destruct (cg_x_tail_new (sc s) c t w1 (cg_mkaux mu false false) Hw) as (ex & Hex & H1).
    pose proof (Hchk ex Hex) as Hck.
    set (x1 := set_env eq_nat_dec ex 7 (S (ex 7))).
    assert (X1 : cg_eqv x1 (cg_rf (sc s) 0 0 c 0 0 1 t)).
    { intros y. assert (E : ex 7 = 0) by (cg_get Hex).
      apply (cg_set_rf _ _ _ _ _ _ Hex (fun y : nat => eq_refl (x1 y)));
        [rewrite E; cg_rf_tac | intros; cg_rf_tac]. }
    destruct (cg_x_dec_next (cg_NEW + 2) 3 x1 (cg_earn (cg_mkaux mu false false)) ltac:(
                replace (1 + (cg_NEW + 2)) with (cg_NEW + 3) by lia; exact cg_sc_decC1))
      as (x2 & Hx2 & H4).
    assert (X2 : cg_eqv x2 (cg_rf (sc s) 0 0 (c - 1) 0 0 1 t)).
    { intros y. assert (E : x1 3 = c) by (cg_get X1). rewrite E in Hx2. cg_set X1 Hx2. }
    destruct (cg_x_dec_next (cg_NEW + 3) 3 x2 (cg_earn (cg_mkaux mu false false)) ltac:(
                replace (1 + (cg_NEW + 3)) with (cg_NEW + 4) by lia; exact cg_sc_decC2))
      as (x3 & Hx3 & H5).
    assert (X3 : cg_eqv x3 (cg_rf (sc s) 0 0 (c - 1 - 1) 0 0 1 t)).
    { intros y. assert (E : x2 3 = c - 1) by (cg_get X2). rewrite E in Hx3. cg_set X2 Hx3. }
    destruct (cg_x_dec_next (cg_NEW + 4) 3 x3 (cg_earn (cg_mkaux mu false false)) ltac:(
                replace (1 + (cg_NEW + 4)) with (cg_NEW + 5) by lia; exact cg_sc_decC3))
      as (x4 & Hx4 & H6).
    assert (X4 : cg_eqv x4 (cg_rf (sc s) 0 0 (c - 1 - 1 - 1) 0 0 1 t)).
    { intros y. assert (E : x3 3 = c - 1 - 1) by (cg_get X3). rewrite E in Hx4. cg_set X3 Hx4. }
    destruct (cg_x_noraise (sc s) (c - 1 - 1 - 1) 1 t x4 (mu + 3) true true X4)
      as (e' & He' & Hn).
    exists e'. split; [exact He' |].
    eapply sss_progress_trans; [exact H1 |].
    eapply sss_progress_trans.
    { apply cg_x_earn; [exact cg_sc_earn | exact Hck | reflexivity]. }
    eapply sss_progress_trans.
    { replace (S cg_NEW) with (cg_NEW + 1) by lia. apply cg_x_inc. exact cg_sc_incE2. }
    replace (1 + (cg_NEW + 1)) with (cg_NEW + 2) by lia.
    replace (1 + (cg_NEW + 2)) with (cg_NEW + 3) in H4 by lia.
    replace (1 + (cg_NEW + 3)) with (cg_NEW + 4) in H5 by lia.
    replace (1 + (cg_NEW + 4)) with cg_NORAISE in H6 by (unfold cg_NORAISE, cg_NEW; lia).
    eapply sss_progress_trans; [exact H4 |].
    eapply sss_progress_trans; [exact H5 |].
    eapply sss_progress_trans; [exact H6 |].
    replace (mu + (3 + (c - 3))) with (mu + 3 + (c - 1 - 1 - 1)) by lia. exact Hn.
  - (* latch up, reading no *)
    destruct (cg_x_noraise (sc s) c 1 t w1 mu true true Hw) as (e' & He' & Hn).
    exists e'. split; [exact He' |].
    eapply sss_progress_trans; [| exact Hn].
    apply cg_x_dec0 with (x := 5); [exact cg_sc_decB | cg_get Hw].
  - (* latch down, reading no *)
    destruct (cg_x_noraise (sc s) c 0 t w1 mu false false Hw) as (e' & He' & Hn).
    exists e'. split; [exact He' |].
    eapply sss_progress_trans; [| exact Hn].
    apply cg_x_dec0 with (x := 5); [exact cg_sc_decB | cg_get Hw].
Qed.

Lemma cg_x_check : forall s c (l : bool) mu e,
  cg_eqv e (cg_rf (sc s) 0 0 c 0 0 (if l then 1 else 0) 0) ->
  exists e', cg_eqv e' (cg_rf (sc s) 0 0 0 0 0 (if l || rd s then 1 else 0) 0) /\
    Xp (cg_CHK, (e, cg_mkaux mu l l))
       (2, (e', cg_mkaux (mu + cg_chk_pay l (rd s) c) (l || rd s) (l || rd s))).
Proof.
  intros s c l mu e He.
  destruct (cg_x_read s c _ e (cg_mkaux mu l l) He) as (t & w1 & Hw1 & H1 & Hchk).
  destruct (cg_x_tail s c l t w1 mu Hw1 Hchk) as (e' & He' & H2).
  exists e'. split; [exact He' | eapply sss_progress_trans; [exact H1 | exact H2]].
Qed.

(* From CHK at the first raise, to NEW, where the fixed checker accepts. *)
Lemma cg_x_to_new : forall s c e aux,
  cg_eqv e (cg_rf (sc s) 0 0 c 0 0 0 0) -> rd s = true ->
  exists ex t, cg_eqv ex (cg_rf (sc s) 0 0 c 0 0 0 t) /\
    Xp (cg_CHK, (e, aux)) (cg_NEW, (ex, aux)) /\
    cg_ueval (URun cg_r) (cg_gk cg_k ex) = true.
Proof.
  intros s c e aux He Rd.
  destruct (cg_x_read s c 0 e aux He) as (t & w1 & Hw1 & H1 & Hchk).
  rewrite Rd in Hw1.
  destruct (cg_x_tail_new (sc s) c t w1 aux Hw1) as (ex & Hex & H2).
  exists ex, t. split; [exact Hex |]. split; [eapply sss_progress_trans; [exact H1 | exact H2] |].
  rewrite <- Rd. apply Hchk. exact Hex.
Qed.

(* ================================================================= *)
(* The invariant at HEAD, and the three phases.                        *)
(* ================================================================= *)

(* The guest's registers at the start: S holds the code of s0. *)
Definition cg_e0 (s0 : st) : env nat nat := fun y => if Nat.eqb y 0 then sc s0 else 0.

Lemma cg_e0_rf : forall s0, cg_eqv (cg_e0 s0) (cg_rf (sc s0) 0 0 0 0 0 0 0).
Proof. intros s0 y. unfold cg_e0. cg_rf_tac. Qed.

Lemma cg_e0_high : forall s0 y, cg_k <= y -> cg_e0 s0 y = 0.
Proof. intros s0 y H. rewrite cg_e0_rf. apply cg_rf_high. exact H. Qed.

(* inv_head n: S holds the code of the state after n driven steps, E the
   latch bit, every other register 0; the record is (ledger + surcharge,
   latch, latch). *)
Definition cg_inv_head (s0 : st) (n : nat) (x : cg_xstate) : Prop :=
  cg_eqv (fst x) (cg_rf (sc (presented_run M s0 n)) 0 0 0 0 0
                    (if mlatch M s0 n then 1 else 0) 0) /\
  snd x = cg_mkaux (mledger M s0 n + surcharge M s0 n) (mlatch M s0 n) (mlatch M s0 n).

Theorem cg_x_prologue : forall s0,
  exists x, cg_inv_head s0 0 x /\ Xp (1, (cg_e0 s0, cg_mkaux 0 false false)) (2, x).
Proof.
  intros s0.
  destruct (cg_x_check s0 0 false 0 (cg_e0 s0) (cg_e0_rf s0)) as (e' & He' & H).
  destruct (cg_account_start M s0) as [Hl Ha].
  exists (e', cg_mkaux (0 + cg_chk_pay false (rd s0) 0) (false || rd s0) (false || rd s0)).
  split; [split |].
  - cbn [fst presented_run]. rewrite Hl. exact He'.
  - cbn [snd]. rewrite Hl, Ha. reflexivity.
  - eapply sss_progress_trans; [| exact H].
    apply cg_x_dec0 with (x := 8); [exact cg_sc_jmp0 | cg_get (cg_e0_rf s0)].
Qed.

Theorem cg_x_step : forall s0 n x i,
  cg_inv_head s0 n x -> pm_next M (presented_run M s0 n) = Some i ->
  exists x', cg_inv_head s0 (S n) x' /\ Xp (2, x) (2, x').
Proof.
  intros s0 n [e a] i [He Ha] Hn. cbn [fst snd] in He, Ha. subst a.
  destruct (cg_x_move _ i _ e (cg_mkaux (mledger M s0 n + surcharge M s0 n)
              (mlatch M s0 n) (mlatch M s0 n)) He Hn) as (e1 & He1 & H1).
  destruct (cg_x_check (cstep (presented_run M s0 n) i) (ccost i) (mlatch M s0 n)
              (mledger M s0 n + surcharge M s0 n) e1 He1) as (e2 & He2 & H2).
  destruct (cg_account_step M s0 n i Hn) as (Hr & Hl & Ha).
  set (b := mlatch M s0 n || rd (cstep (presented_run M s0 n) i)).
  exists (e2, cg_mkaux (mledger M s0 n + surcharge M s0 n +
                        cg_chk_pay (mlatch M s0 n) (rd (cstep (presented_run M s0 n) i)) (ccost i))
                       b b).
  split; [split |].
  - cbn [fst]. rewrite Hr, Hl. exact He2.
  - cbn [snd]. rewrite Hl, Ha. reflexivity.
  - eapply sss_progress_trans; [exact H1 | exact H2].
Qed.

Theorem cg_x_stop : forall s0 n x,
  cg_inv_head s0 n x -> pm_next M (presented_run M s0 n) = None ->
  exists x', cg_inv_head s0 n x' /\ Xp (2, x) (cg_HALTB, x').
Proof.
  intros s0 n [e a] [He Ha] Hn. cbn [fst snd] in He, Ha.
  destruct (cg_x_halt _ _ e a He Hn) as (e1 & He1 & H1).
  exists (e1, a). split; [split; [exact He1 | exact Ha] | exact H1].
Qed.

End Guest.

Print Assumptions cg_maxreg_in.
Print Assumptions cg_xmax_in.
Print Assumptions cg_sc_cons.
Print Assumptions cg_sc_app.
Print Assumptions cg_sc_here1.
Print Assumptions cg_sc_here.
Print Assumptions cg_sc_in.
Print Assumptions cg_set_rf.
Print Assumptions cg_Pn_spec.
Print Assumptions cg_Ps_spec.
Print Assumptions cg_Pc_spec.
Print Assumptions cg_Pr_spec.
Print Assumptions cg_T_ge.
Print Assumptions cg_T_fresh.
Print Assumptions cg_src_reg.
Print Assumptions cg_sc_jmp0.
Print Assumptions cg_sc_next.
Print Assumptions cg_sc_dech.
Print Assumptions cg_sc_tr1.
Print Assumptions cg_sc_step.
Print Assumptions cg_sc_cost.
Print Assumptions cg_sc_erI.
Print Assumptions cg_sc_erS.
Print Assumptions cg_sc_tr2.
Print Assumptions cg_sc_jmp1.
Print Assumptions cg_sc_erT.
Print Assumptions cg_sc_read.
Print Assumptions cg_sc_decB.
Print Assumptions cg_sc_decE.
Print Assumptions cg_sc_incE1.
Print Assumptions cg_sc_jmp2.
Print Assumptions cg_sc_earn.
Print Assumptions cg_sc_incE2.
Print Assumptions cg_sc_decC1.
Print Assumptions cg_sc_decC2.
Print Assumptions cg_sc_decC3.
Print Assumptions cg_sc_erT2.
Print Assumptions cg_sc_pl.
Print Assumptions cg_sc_pay.
Print Assumptions cg_sc_jmp3.
Print Assumptions cg_sc_halt.
Print Assumptions cg_k_gt.
Print Assumptions cg_rf_high.
Print Assumptions cg_rf_spare.
Print Assumptions cg_eqv_zero_high.
Print Assumptions cg_eqv_spare.
Print Assumptions cg_in1.
Print Assumptions cg_in2.
Print Assumptions cg_x_block.
Print Assumptions cg_x_block_p.
Print Assumptions cg_x_one.
Print Assumptions cg_x_dec0.
Print Assumptions cg_x_decS.
Print Assumptions cg_x_inc.
Print Assumptions cg_x_pay.
Print Assumptions cg_x_earn.
Print Assumptions cg_x_dec_next.
Print Assumptions cg_x_erase.
Print Assumptions cg_x_transfert.
Print Assumptions cg_x_payloop.
Print Assumptions cg_set2_rf.
Print Assumptions cg_x_move.
Print Assumptions cg_x_halt.
Print Assumptions cg_x_read.
Print Assumptions cg_x_noraise.
Print Assumptions cg_x_tail_new.
Print Assumptions cg_x_tail.
Print Assumptions cg_x_check.
Print Assumptions cg_x_to_new.
Print Assumptions cg_e0_rf.
Print Assumptions cg_e0_high.
Print Assumptions cg_x_prologue.
Print Assumptions cg_x_step.
Print Assumptions cg_x_stop.
