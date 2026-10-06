(** TcNoFine.v: Kleene's recursion theorem fails for the finer sameness.

    TcPacked.v proves the recursion theorem for programs that compute the
    same packed function. Here the finer sameness of TcRice.v (the same
    stopping, counters, trap latch, ledger, flag, and the same SHAPES of the
    fact table and channel, [tc_equiv]) is shown to have no recursion
    theorem, even on packed inputs and for a transformation that a program of
    the machine carries out.

    The transformation. F(p) is the one-line program

        CHECK (PGe (n + 1)) A,   n the number of p.

    Started on any input at least n + 1 it records a fact whose property is
    PGe (n + 1) and stops. A program e can only record facts with the
    properties of its own CHECK instructions, and every such property is
    PGe m, PZero or PEven with m below the number of e (the number of an
    instruction exceeds its operands, and the number of a program exceeds
    its instructions' numbers). So no e can record the property
    PGe (number of e + 1): the shapes differ on every large input
    [tc_no_fine_fixed_point], and a program T carries F out
    [tc_no_fine_kleene].

    The same argument works for COMMIT and the channel; and it shows what
    the earlier host-machine record theorem relied on: with a single
    property the table can only hold one shape.

    Dependencies: TcRice.v, TcPacked.v, TcCodes.v, TcFuel.v, TcEvalL.v and
    the MetaCoq extraction tactic. No axioms and no unfinished proofs.                  *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is recursion theory on the two-counter machine of EarnedCore.v (its
   programs, runs and the numbering of programs). The machine's link to the
   abstract record (a CertificationSystem with the trace cost floor, and a
   Thiele-complete machine) lives in EarnedCoreLinks.v and ThieleComplete.v. *)


From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Undecidability.L Require Import Tactics.LTactics Datatypes.LNat Datatypes.LOptions
  Datatypes.LProd Datatypes.Lists Datatypes.LBool.
From Undecidability.MinskyMachines Require Import MMA.
From Undecidability.MinskyMachines.Reductions Require Import L_computable_to_MMA_computable.
Require Minimal.UniversalCodes.
Require Import Minimal.TcBlocks Kernel.TcRice Kernel.TcCodes Kernel.TcInterp Kernel.TcEvalL Kernel.TcFuel Kernel.TcPacked.
Module E := Minimal.EarnedCore.
Module UC := Minimal.UniversalCodes.
Set Default Goal Selector "!".

(* ------------------------------------------------------------------ *)
(* A program only records facts with the properties it contains        *)
(* ------------------------------------------------------------------ *)

Definition tc_inv (e : list E.instr) (s : E.state) : Prop :=
  forall f, In f (E.facts (E.core_of s)) -> exists c, In (E.CHECK (E.f_prop f) c) e.

Lemma tc_inv_step : forall e s, tc_inv e s -> tc_inv e (E.step e s).
Proof.
  intros e s Hi f Hf. unfold E.step in Hf |- *.
  destruct (E.next_instr e (E.core_of s)) as [i |] eqn:Hn; [| apply Hi; exact Hf].
  destruct (tc_gnext_some e _ _ Hn) as (He & Hfetch & _).
  assert (Hin : In i e).
  { destruct (E.pc (E.core_of s)) as [| q]; [discriminate |]. simpl in Hfetch. eapply nth_error_In. exact Hfetch. }
  unfold E.exec in Hf. simpl in Hf. unfold E.cexec in Hf. rewrite He in Hf.
  destruct i as [c | c j | | p c | p c |].
  - destruct c; simpl in Hf; apply Hi; unfold E.write in Hf; simpl in Hf; exact Hf.
  - destruct c; simpl in Hf;
      [destruct (E.ca (E.core_of s)) | destruct (E.cb (E.core_of s))]; unfold E.goto, E.write in Hf;
      simpl in Hf; apply Hi; exact Hf.
  - apply Hi. exact Hf.
  - destruct (E.check_ok (E.core_of s) p c).
    + unfold E.record_fact in Hf. simpl in Hf. destruct Hf as [<- | Hf].
      * exists c. unfold E.claim. simpl. exact Hin.
      * apply Hi. exact Hf.
    + unfold E.trap in Hf. simpl in Hf. apply Hi. exact Hf.
  - destruct (E.commit_ok (E.core_of s) p c).
    + unfold E.commit_to in Hf. simpl in Hf. apply Hi. exact Hf.
    + unfold E.trap in Hf. simpl in Hf. apply Hi. exact Hf.
  - destruct (E.certify_ok (E.core_of s)).
    + unfold E.goto in Hf. simpl in Hf. apply Hi. exact Hf.
    + unfold E.trap in Hf. simpl in Hf. apply Hi. exact Hf.
Qed.

Lemma tc_inv_run : forall n e s, tc_inv e s -> tc_inv e (E.run_prog n e s).
Proof.
  induction n as [| n IH]; intros e s H; [exact H |].
  simpl. apply IH, tc_inv_step, H.
Qed.

Lemma tc_inv_start : forall e a, tc_inv e (E.start a 0).
Proof. intros e a f Hf. simpl in Hf. contradiction. Qed.

(* ------------------------------------------------------------------ *)
(* The number of a program exceeds the operands of its instructions   *)
(* ------------------------------------------------------------------ *)

Lemma tc_pair_gt : forall m n, n < UC.pair m n.
Proof. intros m n. pose proof (tc_pair_ge m n). lia. Qed.

Lemma tc_pair_gt_l : forall m n, m < UC.pair m n.
Proof.
  intros m n. unfold UC.pair. pose proof (tc_lt_pow2 m). nia.
Qed.

Lemma tc_lencode_gt : forall l x, In x l -> x < tc_lencode l.
Proof.
  induction l as [| y t IH]; intros x Hx; [contradiction |].
  simpl. destruct Hx as [<- | Hx].
  - apply tc_pair_gt_l.
  - pose proof (IH x Hx). pose proof (tc_pair_gt y (tc_lencode t)). lia.
Qed.

Lemma tc_check_operand : forall e m c, In (E.CHECK (E.PGe m) c) e -> m < tc_pcode e.
Proof.
  intros e m c Hin.
  assert (Hk : In (tc_kcode (tc_toki (E.CHECK (E.PGe m) c))) (map tc_kcode (map tc_toki e))).
  { rewrite map_map. apply in_map_iff. exists (E.CHECK (E.PGe m) c). split; [reflexivity | exact Hin]. }
  apply tc_lencode_gt in Hk. unfold tc_pcode, tc_kpcode.
  eapply Nat.lt_trans; [| exact Hk].
  simpl. unfold UC.pcode.
  pose proof (tc_pair_gt (UC.ccode c) (m + 2)) as H1.
  pose proof (tc_pair_gt 3 (UC.pair (UC.ccode c) (m + 2))) as H2. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The transformation and its fixed point that cannot exist            *)
(* ------------------------------------------------------------------ *)

Definition tc_fprog (p : list E.instr) : list E.instr :=
  [E.CHECK (E.PGe (tc_pcode p + 1)) E.CA].

Lemma tc_fprog_records : forall p n, tc_pcode p + 1 <= n ->
  exists s, tc_ends n (tc_fprog p) s /\
            map tc_shape (E.facts (E.core_of s)) = [(E.PGe (tc_pcode p + 1), E.CA)].
Proof.
  intros p n Hn.
  assert (Hs1 : E.step (tc_fprog p) (E.start n 0) =
                E.exec (E.start n 0) (E.CHECK (E.PGe (tc_pcode p + 1)) E.CA)).
  { unfold E.step. assert (Hnx : E.next_instr (tc_fprog p) (E.core_of (E.start n 0)) =
                              Some (E.CHECK (E.PGe (tc_pcode p + 1)) E.CA)) by reflexivity.
    rewrite Hnx. reflexivity. }
  assert (Hr : E.run_prog 1 (tc_fprog p) (E.start n 0) =
               E.exec (E.start n 0) (E.CHECK (E.PGe (tc_pcode p + 1)) E.CA)).
  { change (E.run_prog 1 (tc_fprog p) (E.start n 0)) with (E.step (tc_fprog p) (E.start n 0)). exact Hs1. }
  assert (Hl : Nat.leb (tc_pcode p + 1) n = true) by (apply Nat.leb_le; exact Hn).
  exists (E.run_prog 1 (tc_fprog p) (E.start n 0)). split.
  - exists 1. split; [reflexivity |]. rewrite Hr.
    unfold E.halted, E.next_instr, E.exec. simpl. unfold E.cexec. simpl.
    unfold E.check_ok. simpl. rewrite Hl. simpl. reflexivity.
  - rewrite Hr. unfold E.exec. simpl. unfold E.cexec. simpl. unfold E.check_ok. simpl.
    rewrite Hl. simpl. reflexivity.
Qed.

Theorem tc_no_fine_fixed_point : forall e, ~ tc_equiv tc_packed e (tc_fprog e).
Proof.
  intros e Heq.
  set (K := tc_pcode e + 1).
  assert (HK : K <= 2 ^ K) by (pose proof (tc_lt_pow2 K); lia).
  destruct (Heq (2 ^ K) (ex_intro _ K eq_refl)) as [_ H2].
  destruct (tc_fprog_records HK) as [s [Hs Hshape]].
  destruct (H2 s Hs) as [t [[N [-> HN]] Hag]].
  destruct Hag as (_ & _ & _ & _ & _ & Hsh & _).
  rewrite Hshape in Hsh.
  set (st := E.run_prog N e (E.start (2 ^ K) 0)) in *.
  destruct (E.facts (E.core_of st)) as [| f rest] eqn:Hf; [discriminate |].
  simpl in Hsh. injection Hsh as Hp _.
  assert (Hin : In f (E.facts (E.core_of st))) by (rewrite Hf; left; reflexivity).
  assert (Hs0 : tc_inv e (E.start (2 ^ K) 0)) by (intros f0 Hf0; simpl in Hf0; contradiction).
  destruct (@tc_inv_run N e (E.start (2 ^ K) 0) Hs0 f Hin) as [c Hc].
  rewrite Hp in Hc. apply tc_check_operand in Hc. unfold K in Hc. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* A program of the machine carries the transformation out            *)
(* ------------------------------------------------------------------ *)

Definition tc_chkf (d fuel x c : nat) : option nat :=
  Some (UC.pair (UC.pair 3 (UC.pair 0 (x + 1 + 2))) 0).

Instance term_tc_chkf : computable tc_chkf. Proof. extract. Qed.

Lemma tc_chkf_mono : forall n n' x c m, tc_chkf 0 n x c = Some m -> n <= n' -> tc_chkf 0 n' x c = Some m.
Proof. intros n n' x c m H _. exact H. Qed.

Definition tc_Rchk (v : Vector.t nat 2) (m : nat) : Prop :=
  exists n, tc_chkf 0 n (Vector.hd v) (Vector.hd (Vector.tl v)) = Some m.

Theorem tc_chk_MMA : MMA_computable tc_Rchk.
Proof.
  apply L_computable_to_MMA_computable.
  exact (@tc_L_computable_fuel2 nat _ tc_chkf _ 0 tc_chkf_mono).
Qed.

Lemma tc_pcode_fprog : forall p, tc_pcode (tc_fprog p) = UC.pair (UC.pair 3 (UC.pair 0 (tc_pcode p + 1 + 2))) 0.
Proof. intro p. reflexivity. Qed.

Theorem tc_no_fine_kleene :
  exists (F : list E.instr -> list E.instr) (T : list E.instr),
    tc_computes_map T F /\ forall e, ~ tc_equiv tc_packed e (F e).
Proof.
  destruct (tc_MMA_to_packed tc_chk_MMA) as [U HU].
  exists tc_fprog, U. split.
  - intro p.
    assert (H2 : tc_pk2 U (tc_pcode p) 0 (tc_pcode (tc_fprog p))).
    { apply HU. unfold tc_Rchk. simpl. exists 0. unfold tc_chkf. rewrite tc_pcode_fprog. reflexivity. }
    unfold tc_pk, tc_pk2 in *. rewrite Nat.pow_0_r, Nat.mul_1_r in H2. exact H2.
  - exact tc_no_fine_fixed_point.
Qed.

Print Assumptions tc_no_fine_fixed_point.
Print Assumptions tc_no_fine_kleene.
