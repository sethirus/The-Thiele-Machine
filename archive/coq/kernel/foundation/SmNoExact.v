(** SmNoExact.v: no recursion theorem for full behaviour.

    SmKleene.v gives a program e with the same partial function as F e, and
    SmFixedPoint.v one with the same stopping, register 0, trap latch,
    ledger, flag, fact count and channel emptiness. This file shows that
    nothing stronger holds in general: there is a map F, computed by a host
    program, such that no program e behaves as F e in the sense of
    sm_hequiv, which compares every register as well.

    The map is F p = [INC r], where r is one above the number of p. The
    number of a program is at least the number of every register it names
    [sm2_reg_bound], so a program e cannot name the register r that F e
    writes, and its run leaves that register at 0 while the run of F e
    leaves it at 1.

    The same argument refutes agreement on the content of the facts: a
    program that checks the register r has a fact about r, and e cannot
    name r.

    Dependencies: as SmDecider.v, and SmLoops.v. No axioms and no unfinished proofs. *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is recursion theory on the host machine, here the impossibility of a fixed point of full behaviour on the host machine of EarnedMulti.v.
   The host machine's link to the abstract record (a CertificationSystem
   with the trace floor, a Thiele-complete machine, and the halting problem
   of U) lives in UniversalInterpreterLinks.v. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Undecidability.L Require Import Tactics.LTactics Datatypes.LNat Datatypes.LOptions
  Datatypes.LProd Datatypes.Lists Datatypes.LBool.
From Undecidability.MinskyMachines Require Import MM MMA.
From Undecidability.MinskyMachines.Reductions Require Import L_computable_to_MMA_computable.
Require Minimal.EarnedMulti Minimal.UniversalCodes.
Require Import Minimal.SmHostBlocks Minimal.SmCodes Minimal.SmInterp Kernel.SmEvalL Kernel.SmFuel Kernel.SmMMAHost
  Kernel.SmKleene Minimal.SmLoops.
Module M := Minimal.EarnedMulti.
Module UC := Minimal.UniversalCodes.
Unset Implicit Arguments.

Local Notation hinstr := (@M.instr UC.hprop).
Local Notation hstate := (@M.state UC.hprop).
Local Notation hrun_prog := (M.run_prog UC.hprop_eqb UC.heval).
Local Notation hfun := (sm_hfun UC.hprop_eqb UC.heval).
Local Notation hequiv := (sm_hequiv UC.hprop_eqb UC.heval).
Local Notation hstart := (@sm_hstart UC.hprop).

(* ================================================================= *)
(* A program's number is above every register it names.               *)
(* ================================================================= *)

Lemma sm2_lt_pow2 : forall m, m < 2 ^ m.
Proof.
  induction m as [| m IH]; [simpl; lia |].
  rewrite Nat.pow_succ_r'. lia.
Qed.

Lemma sm2_pair_ge_l : forall m n, m <= UC.pair m n.
Proof.
  intros m n. unfold UC.pair. pose proof (sm2_lt_pow2 m). nia.
Qed.

Lemma sm2_kcode_reg : forall (i : hinstr) r, M.mentions i r = true -> r <= sm_kcode (sm_to_ki i).
Proof.
  intros i r H. destruct i as [d | d j | | p d | p d |]; simpl in H; try discriminate;
    apply Nat.eqb_eq in H; subst d; simpl.
  - pose proof (sm_pair_ge 0 r). lia.
  - pose proof (sm_pair_ge 1 (UC.pair r j)). pose proof (sm_pair_ge r j).
    pose proof (sm2_pair_ge_l r j). lia.
  - pose proof (sm_pair_ge 3 r). lia.
  - pose proof (sm_pair_ge 4 r). lia.
Qed.

Lemma sm2_hcode_cons : forall (i : hinstr) P,
  sm_hcode (i :: P) = UC.pair (sm_kcode (sm_to_ki i)) (sm_hcode P).
Proof. intros i P. unfold sm_hcode, sm_kpcode. simpl. reflexivity. Qed.

Theorem sm2_reg_bound : forall (P : list hinstr) i r,
  In i P -> M.mentions i r = true -> r <= sm_hcode P.
Proof.
  induction P as [| j P IH]; intros i r Hin Hm; [destruct Hin |].
  rewrite sm2_hcode_cons. destruct Hin as [-> | Hin].
  - pose proof (sm2_kcode_reg i r Hm). pose proof (sm2_pair_ge_l (sm_kcode (sm_to_ki i)) (sm_hcode P)).
    lia.
  - pose proof (IH i r Hin Hm). pose proof (sm_pair_ge (sm_kcode (sm_to_ki j)) (sm_hcode P)). lia.
Qed.

(* A program that names no register q leaves q alone. *)
Lemma sm2_next_in : forall (P : list hinstr) k i, M.next_instr P k = Some i -> In i P.
Proof.
  intros P k i H. unfold M.next_instr in H. destruct (M.err k); [discriminate |].
  destruct (M.fetch P (M.pc k)) as [j |] eqn:Hf; [| discriminate].
  assert (Hj : j = i).
  { destruct j; simpl in H; first [discriminate H | (injection H as H'; exact H')]. }
  subst j. destruct (M.pc k) as [| p]; [discriminate Hf |]. simpl in Hf. eapply nth_error_In. exact Hf.
Qed.

Lemma sm2_trace_in : forall n (P : list hinstr) s i, In i (M.trace_of UC.hprop_eqb UC.heval n P s) -> In i P.
Proof.
  induction n as [| n IH]; intros P s i H; [destruct H |].
  simpl in H. destruct (M.next_instr P (M.core_of s)) as [j |] eqn:Hn; [| destruct H].
  destruct H as [<- | H]; [eapply sm2_next_in; exact Hn | eapply IH; exact H].
Qed.

Theorem sm2_prog_frame : forall (P : list hinstr) q,
  (forall i, In i P -> M.mentions i q = false) ->
  forall n s, M.vals (M.core_of (hrun_prog n P s)) q = M.vals (M.core_of s) q.
Proof.
  intros P q H n s. rewrite (M.multi_run_prog_trace UC.hprop_eqb UC.heval).
  destruct (M.multi_frame_run UC.hprop_eqb UC.heval (M.trace_of UC.hprop_eqb UC.heval n P s) s q)
    as [Hv _]; [| exact Hv].
  intros i Hi. apply H. eapply sm2_trace_in. exact Hi.
Qed.

(* ================================================================= *)
(* The map F p = [INC (number of p + 1)] is computed by a host program. *)
(* ================================================================= *)

Definition sm2_impf (w fuel x c : nat) : option nat :=
  Some (UC.pair (UC.pair 0 (S x)) 0).

Instance term_sm2_impf : computable sm2_impf. Proof. extract. Qed.

Definition sm2_Rimp (v : Vector.t nat 2) (m : nat) : Prop :=
  exists n, sm2_impf 0 n (Vector.hd v) (Vector.hd (Vector.tl v)) = Some m.

Lemma sm2_imp_MMA : MMA_computable sm2_Rimp.
Proof.
  apply L_computable_to_MMA_computable.
  exact (@sm_L_computable_fuel2 nat _ sm2_impf _ 0 (fun n n' x c m H Hle => H)).
Qed.

Lemma sm2_imp_program : exists T : list hinstr,
  forall x m, hfun T x m <-> m = UC.pair (UC.pair 0 (S x)) 0.
Proof.
  destruct sm2_imp_MMA as [nn [Pm HPm]].
  exists (sm_mma_host (S (S (S nn))) Pm). intros x m.
  transitivity (sm2_Rimp (Vector.cons nat x 1 (Vector.cons nat 0 0 (Vector.nil nat))) m).
  2: { unfold sm2_Rimp. simpl. split.
       - intros [n H]. injection H as <-. reflexivity.
       - intros ->. exists 0. reflexivity. }
  symmetry.
  rewrite (sm_mma_two nn Pm sm2_Rimp HPm (M.core_of (sm_hstart x)) x 0 m eq_refl eq_refl).
  - unfold sm_hfun, sm_hends. split.
    + intros [n [Hh Hv]]. exists (hrun_prog n (sm_mma_host (S (S (S nn))) Pm) (sm_hstart x)).
      split.
      * exists n. split; [reflexivity |]. rewrite sm_core_run. exact Hh.
      * rewrite sm_core_run. exact Hv.
    + intros [s [[n [-> Hh]] Hv]]. exists n. rewrite sm_core_run in Hh, Hv. split; assumption.
  - intro r. cbn [M.vals M.core_of sm_hstart M.start M.start_core]. unfold sm_hin, sm_in2.
    destruct (Nat.eqb r 1); [reflexivity |]. destruct (Nat.eqb r 2); reflexivity.
Qed.

(* The map. *)
Definition sm2_imp_map (p : list hinstr) : list hinstr := [M.INC (S (sm_hcode p))].

Lemma sm2_imp_code : forall p, sm_hcode (sm2_imp_map p) = UC.pair (UC.pair 0 (S (sm_hcode p))) 0.
Proof. intro p. reflexivity. Qed.

(* ================================================================= *)
(* The theorem.                                                       *)
(* ================================================================= *)

Theorem sm2_no_exact :
  exists (F : list hinstr -> list hinstr) (T : list hinstr),
    sm_computes_map T F /\ forall e, ~ hequiv e (F e).
Proof.
  destruct sm2_imp_program as [T HT].
  exists sm2_imp_map, T. split.
  - intro p. apply HT. symmetry. apply sm2_imp_code.
  - intros e Heq.
    set (rho := S (sm_hcode e)).
    (* F e on 0: stops with 1 in register rho *)
    assert (Hs : exists s, sm_hends UC.hprop_eqb UC.heval (sm2_imp_map e) 0 s /\
                           M.vals (M.core_of s) rho = 1).
    { set (s0 := hstart 0).
      assert (He0 : M.err (M.core_of s0) = false) by reflexivity.
      assert (Hf0 : M.fetch (sm2_imp_map e) (M.pc (M.core_of s0)) = Some (M.INC rho)) by reflexivity.
      destruct (sm2_step_inc (sm2_imp_map e) s0 rho He0 Hf0) as (N1 & P1 & V1 & W1 & E1).
      exists (M.step UC.hprop_eqb UC.heval (sm2_imp_map e) s0). split.
      - exists 1. split; [reflexivity |].
        unfold M.halted, M.next_instr. destruct E1 as (_ & _ & C & _). rewrite <- C. rewrite He0.
        rewrite P1. reflexivity.
      - rewrite V1, Nat.eqb_refl. subst s0. cbn [M.vals M.core_of hstart sm_hstart M.start M.start_core].
        unfold sm_hin. destruct (Nat.eqb rho 1); reflexivity. }
    destruct Hs as (s & Hs & Hv).
    destruct (proj2 (Heq 0) s Hs) as (t & Ht & Hagree).
    destruct Hagree as (Hvals & _).
    destruct Ht as [n [-> Hh]].
    pose proof (sm2_prog_frame e rho ltac:(
      intros i Hi; destruct (M.mentions i rho) eqn:Hm; [| reflexivity];
      exfalso; pose proof (sm2_reg_bound e i rho Hi Hm); unfold rho in *; lia) n (hstart 0)) as Hfr.
    specialize (Hvals rho). rewrite Hv in Hvals. rewrite Hfr in Hvals.
    symmetry in Hvals.
    cbn [M.vals M.core_of sm_hstart M.start M.start_core] in Hvals. unfold sm_hin in Hvals.
    destruct (Nat.eqb rho 1); discriminate Hvals.
Qed.

Print Assumptions sm2_no_exact.
Print Assumptions sm2_reg_bound.
