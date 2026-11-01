(** CmpFinal.v: the verified compiler, end to end, with the runner that is
    extracted.

    CmpPipeline.v proves that a source program computes y from xs if and
    only if its host program (run by the host machine of EarnedMulti.v), its
    guest program (run by the two-counter machine) and the universal machine
    U_P loaded with the guest, each reach the matching halted state with the
    answer y. CmpRun.v proves the fast runner that the OCaml extraction uses
    against the register semantics of the host program. This file puts the
    runner in the same chain:

      cmp_exec_iff   for a well-formed source program p, p computes y from xs
                     if and only if the runner, given enough fuel, halts with
                     register out + 1 equal to y
      cmp_final      the runner statement together with the four statements
                     of cmp_pipeline

    The runner statement is about the extracted code: cmp_exec is the
    function that ocaml/CmpExtract.v extracts and the OCaml driver calls.

    Dependencies: CmpPipeline.v and CmpRun.v. No axioms and no unfinished proofs.      *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   composes the stages of the verified compiler pipeline of CmpPipeline.v
   with the runner of CmpRun.v. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Undecidability.Shared.Libs.DLW Require Import utils pos vec subcode sss.
From Undecidability.MinskyMachines Require Import MM MMA.
From Undecidability.MinskyMachines.MMenv Require Import env mme_defs.
Require Minimal.EarnedMulti.
From Undecidability.FRACTRAN.Util Require Import prime_seq.
Require Import Kernel.CompilerCodes Kernel.CompilerChecker Kernel.CompilerLifts Kernel.CompilerIcomp.
Require Import Kernel.UniversalPCodes Kernel.UniversalPBridge Kernel.UniversalPBlocks Kernel.UniversalPLayout
  Kernel.UniversalPPhases Kernel.UniversalPSim Kernel.UniversalPRun.
Require Import Kernel.CmpLang Kernel.CmpBlocks Kernel.CmpInline Kernel.CmpFlat Kernel.CmpExpr Kernel.CmpMM
  Kernel.CmpCompile Kernel.CmpHost Kernel.CmpGuest Kernel.CmpPipeline Kernel.CmpRun.

Theorem cmp_exec_iff : forall p nin out, cmp_wf p -> forall xs y,
  cmp_src_computes p xs out y <->
  exists fuel, cr_halted (cmp_exec p nin out xs fuel) = true /\ cmp_answer out (cmp_exec p nin out xs fuel) = y.
Proof.
  intros p nin out Hwf xs y. split.
  - intros (e1 & c & Hd & Hy).
    destruct (cmp_exec_complete p nin out Hwf xs e1 c Hd) as (k & Hk).
    destruct (Hk k (Nat.le_refl k)) as (H1 & _ & H3).
    exists k. split; [exact H1 |]. unfold cmp_answer. rewrite (H3 out (cmp_out_lt_nv0 p nin out)). exact Hy.
  - intros (fuel & Hh & Hy).
    destruct (cmp_exec_sound p nin out Hwf xs fuel Hh) as (e1 & c & Hd & Hv).
    exists e1, c. split; [exact Hd |].
    rewrite <- Hy. unfold cmp_answer. symmetry. apply Hv. apply cmp_out_lt_nv0.
Qed.

Theorem cmp_final : forall (prop : Type) (prop_eqb : prop -> prop -> bool) (eval : prop -> nat -> bool)
  p nin out, cmp_wf p -> forall xs y,
  (cmp_src_computes p xs out y <->
   exists fuel, cr_halted (cmp_exec p nin out xs fuel) = true /\ cmp_answer out (cmp_exec p nin out xs fuel) = y) /\
  (cmp_src_computes p xs out y <->
   exists n v2, @cmp_host_final prop (cmp_mm_prog p nin out) v2
                  (@cmp_host_at prop prop_eqb eval (cmp_mm_prog p nin out) (cmp_mm_load (cmp_nvF p nin out) xs) n) /\
                v2 (S out) = y) /\
  (cmp_src_computes p xs out y <->
   exists n, Minimal.EarnedPriced.pr_halted (cmp_guest p nin out) (Minimal.EarnedGeneric.core_of (cmp_guest_at p nin out xs n)) /\
             cmp_guest_answer out (cmp_guest_at p nin out xs n) = y) /\
  (cmp_src_computes p xs out y <->
   exists t, M.pu_halted U_P (M.core_of (cmp_U_at p nin out xs t)) /\
             cg_expo (qs (S out)) (hv (cmp_U_at p nin out xs t) pu_RB) = y /\
             hv (cmp_U_at p nin out xs t) pu_RA = 0 /\
             M.mu (cmp_U_at p nin out xs t) = 0 /\ M.cert (cmp_U_at p nin out xs t) = false).
Proof.
  intros prop prop_eqb eval p nin out Hwf xs y.
  destruct (cmp_pipeline prop prop_eqb eval p nin out Hwf xs y) as (H1 & H2 & H3).
  refine (conj (cmp_exec_iff p nin out Hwf xs y) _).
  exact (cmp_pipeline prop prop_eqb eval p nin out Hwf xs y).
Qed.

Print Assumptions cmp_exec_iff.
Print Assumptions cmp_final.
