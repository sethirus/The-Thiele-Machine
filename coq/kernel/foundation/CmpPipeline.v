(** CmpPipeline.v: the verified compiler, end to end.

    A source program p (CmpLang.v) that takes nin inputs in its variables
    0 .. nin - 1 and answers in variable out is compiled, by functions
    written in Coq, in stages. Each stage has a correctness theorem about
    halting and answers, and this file composes them.

      source program (CmpLang.v)
        -- call unfolding, CmpInline.v      cmp_inl_fwd, cmp_inl_bwd
        -- flat program, CmpFlat.v          cmp_fc_fwd, cmp_fc_bwd
        -- counter machine program, CmpMM.v cmp_mm_output, cmp_mm_output_conv
        == cmp_mm_prog p nin out            cmp_stageA (CmpCompile.v)
        -- host program, CmpHost.v          cmp_host_fwd, cmp_host_bwd
        -- guest program, CmpGuest.v        cmp_guest_fwd, cmp_guest_bwd
        -- universal machine, UniversalPRun.v

    The counter machine program Q = cmp_mm_prog p nin out is placed at
    address 1 and keeps the inputs in registers 1, 2, ... and the variable
    out in register out + 1. The host program is a program of the
    multi-register machine of EarnedMulti.v (over any property language),
    started with the same registers. The guest program is a program of the
    two-counter machine of EarnedPriced.v, started with counter A at 0 and
    counter B at the Godel code of the registers (cmp_gk is the number of
    registers it codes). U_P is the one fixed host program of
    UniversalPRun.v, loaded with the guest program.

      cmp_pipeline_host   the source program computes y from xs if and only
                          if the host program, run by EarnedMulti.v from
                          registers holding xs, reaches a halted state with
                          register out + 1 equal to y; at that state the
                          registers are those of the final source variables,
                          the facts, channel, trap latch, ledger and flag
                          are as at the start
      cmp_pipeline_guest  the same for the guest program: the source program
                          computes y if and only if the guest halts with its
                          second counter the code of registers whose
                          register out + 1 is y (then the exponent of the
                          prime of register out + 1 in counter B is y)
      cmp_pipeline_U      the same for U_P: the source program computes y
                          if and only if U_P, loaded with the guest, halts
                          with register RB holding such a code, register
                          RA zero, ledger 0 and flag down
      cmp_pipeline        the four statements together

    What is not claimed: the number of steps. The theorems say that the
    machines halt together and agree on the answer; they say nothing about
    how long a run takes, which is measured by the tests (compiled
    programs are slow: a copy or a comparison of numbers costs a loop whose
    length is the value).

    Dependencies: Coq standard library, the vendored coq-undecidability
    library, the Cmp files, the Compiler*.v files and UniversalPRun.v. No
    axioms and no unfinished proofs.                                                    *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this
   file composes the stages of the verified compiler. Its link to the
   abstract record (the host as a CertificationSystem and the universal
   machine meeting thiele_complete) lives in UniversalPRun.v and
   PricedHostLinks.v. *)

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
  Kernel.CmpCompile Kernel.CmpHost Kernel.CmpGuest.

Local Notation mmstep := (@mm_sss_env nat eq_nat_dec).

(* The registers of the counter machine program, and how many the guest codes. *)
Definition cmp_prog_regs (Q : list (mm_instr nat)) : nat := fold_right Nat.max 0 (map cg_xreg Q).

Lemma cmp_prog_regs_lt : forall Q J, In J Q -> cg_xreg J < S (cmp_prog_regs Q).
Proof.
  induction Q as [| J0 Q IH]; intros J H; [destruct H |].
  unfold cmp_prog_regs in *. simpl. destruct H as [<- | H]; [lia | pose proof (IH J H); lia].
Qed.

Definition cmp_gk (p : cmp_prog) (nin out : nat) : nat :=
  Nat.max (S (cmp_prog_regs (cmp_mm_prog p nin out))) (S (cmp_nvF p nin out)).

Lemma cmp_gk_wf : forall p nin out J, In J (cmp_mm_prog p nin out) -> cg_xreg J < cmp_gk p nin out.
Proof.
  intros p nin out J H. unfold cmp_gk. pose proof (cmp_prog_regs_lt _ _ H). lia.
Qed.

Lemma cmp_load_zero : forall p nin out xs x, cmp_gk p nin out <= x ->
  cmp_mm_load (cmp_nvF p nin out) xs x = 0.
Proof.
  intros p nin out xs x H. unfold cmp_gk in H. unfold cmp_mm_load.
  destruct x as [| x']; [reflexivity |].
  destruct (Nat.ltb_spec x' (cmp_nvF p nin out)); [lia | reflexivity].
Qed.

Definition cmp_guest (p : cmp_prog) (nin out : nat) : list (@Minimal.EarnedPriced.pr_instr cg_uprop) :=
  cmp_gprog (cmp_gk p nin out) (cmp_mm_prog p nin out).

Definition cmp_host (prop : Type) (p : cmp_prog) (nin out : nat) : list (@Minimal.EarnedMulti.instr prop) :=
  cmp_hprog (cmp_host_prog (cmp_mm_prog p nin out)).

(* ================================================================= *)
(* The host.                                                          *)
(* ================================================================= *)

Theorem cmp_pipeline_host : forall (prop : Type) (prop_eqb : prop -> prop -> bool) (eval : prop -> nat -> bool)
  p nin out, cmp_wf p -> forall xs y,
  cmp_src_computes p xs out y <->
  exists n v2, @cmp_host_final prop (cmp_mm_prog p nin out) v2
                 (@cmp_host_at prop prop_eqb eval (cmp_mm_prog p nin out) (cmp_mm_load (cmp_nvF p nin out) xs) n) /\
               v2 (S out) = y.
Proof.
  intros prop prop_eqb eval p nin out Hwf xs y. split.
  - intros Hc. destruct ((proj1 (cmp_stageA p nin out Hwf xs y)) Hc) as (j & w2 & Ho & Hy).
    destruct (@cmp_host_fwd prop prop_eqb eval (cmp_mm_prog p nin out) (cmp_mm_load (cmp_nvF p nin out) xs) j w2
                (cmp_mm_load (cmp_nvF p nin out) xs) (fun r => eq_refl) Ho) as (n & Hf).
    exists n, w2. split; assumption.
  - intros (n & v2 & Hf & Hy).
    destruct (@cmp_host_bwd prop prop_eqb eval (cmp_mm_prog p nin out) (cmp_mm_load (cmp_nvF p nin out) xs)
                (cmp_mm_load (cmp_nvF p nin out) xs) n (fun r => eq_refl) (proj1 Hf))
      as (j & v2' & Ho & Hf').
    apply (proj2 (cmp_stageA p nin out Hwf xs y)). exists j, v2'. split; [exact Ho |].
    rewrite <- Hy. destruct Hf as (_ & _ & C & _). destruct Hf' as (_ & _ & C' & _).
    rewrite <- (C (S out)), <- (C' (S out)). reflexivity.
Qed.


(* ================================================================= *)
(* The guest.                                                         *)
(* ================================================================= *)

(* The state of the guest after n steps from the start with the load of xs. *)
Definition cmp_guest_at (p : cmp_prog) (nin out : nat) (xs : list nat) (n : nat) : cg_ystate :=
  Minimal.EarnedPriced.pr_run_prog cg_uprop_eqb cg_ueval n (cmp_guest p nin out)
    (cmp_gstart (cmp_gk p nin out) (cmp_mm_load (cmp_nvF p nin out) xs)).

(* The answer a guest state holds: the exponent of the prime of register
   out + 1 in counter B. *)
Definition cmp_guest_answer (out : nat) (s : cg_ystate) : nat :=
  cg_expo (qs (S out)) (Minimal.EarnedGeneric.cb (Minimal.EarnedGeneric.core_of s)).

Lemma cmp_guest_at_eq : forall p nin out xs n,
  cmp_guest_at p nin out xs n =
  Minimal.EarnedPriced.pr_run_prog cg_uprop_eqb cg_ueval n (cmp_gprog (cmp_gk p nin out) (cmp_mm_prog p nin out))
    (cmp_gstart (cmp_gk p nin out) (cmp_mm_load (cmp_nvF p nin out) xs)).
Proof. reflexivity. Qed.

Lemma cmp_out_lt_gk : forall p nin out, S out < cmp_gk p nin out.
Proof.
  intros p nin out. unfold cmp_gk, cmp_nvF, cmp_nv0. pose proof (Nat.le_max_r (cmp_svmax (cp_main p)) (Nat.max nin (S out))).
  pose proof (Nat.le_max_r nin (S out)). lia.
Qed.

Lemma cmp_out_lt_nv0 : forall p nin out, out < cmp_nv0 p nin out.
Proof.
  intros p nin out. unfold cmp_nv0. pose proof (Nat.le_max_r nin (S out)).
  pose proof (Nat.le_max_r (cmp_svmax (cp_main p)) (Nat.max nin (S out))). lia.
Qed.

Theorem cmp_pipeline_guest : forall p nin out, cmp_wf p -> forall xs y,
  cmp_src_computes p xs out y <->
  exists n, Minimal.EarnedPriced.pr_halted (cmp_guest p nin out) (Minimal.EarnedGeneric.core_of (cmp_guest_at p nin out xs n)) /\
            cmp_guest_answer out (cmp_guest_at p nin out xs n) = y.
Proof.
  intros p nin out Hwf xs y. split.
  - intros Hc. destruct ((proj1 (cmp_stageA p nin out Hwf xs y)) Hc) as (j & w2 & Ho & Hy).
    destruct (cmp_guest_fwd (cmp_gk p nin out) (cmp_mm_prog p nin out) (cmp_gk_wf p nin out)
                (cmp_mm_load (cmp_nvF p nin out) xs) (cmp_load_zero p nin out xs) j w2 Ho) as (n & Hf).
    exists n. destruct Hf as (A & B & C & D & E).
    split; [exact A |]. unfold cmp_guest_answer. rewrite (cmp_guest_at_eq p nin out xs n). rewrite D.
    rewrite cg_expo_gk. destruct (Nat.ltb_spec (S out) (cmp_gk p nin out)) as [_ | Hn];
      [exact Hy | pose proof (cmp_out_lt_gk p nin out); lia].
  - intros (n & Hh & Hy).
    destruct (cmp_guest_bwd (cmp_gk p nin out) (cmp_mm_prog p nin out) (cmp_gk_wf p nin out)
                (cmp_mm_load (cmp_nvF p nin out) xs) (cmp_load_zero p nin out xs) n Hh) as (j & e1 & Ho & Hf).
    apply (proj2 (cmp_stageA p nin out Hwf xs y)). exists j, e1. split; [exact Ho |].
    destruct Hf as (A & B & C & D & E). unfold cmp_guest_answer in Hy. rewrite (cmp_guest_at_eq p nin out xs n) in Hy.
    rewrite D in Hy. rewrite cg_expo_gk in Hy. destruct (Nat.ltb_spec (S out) (cmp_gk p nin out)) as [_ | Hn];
      [exact Hy | pose proof (cmp_out_lt_gk p nin out); lia].
Qed.

(* A halted guest has the shape of the end of the run. *)
Theorem cmp_pipeline_guest_final : forall p nin out, cmp_wf p -> forall xs n,
  Minimal.EarnedPriced.pr_halted (cmp_guest p nin out) (Minimal.EarnedGeneric.core_of (cmp_guest_at p nin out xs n)) ->
  exists e1, cmp_guest_final (cmp_gk p nin out) (cmp_mm_prog p nin out) e1 (cmp_guest_at p nin out xs n).
Proof.
  intros p nin out Hwf xs n Hh.
  destruct (cmp_guest_bwd (cmp_gk p nin out) (cmp_mm_prog p nin out) (cmp_gk_wf p nin out)
              (cmp_mm_load (cmp_nvF p nin out) xs) (cmp_load_zero p nin out xs) n Hh) as (j & e1 & _ & Hf).
  exists e1. exact Hf.
Qed.


(* ================================================================= *)
(* The universal machine.                                             *)
(* ================================================================= *)

Module M := Minimal.EarnedMultiPriced.

(* The fixed host program U_P, loaded with the guest program and the
   counters 0 and the code of the load of xs, after t steps. *)
Definition cmp_U_at (p : cmp_prog) (nin out : nat) (xs : list nat) (t : nat) : @M.pu_state pu_hprop :=
  pu_hrun (cmp_guest p nin out) 0
    (cg_gk (cmp_gk p nin out) (cmp_mm_load (cmp_nvF p nin out) xs)) t.

Theorem cmp_pipeline_U : forall p nin out, cmp_wf p -> forall xs y,
  cmp_src_computes p xs out y <->
  exists t, M.pu_halted U_P (M.core_of (cmp_U_at p nin out xs t)) /\
            cg_expo (qs (S out)) (hv (cmp_U_at p nin out xs t) pu_RB) = y /\
            hv (cmp_U_at p nin out xs t) pu_RA = 0 /\
            M.mu (cmp_U_at p nin out xs t) = 0 /\ M.cert (cmp_U_at p nin out xs t) = false.
Proof.
  intros p nin out Hwf xs y. set (b := cg_gk (cmp_gk p nin out) (cmp_mm_load (cmp_nvF p nin out) xs)).
  assert (Hg : forall n, pu_grun (cmp_guest p nin out) 0 b n = cmp_guest_at p nin out xs n) by (intros n; reflexivity).
  split.
  - intros Hc. destruct ((proj1 (cmp_pipeline_guest p nin out Hwf xs y)) Hc) as (n & Hh & Hy).
    destruct (cmp_pipeline_guest_final p nin out Hwf xs n Hh) as (e1 & Hf).
    destruct (proj1 (pu_universal_halting (cmp_guest p nin out) 0 b)) as [t Ht].
    + exists n. rewrite Hg. exact Hh.
    + destruct (pu_universal_output (cmp_guest p nin out) 0 b n t ltac:(rewrite Hg; exact Hh) Ht)
        as (HA & HB & HE & HM & HC).
      exists t. destruct Hf as (_ & _ & C & D & E & F & G0 & H0 & I0).
      repeat split.
      * exact Ht.
      * unfold cmp_U_at; fold b. rewrite HB. rewrite Hg. exact Hy.
      * unfold cmp_U_at; fold b. rewrite HA. rewrite Hg. exact C.
      * unfold cmp_U_at; fold b. rewrite HM. rewrite Hg. exact H0.
      * unfold cmp_U_at; fold b. rewrite HC. rewrite Hg. exact I0.
  - intros (t & Ht & Hy & _).
    destruct (proj2 (pu_universal_halting (cmp_guest p nin out) 0 b)) as [m Hm]; [exists t; exact Ht |].
    destruct (pu_universal_output (cmp_guest p nin out) 0 b m t Hm Ht) as (HA & HB & HE & HM & HC).
    apply (proj2 (cmp_pipeline_guest p nin out Hwf xs y)). exists m. split; [rewrite <- Hg; exact Hm |].
    unfold cmp_guest_answer. rewrite <- Hg. unfold cmp_U_at in Hy. fold b in Hy. rewrite HB in Hy. exact Hy.
Qed.

(* ================================================================= *)
(* The pipeline theorem.                                              *)
(* ================================================================= *)

Theorem cmp_pipeline : forall (prop : Type) (prop_eqb : prop -> prop -> bool) (eval : prop -> nat -> bool)
  p nin out, cmp_wf p -> forall xs y,
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
  intros prop prop_eqb eval p nin out Hwf xs y. split; [| split].
  - apply (cmp_pipeline_host prop prop_eqb eval p nin out Hwf xs y).
  - apply (cmp_pipeline_guest p nin out Hwf xs y).
  - apply (cmp_pipeline_U p nin out Hwf xs y).
Qed.

Print Assumptions cmp_pipeline.
