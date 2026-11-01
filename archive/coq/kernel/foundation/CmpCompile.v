(** CmpCompile.v: the compiler from source programs to counter-machine
    programs, and its correctness theorem.

    cmp_mm_prog p nin out is the program of the vendored counter machine
    obtained from the source program p that takes nin inputs and answers in
    variable out:

      1. cmp_inlined: every procedure call is unfolded (CmpInline.v) in the
         frame of the main program, which has cmp_nv0 variables: the
         variables p mentions, the nin inputs and the answer variable;
      2. cmp_flat: the structured statement becomes a flat program of
         assignments and jumps at address 1 (CmpFlat.v);
      3. cmp_mm_prog: every flat instruction becomes counter machine code
         (CmpMM.v), the whole program again at address 1. Variable x lives
         in register x + 1, register 0 is the zero register of the jumps.

    A run starts at address 1 with the inputs in registers 1, 2, ... (every
    other register 0), cmp_mm_load. It ends when the address is 1 plus the
    length of the program. The theorem:

      cmp_stageA   the source program computes y (a derivation of its main
                   statement from the inputs, ending with variable out
                   equal to y) if and only if the counter machine program
                   has a run from the load of the inputs that leaves the
                   program with register out + 1 equal to y

    In particular the counter machine program halts exactly when the
    source program does (the source has a derivation exactly when its
    program halts: a statement that does not terminate has none), and the
    answer is the same. The theorem also carries every variable of the main
    frame (cmp_stageA_vars): the registers 1 .. nv0 at the end hold the
    variables of the final source state.

    Dependencies: Coq standard library, the vendored coq-undecidability
    library and the Cmp files before this one. No axioms and no unfinished proofs.     *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is one stage of the verified compiler pipeline of CmpPipeline.v and
   imports only the Coq standard library, the vendored coq-undecidability
   library and the Cmp files. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Undecidability.Shared.Libs.DLW Require Import utils pos vec subcode sss.
From Undecidability.Shared.Libs.DLW.Code Require Import compiler compiler_correction.
From Undecidability.MinskyMachines Require Import MM.
From Undecidability.MinskyMachines.MMenv Require Import env mme_defs.
Require Import Kernel.CmpLang Kernel.CmpInline Kernel.CmpFlat Kernel.CmpBlocks Kernel.CmpExpr Kernel.CmpMM.

Local Notation mmstep := (@mm_sss_env nat eq_nat_dec).

Definition cmp_nv0 (p : cmp_prog) (nin out : nat) : nat :=
  Nat.max (cmp_svmax (cp_main p)) (Nat.max nin (S out)).

Definition cmp_inlined (p : cmp_prog) (nin out : nat) : cmp_stmt :=
  cmp_inl (cp_procs p) (length (cp_procs p)) 0 (cmp_nv0 p nin out) (cp_main p).

Definition cmp_nvF (p : cmp_prog) (nin out : nat) : nat :=
  Nat.max (cmp_svmax (cmp_inlined p nin out)) (cmp_nv0 p nin out).

Definition cmp_flat (p : cmp_prog) (nin out : nat) : list cmp_fi := cmp_fc (cmp_inlined p nin out) 1.

Definition cmp_mm_prog (p : cmp_prog) (nin out : nat) : list cmp_mi :=
  cmp_code (cmp_nvF p nin out) (1, cmp_flat p nin out) 1.

(* The inputs in registers 1, 2, ...; everything else 0. *)
Definition cmp_mm_load (nv : nat) (xs : list nat) : nat -> nat :=
  fun r => match r with 0 => 0 | S x => if Nat.ltb x nv then nth x xs 0 else 0 end.

Lemma cmp_mm_load_simul : forall nv xs, cmp_simul nv (cmp_init xs) (cmp_mm_load nv xs).
Proof.
  intros nv xs. unfold cmp_simul, cmp_mm_load, cmp_init, cmp_lget. repeat split.
  - intros r Hr. destruct (Nat.ltb_spec r nv); [reflexivity | lia].
  - intros r Hr. destruct r as [| x]; [lia |]. destruct (Nat.ltb_spec x nv); [lia | reflexivity].
Qed.

Lemma cmp_flat_length : forall p nin out, length (cmp_flat p nin out) = cmp_flen (cmp_inlined p nin out).
Proof. intros. unfold cmp_flat. apply cmp_fc_length. Qed.

Theorem cmp_stageA_fwd : forall p nin out, cmp_wf p -> forall xs e1 c,
  cmp_ceval (cp_procs p) (cmp_init xs) (cp_main p) e1 c ->
  exists w2, (forall x, x < cmp_nv0 p nin out -> w2 (S x) = e1 x) /\
    sss_output mmstep (1, cmp_mm_prog p nin out) (1, cmp_mm_load (cmp_nvF p nin out) xs)
      (1 + length (cmp_mm_prog p nin out), w2).
Proof.
  intros p nin out [Hwp Hws] xs e1 c Hd.
  set (nv0 := cmp_nv0 p nin out). set (nv := cmp_nvF p nin out).
  assert (Hn0 : cmp_svmax (cp_main p) <= nv0) by (unfold nv0, cmp_nv0; lia).
  destruct (cmp_inl_fwd _ _ _ _ _ Hd (length (cp_procs p)) 0 nv0 (cmp_init xs) Hwp Hws Hn0
              ltac:(intros x Hx; reflexivity)) as (G1 & c' & D1 & Hfr & _).
  assert (Hsv : cmp_svmax (cmp_inlined p nin out) <= nv) by (unfold nv, cmp_nvF; lia).
  destruct (cmp_fc_fwd _ _ _ _ D1 (1, cmp_flat p nin out) 1 nv (cmp_init xs)
              ltac:(unfold cmp_flat, cmp_inlined; apply subcode_refl) Hsv (cmp_eqv_refl _))
    as (fe1 & Q1 & R1).
  assert (Hout : sss_output (cmp_fstep nv) (1, cmp_flat p nin out) (fst (1, cmp_flat p nin out), cmp_init xs)
                   (1 + cmp_flen (cmp_inlined p nin out), fe1)).
  { split; [exact R1 |]. unfold out_code, code_end. cbn [fst snd]. right. rewrite cmp_flat_length. lia. }
  destruct (cmp_mm_output nv (1, cmp_flat p nin out) 1 _ _ _ (cmp_mm_load nv xs)
              (cmp_mm_load_simul nv xs) Hout) as (w2 & Hs2 & Ho).
  exists w2. split.
  - intros x Hx. destruct Hs2 as (A & B & C). rewrite B by (unfold nv, cmp_nvF; unfold nv0 in Hx; lia).
    rewrite <- Q1. specialize (Hfr x Hx). simpl in Hfr. exact Hfr.
  - exact Ho.
Qed.

Theorem cmp_stageA_bwd : forall p nin out, cmp_wf p -> forall xs j w2,
  sss_output mmstep (1, cmp_mm_prog p nin out) (1, cmp_mm_load (cmp_nvF p nin out) xs) (j, w2) ->
  exists e1 c, cmp_ceval (cp_procs p) (cmp_init xs) (cp_main p) e1 c /\
    j = 1 + length (cmp_mm_prog p nin out) /\
    (forall x, x < cmp_nv0 p nin out -> w2 (S x) = e1 x).
Proof.
  intros p nin out [Hwp Hws] xs j w2 Ho.
  set (nv0 := cmp_nv0 p nin out). set (nv := cmp_nvF p nin out).
  assert (Hn0 : cmp_svmax (cp_main p) <= nv0) by (unfold nv0, cmp_nv0; lia).
  assert (Hsv : cmp_svmax (cmp_inlined p nin out) <= nv) by (unfold nv, cmp_nvF; lia).
  destruct (cmp_mm_output_conv nv (1, cmp_flat p nin out) 1 (cmp_init xs) j (cmp_mm_load nv xs) w2
              (cmp_mm_load_simul nv xs) Ho) as (i2 & v2 & Hs2 & [[k Hk] Hfo] & Hj).
  cbn [fst] in Hk.
  assert (Hout : i2 < 1 \/ 1 + cmp_flen (cmp_inlined p nin out) <= i2).
  { destruct Hfo as [H | H]; [left; exact H | right]. unfold code_end in H. cbn [fst snd] in H.
    rewrite cmp_flat_length in H. lia. }
  destruct (cmp_fc_bwd (cmp_inlined p nin out) (cmp_inl_nocall _ _ _ _ _) (1, cmp_flat p nin out) 1 nv
              (cmp_init xs) k i2 v2 ltac:(unfold cmp_flat; apply subcode_refl) Hsv Hk Hout)
    as (e1' & c1 & k1 & fe1 & D1 & Q1 & K1 & R1 & R1').
  assert (Hst : (1 + cmp_flen (cmp_inlined p nin out), fe1) = (i2, v2)).
  { eapply sss_steps_stop with (k := k - k1); [| exact R1'].
    cbn [fst]. unfold out_code, code_end. cbn [fst snd]. right. rewrite cmp_flat_length. lia. }
  inversion Hst; subst.
  destruct (cmp_inl_bwd (cp_procs p) (length (cp_procs p)) (cp_main p) 0 nv0 (cmp_init xs) e1' c1 (cmp_init xs)
              Hwp (Nat.le_refl _) Hws Hn0 D1 ltac:(intros x Hx; reflexivity)) as (e1 & c & D & Hfr & _).
  exists e1, c. split; [exact D |]. split; [first [exact Hj | reflexivity] |].
  intros x Hx. destruct Hs2 as (A & B & C). rewrite B by (unfold nv, cmp_nvF; unfold nv0 in Hx; lia).
  rewrite <- Q1. specialize (Hfr x Hx). simpl in Hfr. exact Hfr.
Qed.

Theorem cmp_stageA : forall p nin out, cmp_wf p -> forall xs y,
  cmp_src_computes p xs out y <->
  exists j w2, sss_output mmstep (1, cmp_mm_prog p nin out) (1, cmp_mm_load (cmp_nvF p nin out) xs) (j, w2) /\
               w2 (S out) = y.
Proof.
  intros p nin out Hwf xs y. split.
  - intros (e1 & c & Hd & Hy).
    destruct (cmp_stageA_fwd p nin out Hwf xs e1 c Hd) as (w2 & Hv & Ho).
    exists (1 + length (cmp_mm_prog p nin out)), w2. split; [exact Ho |].
    rewrite Hv by (unfold cmp_nv0; lia). exact Hy.
  - intros (j & w2 & Ho & Hy).
    destruct (cmp_stageA_bwd p nin out Hwf xs j w2 Ho) as (e1 & c & Hd & _ & Hv).
    exists e1, c. split; [exact Hd |].
    rewrite <- Hy. symmetry. apply Hv. unfold cmp_nv0. lia.
Qed.

Print Assumptions cmp_stageA.
