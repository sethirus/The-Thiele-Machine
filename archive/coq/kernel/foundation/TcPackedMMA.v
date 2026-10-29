(** TcPackedMMA.v: any vendored alternate-Minsky program, as a two-counter
    program with packed inputs and exact outputs.

    Let P be a program of the vendored machine with 3 + n0 registers that
    computes a relation R(x, e, m): started with 0 in register 0, x in
    register 1, e in register 2 and 0 elsewhere, it stops with m in register
    0 exactly when R x e m. Then there is a program U of the small machine
    (INC and DEC only, so it neither pays nor records anything) such that,
    started with 2^x * 3^e in counter A and 0 in counter B,

        U stops with exactly 2^y in counter A   if and only if   R x e y.

    [tc_mma_packed] is this statement. The construction: P is made to leave
    through its last line (TcNorm.v); an epilogue empties every register but
    register 0 and moves it into register 1 (TcEpi.v); the result is compiled
    to a two-register program in which register j lives in the exponent of
    the j-th modulus, the moduli of registers 1 and 2 being 2 and 3
    (TcMod.v, TcCompile0.v); and that program is read through the bridge
    (TcBridge.v). Nothing is assumed about P beyond what R says.

    Dependencies: the Tc files named above and TcCompose.v. No axioms and no unfinished proofs.                                                               *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is recursion theory on the two-counter machine of EarnedCore.v (its
   programs, runs and the numbering of programs). The machine's link to the
   abstract record (a CertificationSystem with the trace cost floor, and a
   Thiele-complete machine) lives in EarnedCoreLinks.v and ThieleComplete.v. *)


From Coq Require Import List Arith Lia.
Import ListNotations.
From Undecidability.Shared.Libs.DLW Require Import utils gcd godel_coding pos vec subcode sss.
From Undecidability.MinskyMachines Require Import MM MMA.
From Undecidability.MinskyMachines.MMA Require Import mma_defs mma_utils.
Require Import Kernel.TcGodel Kernel.TcMod Kernel.TcBridge Kernel.TcNorm Kernel.TcEpi Kernel.TcCompile0 Minimal.TcBlocks Kernel.TcRice Kernel.TcCompose.
Module E := Minimal.EarnedCore.
Set Default Goal Selector "!".

#[local] Notation "e #> x" := (vec_pos e x).

Definition tc_init (n0 x e : nat) : vec nat (3 + n0) := 0 ## x ## e ## vec_zero (n := n0).

Section Pp.
  Variable (n0 : nat) (P : list (mm_instr (pos (3 + n0)))).

  Definition tc_P1 : list (mm_instr (pos (3 + n0))) := tc_normcode P 1.
  Definition tc_Pp : list (mm_instr (pos (3 + n0))) := tc_P1 ++ tc_epi n0 (1 + length tc_P1).

  Lemma tc_Pp_length : 1 + length tc_Pp = length (tc_L n0) + 3 + (1 + length tc_P1).
  Proof. unfold tc_Pp. rewrite app_length, tc_epi_length. lia. Qed.

  Lemma tc_Pp_halts : forall v c w,
    sss_output (@mma_sss (3 + n0)) (1, P) (1, v) (c, w) ->
    sss_output (@mma_sss (3 + n0)) (1, tc_Pp) (1, v) (1 + length tc_Pp, tc_unit1 n0 (w#>pos0)).
  Proof.
    intros v c w Hout.
    pose proof (tc_normcode_halts Hout 1) as Hn. fold tc_P1 in Hn.
    destruct Hn as [Hnc _].
    split.
    - eapply sss_compute_trans.
      + eapply subcode_sss_compute; [| exact Hnc].
        exists [], (tc_epi n0 (1 + length tc_P1)). split; [reflexivity | reflexivity].
      + replace (1 + length tc_P1) with (1 + length tc_P1) by reflexivity.
        pose proof (tc_epi_run n0 (1 + length tc_P1) w) as Hrun.
        rewrite tc_Pp_length.
        eapply subcode_sss_compute; [| exact Hrun].
        exists tc_P1, []. split; [unfold tc_Pp; rewrite app_nil_r; reflexivity | simpl; lia].
    - unfold out_code, code_end. cbn [fst snd]. right. pose proof tc_Pp_length. lia.
  Qed.

  Lemma tc_Pp_terminates : forall v,
    sss_terminates (@mma_sss (3 + n0)) (1, tc_Pp) (1, v) ->
    sss_terminates (@mma_sss (3 + n0)) (1, P) (1, v).
  Proof.
    intros v Ht.
    apply (proj1 (tc_normcode_terminates P v 1)).
    fold tc_P1.
    assert (Hsc : subcode (1, tc_P1) (1, tc_Pp)).
    { exists [], (tc_epi n0 (1 + length tc_P1)). split; reflexivity. }
    exact (@subcode_sss_terminates _ _ (@mma_sss (3 + n0)) (1, tc_P1) (1, tc_Pp) (1, v) Hsc Ht).
  Qed.

  (* whatever the compiled prefix outputs is the unit file of what P outputs *)
  Lemma tc_Pp_output : forall v j w,
    sss_output (@mma_sss (3 + n0)) (1, tc_Pp) (1, v) (j, w) ->
    exists c w', sss_output (@mma_sss (3 + n0)) (1, P) (1, v) (c, w') /\
                 j = 1 + length tc_Pp /\ w = tc_unit1 n0 (w'#>pos0).
  Proof.
    intros v j w Hout.
    assert (Ht : sss_terminates (@mma_sss (3 + n0)) (1, tc_Pp) (1, v)) by (exists (j, w); exact Hout).
    apply tc_Pp_terminates in Ht. destruct Ht as [[c w'] Hc].
    exists c, w'. split; [exact Hc |].
    pose proof (tc_Pp_halts Hc) as H2.
    pose proof (sss_output_fun (@mma_sss_fun (3 + n0)) Hout H2) as E1.
    injection E1 as E2 E3. split; assumption.
  Qed.
End Pp.

Lemma tc_unit1_shape : forall n0 y, tc_unit1 n0 y = 0 ## y ## 0 ## vec_zero (n := n0).
Proof.
  intros n0 y. apply vec_pos_ext. intro p. unfold tc_unit1. rewrite vec_pos_set.
  change (pos (S (S (S n0)))) in p.
  pos_inv p.
  - destruct (pos_eq_dec (pos0 : pos (3 + n0)) pos1) as [E | E]; [discriminate E | reflexivity].
  - pos_inv p.
    + destruct (pos_eq_dec (pos1 : pos (3 + n0)) pos1) as [E | E]; [reflexivity | exfalso; apply E; reflexivity].
    + pos_inv p.
      * destruct (pos_eq_dec (pos2 : pos (3 + n0)) pos1) as [E | E]; [discriminate E | reflexivity].
      * destruct (pos_eq_dec (pos_nxt (pos_nxt (pos_nxt p)) : pos (3 + n0)) pos1) as [E | E];
          [discriminate E | ].
        simpl. rewrite vec_zero_spec. reflexivity.
Qed.

Theorem tc_mma_packed : forall n0 (P : list (mm_instr (pos (3 + n0)))) (R : nat -> nat -> nat -> Prop),
  (forall x e m, R x e m <->
     exists c v', sss_output (@mma_sss (3 + n0)) (1, P) (1, tc_init n0 x e) (c, m ## v')) ->
  exists U : list E.instr, forall x e y,
    (exists s, tc_ends (2 ^ x * 3 ^ e) U s /\ E.ca (E.core_of s) = 2 ^ y) <-> R x e y.
Proof.
  intros n0 P R HR.
  destruct (tc_moduli_for n0) as [ms [Hok [Hm1 Hm2]]].
  destruct (tc_cons_inv ms) as [m0 [t ->]].
  destruct (tc_cons_inv t) as [m1 [t' ->]].
  destruct (tc_cons_inv t') as [m2 [ms' ->]].
  simpl in Hm1, Hm2. subst m1 m2.
  set (gc := tc_gc Hok).
  assert (Hres : forall p, Nat.gcd (gc_pr gc p) 1 = 1) by (intro p; apply tc_gcd_1_r).
  set (Q := tc_code0 gc (tc_Pp P) 1).
  exists (E.compile (tc_P Q)).
  intros x e y.
  assert (Henc : gc_enc gc (tc_init n0 x e) = 2 ^ x * 3 ^ e).
  { assert (E : gc_enc gc (tc_init n0 x e) = tc_enc (m0 ## 2 ## 3 ## ms') (tc_init n0 x e)) by reflexivity.
    rewrite E. unfold tc_init. rewrite tc_enc_three. simpl. lia. }
  assert (Henc1 : forall m, gc_enc gc (tc_unit1 n0 m) = 2 ^ m).
  { intro m. rewrite tc_unit1_shape.
    assert (E : gc_enc gc (0 ## m ## 0 ## vec_zero (n := n0)) = tc_enc (m0 ## 2 ## 3 ## ms') (0 ## m ## 0 ## vec_zero (n := n0))) by reflexivity.
    rewrite E. rewrite tc_enc_three. simpl. lia. }
  split.
  - intros [s [Hends Hca]].
    destruct (tc_compile_ends (tc_P Q) _ s Hends) as [m [c' [Hsteps [Hstop [Hca' Hcb']]]]].
    destruct c' as [j [a b]]. simpl in Hca', Hcb'.
    assert (Hout : sss_output (@mma_sss 2) (1, Q) (1, tc_st2 (1 * gc_enc gc (tc_init n0 x e)))
                              (j, tc_tovec a b)).
    { apply tc_output_iff. exists m. rewrite Henc, Nat.mul_1_l. split; [exact Hsteps | exact Hstop]. }
    destruct (tc_comp0_complete gc (tc_Pp P) (tc_init n0 x e) 1 Hres Hout)
      as [j' [v' [Hout' Hw]]].
    assert (Ha : a = 1 * gc_enc gc v').
    { pose proof (f_equal (fun v : vec nat 2 => v#>pos1) Hw) as H1. exact H1. }
    destruct (tc_Pp_output Hout') as [c [w' [Hc [_ Hv']]]].
    subst v'. rewrite Henc1 in Ha. rewrite Nat.mul_1_l in Ha.
    assert (Hy : w'#>pos0 = y).
    { apply (Nat.pow_inj_r 2); [lia |]. rewrite <- Ha. rewrite <- Hca'. exact Hca. }
    apply HR. destruct (tc_cons_inv w') as [h [tl ->]]. simpl in Hy. subst h.
    exists c, tl. exact Hc.
  - intro HRy. apply HR in HRy. destruct HRy as [c [v' Hc]].
    pose proof (tc_Pp_halts Hc) as Hp. simpl in Hp.
    pose proof (tc_comp0_halts gc Hp 1 Hres 1) as Hq.
    apply tc_output_iff in Hq. destruct Hq as [m [Hsteps Hstop]].
    rewrite Henc, Henc1, !Nat.mul_1_l in Hsteps. rewrite Henc1, Nat.mul_1_l in Hstop.
    destruct (tc_ends_compile (tc_P Q) _ m _ Hsteps Hstop) as [s [Hends [Hca _]]].
    exists s. split; [exact Hends |]. simpl in Hca. exact Hca.
Qed.

Print Assumptions tc_mma_packed.
