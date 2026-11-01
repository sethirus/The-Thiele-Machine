(** TcCompile0.v: the Goedel-number compiler from k registers to two, with
    no uncoded registers.

    This is the compiler of TcCompile.v (a copy of the vendored
    MMA/mma_k_mma_2_compiler.v with a factor res riding in the code) with
    the uncoded registers removed: every register of the source machine is
    coded in counter A as the exponent of its modulus, and counter B is the
    spare. A source state v is simulated by the target state
        0 ## res * code(v) ## nil
    (the spare 0, then counter A holding res times the code of v).

    [tc_comp0 res] is a vendored compiler record; [tc_code0 P i] is the
    code of P at address i. The code does not depend on res (checked by
    reflexivity in TcCompile.v for the version with uncoded registers; here
    the code is built from icomp0, which does not mention res).

    The statements used later are packaged as [tc_comp0_halts],
    [tc_comp0_terminates] and [tc_comp0_complete].

    Dependencies: Coq standard library, the vendored coq-undecidability
    library. No axioms and no unfinished proofs.                                        *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is recursion theory on the two-counter machine of EarnedCore.v (its
   programs, runs and the numbering of programs). The machine's link to the
   abstract record (a CertificationSystem with the trace cost floor, and a
   Thiele-complete machine) lives in EarnedCoreLinks.v and ThieleComplete.v. *)


Require Import List Arith Lia.

From Undecidability.Shared.Libs.DLW
  Require Import utils gcd godel_coding pos vec subcode sss compiler_correction.

From Undecidability.MinskyMachines.MMA
  Require Import mma_defs mma_utils.

Set Implicit Arguments.
Set Default Goal Selector "!".

#[local] Notation "e #> x" := (vec_pos e x).
#[local] Notation "e [ v / x ]" := (vec_change e x v).

Section comp0.

  Variable (k : nat) (gc : godel_coding k).

  Local Notation r := (pos1 : pos 2).
  Local Notation s := (pos0 : pos 2).

  Local Definition icomp0 (lnk : nat -> nat) (i : nat) (x : mm_instr (pos k)) : list (mm_instr (pos 2)) :=
    match x with
    | mm_inc p => mma_mult_cst_with_zero r s (gc_pr gc p) (lnk i)
    | mm_dec p j => mma_div_branch r s (gc_pr gc p) (lnk i) (lnk j)
    end.

  Local Definition ilen0 (x : mm_instr (pos k)) : nat :=
    match x with
    | mm_inc p => 8 + gc_pr gc p
    | mm_dec p j => 16 + 7 * gc_pr gc p
    end.

  Local Fact icomp0_len : forall lnk i x, length (icomp0 lnk i x) = ilen0 x.
  Proof.
    intros lnk i [p | p j]; simpl.
    - apply mma_mult_cst_with_zero_length.
    - apply mma_div_branch_length.
  Qed.

  Variable (res : nat) (Hres : forall p, Nat.gcd (gc_pr gc p) res = 1).

  Let simul (v : vec nat k) (w : vec nat 2) : Prop := w = 0 ## (res * gc_enc gc v) ## vec_nil.

  Local Fact gcr_succ p v : gc_pr gc p * (res * gc_enc gc v) = res * gc_enc gc (v[(S (v#>p))/p]).
  Proof. rewrite <- gc_succ. ring. Qed.

  Local Fact gcr_not_div p v : v#>p = 0 -> ~ divides (gc_pr gc p) (res * gc_enc gc v).
  Proof.
    intros H [c Hc]. apply (gc_not_div gc p v H).
    assert (Hd : Nat.divide (gc_pr gc p) (res * gc_enc gc v)) by (exists c; exact Hc).
    apply Nat.gauss in Hd; [| apply Hres].
    exact Hd.
  Qed.

  Local Fact vec_change_back (v : vec nat k) p a : v#>p = S a -> (v[a/p])[(S ((v[a/p])#>p))/p] = v.
  Proof.
    intros H. apply vec_pos_ext. intro q.
    destruct (pos_eq_dec q p) as [-> | D].
    - rewrite vec_change_eq by reflexivity. rewrite vec_change_eq by reflexivity. rewrite H. reflexivity.
    - rewrite vec_change_neq by auto. rewrite vec_change_neq by auto. reflexivity.
  Qed.

  Local Lemma icomp0_sound :
    instruction_compiler_sound icomp0 (@mma_sss k) (@mma_sss 2) simul.
  Proof.
    intros lnk I i1 v1 i2 v2 w1 H Hl Hs. unfold simul in Hs. subst w1.
    rewrite icomp0_len in Hl.
    destruct I as [p | p j]; simpl in Hl |- *.
    - apply mma_sss_INC_inv in H as [-> ->].
      exists (0 ## (gc_pr gc p * (res * gc_enc gc v1)) ## vec_nil). split.
      + replace (lnk (1 + i1)) with (8 + gc_pr gc p + lnk i1) by lia.
        apply mma_mult_cst_with_zero_progress.
        * discriminate.
        * reflexivity.
        * reflexivity.
      + unfold simul. rewrite gcr_succ. reflexivity.
    - destruct (v1#>p) as [| a] eqn:Hp.
      + apply mma_sss_DEC0_inv in H; [| exact Hp]. destruct H as [-> ->].
        exists (0 ## (res * gc_enc gc v1) ## vec_nil). split; [| reflexivity].
        replace (lnk (1 + i1)) with (16 + 7 * gc_pr gc p + lnk i1) by lia.
        apply mma_div_branch_1_progress.
        * discriminate.
        * reflexivity.
        * pose proof (gc_pr_nz gc p). lia.
        * apply gcr_not_div. exact Hp.
        * reflexivity.
      + apply mma_sss_DEC1_inv with (u := a) in H; [| exact Hp]. destruct H as [-> ->].
        exists (0 ## (res * gc_enc gc (v1[a/p])) ## vec_nil). split.
        * apply mma_div_branch_0_progress with (a := res * gc_enc gc (v1[a/p])).
          -- discriminate.
          -- reflexivity.
          -- pose proof (gc_pr_nz gc p). lia.
          -- simpl.
             pose proof (gcr_succ p (v1[a/p])) as E. rewrite (vec_change_back v1 p Hp) in E.
             rewrite <- E. ring.
          -- reflexivity.
        * reflexivity.
  Qed.

  Definition tc_comp0 : compiler_t (@mma_sss k) (@mma_sss 2) simul.
  Proof.
    apply generic_compiler with icomp0 ilen0.
    + intros; apply icomp0_len.
    + apply mma_sss_total_ni.
    + apply mma_sss_fun.
    + apply icomp0_sound.
  Defined.

End comp0.

(* the code does not mention res *)
Definition tc_code0 (k : nat) (gc : godel_coding k) (P : list (mm_instr (pos k))) (i : nat) :
  list (mm_instr (pos 2)) :=
  gc_code (tc_comp0 gc 1 (fun p => Nat.divide_1_r _ ltac:(apply Nat.gcd_divide_r))) (1, P) i.

Lemma tc_code0_indep : forall (k : nat) (gc : godel_coding k) P i res H,
  gc_code (tc_comp0 gc res H) (1, P) i = tc_code0 gc P i.
Proof. reflexivity. Qed.

Definition tc_st2 (a : nat) : vec nat 2 := 0 ## a ## vec_nil.

Theorem tc_comp0_halts : forall k (gc : godel_coding k) P v j v',
  sss_output (@mma_sss k) (1, P) (1, v) (j, v') ->
  forall res (Hres : forall p, Nat.gcd (gc_pr gc p) res = 1) i,
  sss_output (@mma_sss 2) (i, tc_code0 gc P i) (i, tc_st2 (res * gc_enc gc v))
             (i + length (tc_code0 gc P i), tc_st2 (res * gc_enc gc v')).
Proof.
  intros k gc P v j v' Hout res Hres i.
  destruct (@compiler_t_output_sound' _ _ _ _ _ _ _ (tc_comp0 gc res Hres) (1, P) i v
              (tc_st2 (res * gc_enc gc v)) j v' eq_refl Hout) as [w' [Hw' Hs1]].
  unfold tc_st2 in *. cbv beta in Hs1. subst w'. exact Hw'.
Qed.

Theorem tc_comp0_terminates : forall k (gc : godel_coding k) P v,
  forall res (Hres : forall p, Nat.gcd (gc_pr gc p) res = 1) i,
  sss_terminates (@mma_sss k) (1, P) (1, v) <->
  sss_terminates (@mma_sss 2) (i, tc_code0 gc P i) (i, tc_st2 (res * gc_enc gc v)).
Proof.
  intros k gc P v res Hres i.
  apply (@compiler_t_term_equiv _ _ _ _ _ _ _ (tc_comp0 gc res Hres) (1, P) i v
           (tc_st2 (res * gc_enc gc v)) eq_refl).
Qed.

Theorem tc_comp0_complete : forall k (gc : godel_coding k) P v,
  forall res (Hres : forall p, Nat.gcd (gc_pr gc p) res = 1) i j w,
  sss_output (@mma_sss 2) (i, tc_code0 gc P i) (i, tc_st2 (res * gc_enc gc v)) (j, w) ->
  exists j' v', sss_output (@mma_sss k) (1, P) (1, v) (j', v') /\ w = tc_st2 (res * gc_enc gc v').
Proof.
  intros k gc P v res Hres i j w Hout.
  pose proof (gc_fst (tc_comp0 gc res Hres) (1, P) i) as Hfst. simpl in Hfst.
  destruct (@gc_complete _ _ _ _ _ _ _ (tc_comp0 gc res Hres) (1, P) i 1 v (tc_st2 (res * gc_enc gc v)) j w)
    as [i2 [v2 [Hsim [Hout2 _]]]].
  - split; [reflexivity |].
    match goal with |- sss_output _ _ (?a, _) _ => replace a with i by exact Hfst end.
    exact Hout.
  - exists i2, v2. split; [exact Hout2 | exact Hsim].
Qed.

Print Assumptions tc_comp0_halts.
Print Assumptions tc_comp0_complete.
