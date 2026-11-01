(** TcPacked.v: the two-counter machine with packed inputs is an acceptable
    programming system, and Kleene's recursion theorem holds in it.

    The packed reading. A program P of the small machine computes y from x,
    [tc_pk P x y], when started with 2^x in counter A and 0 in counter B it
    stops with exactly 2^y in counter A (Minsky 1961 and Schroeppel 1972
    code numbers this way). Two inputs are packed as 2^x * 3^e,
    [tc_pk2 V x e y].

    Proved here, with no assumption:

      [tc_pk_unique]        the output is unique
      [tc_universal]        one two-counter program U with
                            tc_pk2 U x e y <-> tc_pk (tc_pdec e) x y
      [tc_smn]              tc_pk (tc_spec c V) x y <-> tc_pk2 V x c y
      [tc_second_recursion] for every program T there is a program e with
                            tc_pk e x y <-> exists d, tc_pk T (tc_pcode e) d
                                                    /\ tc_pk (tc_pdec d) x y
      [tc_kleene]           for every transformation F of programs that some
                            program T carries out on program numbers there
                            is a program e that computes the same function
                            as F e
      [tc_rice_packed]      (TcRice.v) every extensional nontrivial property
                            is undecidable

    The universal program and the evaluator in the recursion theorem come
    from finite algorithms written out in TcInterp.v, turned into lambda
    calculus terms and then into Minsky programs by the vendored compilers
    (TcEvalL.v, TcFuel.v) and into a two-counter program by the compiler of
    TcPackedMMA.v. Those tools supply the programs and certify their
    input-output relations; the fixed-point argument is the textbook one.

    Dependencies: the Tc files named above. No axioms and no unfinished proofs.         *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is recursion theory on the two-counter machine of EarnedCore.v (its
   programs, runs and the numbering of programs). The machine's link to the
   abstract record (a CertificationSystem with the trace cost floor, and a
   Thiele-complete machine) lives in EarnedCoreLinks.v and ThieleComplete.v. *)


From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Undecidability.Shared.Libs.DLW Require Import utils pos vec subcode sss.
From Undecidability.MinskyMachines Require Import MM MMA.
From Undecidability.MinskyMachines.MMA Require Import mma_defs.
Require Import Kernel.TcGodel Kernel.TcBridge Minimal.TcBlocks Kernel.TcRice Kernel.TcCompose Kernel.TcGadget Kernel.TcCodes Kernel.TcInterp
  Kernel.TcPackedMMA Kernel.TcEvalL Kernel.TcFuel.
Module E := Minimal.EarnedCore.
Set Default Goal Selector "!".

Definition tc_pk2 (V : list E.instr) (x e y : nat) : Prop :=
  exists s, tc_ends (2 ^ x * 3 ^ e) V s /\ E.ca (E.core_of s) = 2 ^ y.

(* ================================================================= *)
(* Determinism                                                        *)
(* ================================================================= *)

Lemma tc_ends_unique : forall n P s t, tc_ends n P s -> tc_ends n P t -> s = t.
Proof.
  intros n P s t [N [-> HN]] [M [-> HM]].
  destruct (Nat.le_ge_cases N M) as [H | H].
  - symmetry. apply tc_ghalted_after; assumption.
  - apply tc_ghalted_after; assumption.
Qed.

Theorem tc_pk_unique : forall P x y y', tc_pk P x y -> tc_pk P x y' -> y = y'.
Proof.
  intros P x y y' [s [Hs Hy]] [t [Ht Hy']].
  rewrite (tc_ends_unique Hs Ht) in Hy. rewrite Hy in Hy'.
  apply (Nat.pow_inj_r 2); [lia | exact Hy'].
Qed.

Theorem tc_pk2_unique : forall P x e y y', tc_pk2 P x e y -> tc_pk2 P x e y' -> y = y'.
Proof.
  intros P x e y y' [s [Hs Hy]] [t [Ht Hy']].
  rewrite (tc_ends_unique Hs Ht) in Hy. rewrite Hy in Hy'.
  apply (Nat.pow_inj_r 2); [lia | exact Hy'].
Qed.

(* ================================================================= *)
(* The vendored computability relation, read as a packed program      *)
(* ================================================================= *)

Lemma tc_const_zero : forall n0, Vector.const 0 n0 = vec_zero (n := n0).
Proof.
  intro n0. apply vec_pos_ext. intro p. rewrite vec_zero_spec.
  induction p as [m | m p IH]; [reflexivity | simpl; exact IH].
Qed.

Theorem tc_MMA_to_packed : forall (R : Vector.t nat 2 -> nat -> Prop),
  MMA_computable R ->
  exists U : list E.instr, forall x e y, tc_pk2 U x e y <-> R (Vector.cons nat x 1 (Vector.cons nat e 0 (Vector.nil nat))) y.
Proof.
  intros R [n0 [P HP]].
  assert (Hsem : forall x e m, R (Vector.cons nat x 1 (Vector.cons nat e 0 (Vector.nil nat))) m <->
     exists c v', sss_output (@mma_sss (3 + n0)) (1, P) (1, tc_init n0 x e) (c, m ## v')).
  { intros x e m. rewrite HP. rewrite tc_const_zero. reflexivity. }
  destruct (tc_mma_packed (R := fun x e m => R (Vector.cons nat x 1 (Vector.cons nat e 0 (Vector.nil nat))) m)
              (P := P) Hsem) as [U HU].
  exists U. intros x e y. unfold tc_pk2. apply HU.
Qed.

(* ================================================================= *)
(* The universal program                                              *)
(* ================================================================= *)

Theorem tc_universal : exists U : list E.instr,
  forall x e y, tc_pk2 U x e y <-> tc_pk (tc_pdec e) x y.
Proof.
  destruct (tc_MMA_to_packed tc_uev_MMA) as [U HU].
  exists U. intros x e y. rewrite HU. unfold tc_Ruev. simpl.
  apply tc_uev_spec.
Qed.

(* ================================================================= *)
(* s-m-n                                                              *)
(* ================================================================= *)

Theorem tc_smn : forall c V x y, tc_pk (tc_spec c V) x y <-> tc_pk2 V x c y.
Proof.
  intros c V x y.
  set (M := tc_P (tc_vchain 3 c 1)).
  assert (HM : length M = c * 11).
  { unfold M, tc_P. rewrite map_length, tc_vchain_length. lia. }
  assert (Hrun : sss_output (@mma_sss 2) (1, tc_vchain 3 c 1) (1, tc_tovec (2 ^ x) 0)
                            (c * (8 + 3) + 1, tc_tovec (3 ^ c * 2 ^ x) 0)).
  { split.
    - replace (c * (8 + 3) + 1) with (c * (8 + 3) + 1) by reflexivity.
      exact (tc_vchain_run 3 c 1 (2 ^ x)).
    - unfold out_code, code_end. cbn [fst snd]. right. rewrite tc_vchain_length. lia. }
  apply tc_output_iff in Hrun. destruct Hrun as [m [Hsteps _]].
  fold M in Hsteps. change (tc_ofvec (tc_tovec (2 ^ x) 0)) with (2 ^ x, 0) in Hsteps.
  change (tc_ofvec (tc_tovec (3 ^ c * 2 ^ x) 0)) with (3 ^ c * 2 ^ x, 0) in Hsteps.
  assert (Hlen : c * (8 + 3) + 1 = S (length M)) by (rewrite HM; lia).
  rewrite Hlen in Hsteps.
  pose proof (tc_compose_halts M (2 ^ x) (3 ^ c * 2 ^ x) V m Hsteps) as [H1 H2].
  unfold tc_pk, tc_pk2.
  assert (Hsp : tc_spec c V = E.compile M ++ tc_greloc (length M) V)
    by (unfold tc_spec; rewrite HM; reflexivity).
  rewrite Hsp. rewrite (Nat.mul_comm (2 ^ x) (3 ^ c)).
  split.
  - intros [s [Hs Hy]]. destruct (H1 s Hs) as [t [Ht Ha]]. exists t. split; [exact Ht |].
    destruct Ha as (Ha & _). rewrite <- Ha. exact Hy.
  - intros [t [Ht Hy]]. destruct (H2 t Ht) as [s [Hs Ha]]. exists s. split; [exact Hs |].
    destruct Ha as (Ha & _). rewrite Ha. exact Hy.
Qed.

(* ================================================================= *)
(* The second recursion theorem                                       *)
(* ================================================================= *)

Theorem tc_second_recursion : forall T : list E.instr, exists e : list E.instr,
  forall x y, tc_pk e x y <->
    exists d, tc_pk T (tc_pcode e) d /\ tc_pk (tc_pdec d) x y.
Proof.
  intro T.
  destruct (tc_MMA_to_packed (tc_ev_MMA (tc_pcode T))) as [VG HVG].
  set (c0 := tc_pcode VG).
  exists (tc_spec c0 VG). intros x y.
  rewrite tc_smn, HVG. unfold tc_Rev. simpl.
  rewrite tc_ev_spec. rewrite tc_pdec_pcode.
  assert (Hk : tc_kspec c0 = tc_pcode (tc_spec c0 VG)).
  { rewrite tc_kspec_code. unfold c0. rewrite tc_pdec_pcode. reflexivity. }
  rewrite Hk. reflexivity.
Qed.

(* Kleene's recursion theorem: a transformation of programs that a program
   carries out on program numbers has a fixed point up to computing the
   same function. *)
Definition tc_computes_map (T : list E.instr) (F : list E.instr -> list E.instr) : Prop :=
  forall p, tc_pk T (tc_pcode p) (tc_pcode (F p)).

Theorem tc_kleene : forall (F : list E.instr -> list E.instr) (T : list E.instr),
  tc_computes_map T F ->
  exists e, forall x y, tc_pk e x y <-> tc_pk (F e) x y.
Proof.
  intros F T HT. destruct (tc_second_recursion T) as [e He]. exists e. intros x y.
  rewrite He. split.
  - intros [d [Hd Hx]]. rewrite (tc_pk_unique Hd (HT e)) in Hx.
    rewrite tc_pdec_pcode in Hx. exact Hx.
  - intro H. exists (tc_pcode (F e)). split; [apply HT |]. rewrite tc_pdec_pcode. exact H.
Qed.

(* the same statement for transformations of program numbers *)
Theorem tc_kleene_codes : forall (f : nat -> nat) (T : list E.instr),
  (forall n, tc_pk T n (f n)) ->
  exists e, forall x y, tc_pk (tc_pdec e) x y <-> tc_pk (tc_pdec (f e)) x y.
Proof.
  intros f T HT. destruct (tc_second_recursion T) as [e He].
  exists (tc_pcode e). intros x y. rewrite tc_pdec_pcode. rewrite He. split.
  - intros [d [Hd Hx]]. rewrite (tc_pk_unique Hd (HT (tc_pcode e))) in Hx. exact Hx.
  - intro H. exists (f (tc_pcode e)). split; [apply HT | exact H].
Qed.

Print Assumptions tc_universal.
Print Assumptions tc_smn.
Print Assumptions tc_second_recursion.
Print Assumptions tc_kleene.
Print Assumptions tc_kleene_codes.
