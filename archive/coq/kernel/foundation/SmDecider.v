(** SmDecider.v: no host program decides a property of what programs
    compute.

    A host program D decides a property Pi of host programs when, run on
    the number of any program p, D stops, and it stops with 1 in register 0
    exactly when Pi p holds  [sm_decides].

    Theorem [sm_no_host_decider]. Let Pi depend only on the partial
    function a program computes, hold of some program and fail of another.
    Then no host program decides Pi.

    The proof builds, from D, a host program that computes D's flip on
    numbers: on the number of p it stops with the number of the "no"
    witness when D says 1, and with the number of the "yes" witness
    otherwise. That program comes from the same route as the evaluator of
    SmKleene.v (a fuel function, L, the vendored Minsky compiler, and
    SmMMAHost.v). Then sm_no_inside_decider of SmKleene.v applies. The
    Boolean function it needs is read off D's runs by a search over step
    counts (ConstructiveEpsilon of the standard library, which uses no
    axiom).

    Dependencies: as SmKleene.v, and ConstructiveEpsilon from the Coq
    standard library. No axioms, no Admitted.                              *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is recursion theory on the host machine, here the machine of EarnedMulti.v read as a numbering of partial functions.
   The host machine's link to the abstract record (a CertificationSystem
   with the trace floor, a Thiele-complete machine, and the halting problem
   of U) lives in UniversalInterpreterLinks.v. *)

From Coq Require Import List Arith Lia Bool ConstructiveEpsilon.
Import ListNotations.
From Undecidability.L Require Import Tactics.LTactics Datatypes.LNat Datatypes.LOptions
  Datatypes.LProd Datatypes.Lists Datatypes.LBool.
From Undecidability.MinskyMachines Require Import MM MMA.
From Undecidability.MinskyMachines.Reductions Require Import L_computable_to_MMA_computable.
Require Minimal.EarnedMulti Minimal.UniversalCodes.
Require Import Minimal.SmHostBlocks Minimal.SmCodes Minimal.SmInterp Kernel.SmEvalL Kernel.SmFuel Kernel.SmMMAHost Kernel.SmKleene.
Module M := Minimal.EarnedMulti.
Module UC := Minimal.UniversalCodes.
Unset Implicit Arguments.

Local Notation hinstr := (@M.instr UC.hprop).
Local Notation hfun := (sm_hfun UC.hprop_eqb UC.heval).
Local Notation hrun_prog := (M.run_prog UC.hprop_eqb UC.heval).

(* D's flip on numbers, for D numbered dc and witnesses numbered nc, yc. *)
Definition sm_flipf (w : nat * (nat * nat)) (fuel x c : nat) : option nat :=
  match sm_kout fuel (sm_kpdec (fst w)) x with
  | Some b => Some (if Nat.eqb b 1 then fst (snd w) else snd (snd w))
  | None => None
  end.

Instance term_sm_flipf : computable sm_flipf. Proof. extract. Qed.

Lemma sm_flipf_mono : forall w n n' x c m,
  sm_flipf w n x c = Some m -> n <= n' -> sm_flipf w n' x c = Some m.
Proof.
  intros w n n' x c m H Hle. unfold sm_flipf in *.
  destruct (sm_kout n (sm_kpdec (fst w)) x) as [b |] eqn:Hb; [| discriminate].
  rewrite (sm_kout_mono n n' _ _ b Hle Hb). exact H.
Qed.

Definition sm_Rflip (w : nat * (nat * nat)) (v : Vector.t nat 2) (m : nat) : Prop :=
  exists n, sm_flipf w n (Vector.hd v) (Vector.hd (Vector.tl v)) = Some m.

Lemma sm_flip_MMA : forall w, MMA_computable (sm_Rflip w).
Proof.
  intro w. apply L_computable_to_MMA_computable.
  exact (@sm_L_computable_fuel2 (nat * (nat * nat)) _ sm_flipf _ w (sm_flipf_mono w)).
Qed.

Definition sm_decides (D : list hinstr) (Pi : list hinstr -> Prop) : Prop :=
  forall p, (exists b, hfun D (sm_hcode p) b) /\ (hfun D (sm_hcode p) 1 <-> Pi p).

(* A host program that computes a map g on numbers, given as a run of the
   interpreter. *)
Lemma sm_flip_program : forall w, exists T : list hinstr,
  forall x m, hfun T x m <-> exists n, sm_flipf w n x 0 = Some m.
Proof.
  intro w. destruct (sm_flip_MMA w) as [nn [Pm HPm]].
  exists (sm_mma_host (S (S (S nn))) Pm). intros x m.
  transitivity (sm_Rflip w (Vector.cons nat x 1 (Vector.cons nat 0 0 (Vector.nil nat))) m);
    [| reflexivity].
  symmetry.
  rewrite (sm_mma_two nn Pm (sm_Rflip w) HPm (M.core_of (sm_hstart x)) x 0 m eq_refl eq_refl).
  - unfold sm_hfun, sm_hends. split.
    + intros [n [Hh Hv]]. exists (hrun_prog n (sm_mma_host (S (S (S nn))) Pm) (sm_hstart x)).
      split.
      * exists n. split; [reflexivity |]. rewrite sm_core_run. exact Hh.
      * rewrite sm_core_run. exact Hv.
    + intros [s [[n [-> Hh]] Hv]]. exists n. rewrite sm_core_run in Hh, Hv. split; assumption.
  - intro r. cbn [M.vals M.core_of sm_hstart M.start M.start_core]. unfold sm_hin, sm_in2.
    destruct (Nat.eqb r 1); [reflexivity |]. destruct (Nat.eqb r 2); reflexivity.
Qed.

Theorem sm_no_host_decider : forall (Pi : list hinstr -> Prop) yes no,
  sm_fun_ext Pi -> Pi yes -> ~ Pi no ->
  ~ exists D, sm_decides D Pi.
Proof.
  intros Pi yes no Hext Hy Hn [D HD].
  (* The answer of D on p, found by a search over step counts. *)
  assert (Hsearch : forall p, {b : nat | hfun D (sm_hcode p) b}).
  { intro p.
    assert (Hex : exists n, exists b, sm_kout n (sm_kpdec (sm_hcode D)) (sm_hcode p) = Some b).
    { destruct (proj1 (HD p)) as [b Hb].
      assert (Hb' : hfun (sm_hdecode (sm_hcode D)) (sm_hcode p) b) by (rewrite sm_hdecode_hcode; exact Hb).
      apply (proj2 (sm_uev_spec _ _ _)) in Hb'. destruct Hb' as [n Hn']. exists n, b. exact Hn'. }
    assert (Hdec : forall n, {exists b, sm_kout n (sm_kpdec (sm_hcode D)) (sm_hcode p) = Some b} +
                             {~ exists b, sm_kout n (sm_kpdec (sm_hcode D)) (sm_hcode p) = Some b}).
    { intro n. destruct (sm_kout n (sm_kpdec (sm_hcode D)) (sm_hcode p)) as [b |].
      - left. exists b. reflexivity.
      - right. intros [b Hb]. discriminate. }
    destruct (constructive_indefinite_ground_description_nat _ Hdec Hex) as [n Hn'].
    destruct (sm_kout n (sm_kpdec (sm_hcode D)) (sm_hcode p)) as [b |] eqn:Hb.
    - exists b. rewrite <- (sm_hdecode_hcode D). apply sm_uev_spec. exists n. exact Hb.
    - exfalso. destruct Hn' as [b Hb']. discriminate. }
  set (d := fun p => Nat.eqb (proj1_sig (Hsearch p)) 1).
  apply (sm_no_inside_decider Pi yes no Hext Hy Hn d).
  - destruct (sm_flip_program (sm_hcode D, (sm_hcode no, sm_hcode yes))) as [T HT].
    exists T. intro p. apply HT.
    destruct (Hsearch p) as [b Hb] eqn:Hs.
    assert (Hb' := Hb). rewrite <- (sm_hdecode_hcode D) in Hb'.
    apply (proj2 (sm_uev_spec _ _ _)) in Hb'. destruct Hb' as [n Hn'].
    exists n. unfold sm_flipf. cbn [fst snd]. unfold sm_uev in Hn'. rewrite Hn'.
    unfold d. rewrite Hs. cbn [proj1_sig]. destruct (Nat.eqb b 1); reflexivity.
  - intro p. unfold d. destruct (Hsearch p) as [b Hb]. cbn [proj1_sig]. split.
    + intro Hb1. apply Nat.eqb_eq in Hb1. subst b. apply (proj2 (HD p)). exact Hb.
    + intro HPi. apply (proj2 (HD p)) in HPi.
      rewrite (sm_hfun_det UC.hprop_eqb UC.heval D _ b 1 Hb HPi). reflexivity.
Qed.

Print Assumptions sm_no_host_decider.
