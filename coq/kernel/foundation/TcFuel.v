(** TcFuel.v: a monotone fuel function of two numbers is L-computable, and
    so is a program of the vendored alternate Minsky machine.

    [tc_L_computable_fuel2]: for a computable f with f d n x c monotone in
    the fuel n, the relation "some fuel n has f d n x c = Some m" is
    L-computable, by unbounded search over the fuel ([tc_mu_option]).

    [tc_ev_MMA], [tc_uev_MMA]: the two packed evaluators of TcInterp.v, as
    relations of two numbers, are MMA_computable: the vendored theorem
    [L_computable_to_MMA_computable] gives a program of the vendored
    alternate Minsky machine with the two inputs in registers 1 and 2 and
    the answer in register 0.

    [tc_mu_option] and [tc_mu_option_spec] are copied, renamed with the tc_
    prefix, from the vendored Undecidability.L.Reductions.HaltMuRec_to_HaltL
    (MPL 2.0), as they were in the earlier VMGuestEvalL.v and SmFuel.v, so
    that this file does not need the recursive-algebra development.

    Dependencies: as TcEvalL.v. No axioms and no unfinished proofs.                    *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is recursion theory on the two-counter machine of EarnedCore.v (its
   programs, runs and the numbering of programs). The machine's link to the
   abstract record (a CertificationSystem with the trace cost floor, and a
   Thiele-complete machine) lives in EarnedCoreLinks.v and ThieleComplete.v. *)


From Undecidability.L Require Import L Tactics.LTactics Datatypes.LNat Datatypes.LOptions Util.L_facts.
From Undecidability.L Require Import Computability.MuRec.
From Undecidability.L.Util Require Import ClosedLAdmissible.
From Undecidability.MinskyMachines Require Import MMA.
From Undecidability.MinskyMachines.Reductions Require Import L_computable_to_MMA_computable.
Require Import Minimal.TcBlocks Kernel.TcCodes Kernel.TcInterp Kernel.TcEvalL.
Import L_Notations.

Definition tc_mu_option : term := (lam (0 (mu (lam (1 0 (lam (enc true)) (enc false)))) (lam 0) (lam 0))).

Lemma tc_mu_option_proc : proc tc_mu_option.
Proof.
  unfold tc_mu_option. Lproc.
Qed.
#[export] Hint Resolve tc_mu_option_proc : Lproc.

From Undecidability Require Import LOptions.

Lemma tc_mu_option_equiv {X} `{encodable X} s (b : X)  :
  proc s ->
  tc_mu_option s == s (mu (lam (s 0 (lam (enc true)) (enc false)))) (lam 0) (lam 0).
Proof.
  unfold tc_mu_option. intros Hs. now Lsimpl.
Qed.

Definition tc_mu_option_spec {X} {ENC : encodable X} {I : encInj ENC} s (b : X)  :
  proc s ->
  (forall x : X, enc x <> lam 0) ->
 (forall n : nat, exists o : option X, s (enc n) == enc o) ->
  (forall b : X, forall m n : nat, s (enc n) == enc (Some b) -> m >= n -> s (enc m) == enc (Some b)) ->
  tc_mu_option s == enc b <-> exists n : nat, s (enc n) == enc (Some b).
Proof.
  intros Hs Hinv Ht Hm.
  rewrite (@tc_mu_option_equiv X); eauto.
  split.
  - intros He.
    match goal with [He : ?s == _ |- _ ] => assert (converges s) as Hc end.
    { eexists. split. 1: exact He. Lproc. }
    eapply app_converges in Hc as [Hc _].
    eapply app_converges in Hc as [Hc _].
    eapply app_converges in Hc as [_ Hc].
    destruct Hc as [v [Hc Hv]].
    pose proof (Hc' := Hc).
    eapply mu_sound in Hc as [n [-> [Hc1 _]]]; eauto.
    * exists n.
      destruct (Ht n) as [ [x | ] Htt].
      -- rewrite Htt.
         enough (enc b == enc x) as -> % enc_extinj. 1: reflexivity.
         rewrite <- He.
         rewrite Hc'. Lsimpl. rewrite Htt. now Lsimpl.
      -- exfalso. eapply (Hinv b). eapply unique_normal_forms; try Lproc.
         rewrite <- He, Hc'. Lsimpl.
         rewrite Htt. Lsimpl. reflexivity.
    * Lproc.
    * intros n. destruct (Ht n) as [[] ];
      eexists; Lsimpl; rewrite H; Lsimpl; reflexivity.
  - intros [n Hn].
    edestruct mu_complete' with (n := n) as [n' [H' H'']].
    4: rewrite H'.
    + Lproc.
    + intros m. destruct (Ht m) as [ [] ];
      eexists; Lsimpl; rewrite H; Lsimpl; reflexivity.
    + Lsimpl. rewrite Hn. now Lsimpl.
    + destruct (Ht n') as [[] Heq]; rewrite Heq; Lsimpl.
      * enough (HH : enc (Some x) == enc (Some b))by now eapply enc_extinj in HH; inv HH.
        assert (n <= n' \/ n' <= n) as [Hl | Hl] by lia.
        -- eapply Hm in Hl; eauto. now rewrite <- Heq, Hl.
        -- eapply Hm in Hl; eauto. now rewrite <- Hn, Hl.
      * enough (false = true) by congruence.
        eapply enc_extinj. rewrite <- H''.
        symmetry. Lsimpl. rewrite Heq. now Lsimpl.
Qed.

Section Fuel2.
  Variable X : Type.
  Context {encX : encodable X}.
  Variable f : X -> nat -> nat -> nat -> option nat.
  Context {Hf : computable f}.
  Variable d : X.
  Variable mono : forall n n' x c m, f d n x c = Some m -> n <= n' -> f d n' x c = Some m.

  Lemma tc_f2_total : forall x c n : nat, exists o : option nat,
    (lam (ext f (enc d) 0 (enc x) (enc c))) (enc n) == enc o.
  Proof. intros x c n. eexists. Lsimpl. reflexivity. Qed.

  Theorem tc_L_computable_fuel2 :
    L_computable (fun (v : Vector.t nat 2) m =>
      exists n, f d n (Vector.hd v) (Vector.hd (Vector.tl v)) = Some m).
  Proof.
    exists (lam (lam (tc_mu_option (lam (ext f (enc d) 0 2 1))))).
    intros v.
    assert (Hv : v = Vector.cons nat (Vector.hd v) 1
                       (Vector.cons nat (Vector.hd (Vector.tl v)) 0 (Vector.nil nat))).
    { rewrite (Vector.eta v) at 1. rewrite (Vector.eta (Vector.tl v)) at 1.
      rewrite (Vector.nil_spec (Vector.tl (Vector.tl v))). reflexivity. }
    rewrite Hv. generalize (Vector.hd v), (Vector.hd (Vector.tl v)). clear Hv v. intros x c.
    cbn [Vector.hd Vector.tl Vector.fold_left].
    change (nat_enc x) with (enc x). change (nat_enc c) with (enc c).
    assert (Hbeta : lam (lam (tc_mu_option (lam (ext f (enc d) 0 2 1)))) (enc x) (enc c) ==
                    tc_mu_option (lam (ext f (enc d) 0 (enc x) (enc c)))) by (unfold tc_mu_option; now Lsimpl).
    assert (Hc : forall k, lam (ext f (enc d) 0 (enc x) (enc c)) (enc k) == enc (f d k x c))
      by (intro; now Lsimpl).
    split.
    - intros m. cbv beta. cbn [Vector.hd Vector.tl Vector.caseS]. rewrite L_facts.eval_iff.
      assert (lambda (nat_enc m)) as [b Hb]. { change (lambda (enc m)). Lproc. }
      rewrite Hb, eproc_equiv.
      rewrite Hbeta, <- Hb. change (nat_enc m) with (enc m).
      rewrite tc_mu_option_spec.
      + split.
        * intros [n Hn]. exists n. rewrite Hc, Hn. reflexivity.
        * intros [n Hn]. exists n. rewrite Hc in Hn. apply enc_extinj in Hn. exact Hn.
      + unfold tc_mu_option. Lproc.
      + intros []; cbv; congruence.
      + apply tc_f2_total.
      + intros b' n0 n1 Hn Hle.
        rewrite Hc in *. apply enc_extinj in Hn. rewrite (mono Hn Hle). reflexivity.
    - intros o [H1 H2] % eval_iff.
      eapply star_equiv_subrelation in H1.
      rewrite Hbeta in H1.
      unfold tc_mu_option in H1.
      match goal with [Hn : ?s == ?b |- _ ] => evar (t : term); assert (s == t) end.
      1: Lsimpl. all: subst t. 1: reflexivity.
      rewrite H in H1.
      match type of H1 with ?s == _ => assert (converges s) end.
      1: exists o; split; eassumption.
      eapply app_converges in H0 as [Hc0 _].
      eapply app_converges in Hc0 as [Hc0 _].
      eapply app_converges in Hc0 as [_ Hc0].
      destruct Hc0 as [v'' [Hc1 Hc2]].
      pose proof (Hc1' := Hc1).
      eapply mu_sound in Hc1; eauto.
      + destruct Hc1 as [m [-> []]].
        rewrite Hc1' in H1.
        destruct (f d m x c) eqn:E.
        * match type of H1 with ?s == ?b => evar (t : term); assert (s == t) end.
          1: Lsimpl. all: subst t. 1: reflexivity.
          rewrite H4, E in H1.
          match type of H1 with ?s == ?b => evar (t : term); assert (s == t) end.
          1: Lsimpl. all: subst t. 1: reflexivity.
          rewrite H5 in H1.
          eapply unique_normal_forms in H1. 2,3: Lproc.
          subst. exists n. cbn [Vector.hd Vector.tl Vector.caseS]. reflexivity.
        * enough (true = false) by congruence. eapply enc_extinj.
          rewrite <- H0. Lsimpl. now rewrite E.
      + Lproc.
      + intros n. destruct (f d n x c) eqn:EE; eexists; Lsimpl; rewrite EE; try Lsimpl; reflexivity.
  Qed.
End Fuel2.

(* The evaluator of the recursion theorem, for the transformation numbered
   t, as a relation of the input x and the number c. *)
Definition tc_Rev (t : nat) (v : Vector.t nat 2) (m : nat) : Prop :=
  exists n, tc_ev t n (Vector.hd v) (Vector.hd (Vector.tl v)) = Some m.

Theorem tc_ev_MMA : forall t, MMA_computable (tc_Rev t).
Proof.
  intro t. apply L_computable_to_MMA_computable.
  exact (@tc_L_computable_fuel2 nat _ tc_ev _ t
           (fun n n' x c m H Hle => tc_ev_mono t n n' x c m Hle H)).
Qed.

(* The universal evaluator, as a relation of the input x and the program
   number c. *)
Definition tc_Ruev (v : Vector.t nat 2) (m : nat) : Prop :=
  exists n, tc_uev n (Vector.hd v) (Vector.hd (Vector.tl v)) = Some m.

Theorem tc_uev_MMA : MMA_computable tc_Ruev.
Proof.
  apply L_computable_to_MMA_computable.
  exact (@tc_L_computable_fuel2 nat _ tc_uev2 _ 0
           (fun n n' x c m H Hle => tc_uev_mono n n' x c Hle m H)).
Qed.

Print Assumptions tc_ev_MMA.
Print Assumptions tc_uev_MMA.
