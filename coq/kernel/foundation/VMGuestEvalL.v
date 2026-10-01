(** The guest evaluator in the lambda calculus L, and its Minsky machine.

    Every function of the tuple-form evaluator ([VMGuestEvalTuple]) is
    extracted to L with a correctness proof ([computable]). A fuel function
    that is monotone in its fuel defines an L-computable relation through
    unbounded minimization ([L_computable_fuel]), and the vendored
    [L_computable_to_MMA_computable] turns that into an alternate Minsky
    machine ([RD_MMA]). The extraction tactic needs MetaCoq Template; the
    resulting terms and proofs are checked by the Coq kernel. *)

From Undecidability.L Require Import Tactics.LTactics Datatypes.LNat Datatypes.LOptions Datatypes.LProd Datatypes.Lists Datatypes.LBool.
From Undecidability.L.Tactics Require Import GenEncode.
From Kernel Require Import VMEncoding VMSelfGuest VMSelfRun VMGuestEvalNat.
From Undecidability.MinskyMachines Require Import MMA.
From Undecidability.MinskyMachines.Reductions Require Import L_computable_to_MMA_computable.

MetaCoq Run (tmGenEncode "enc_GInstr" GInstr).
#[export] Hint Resolve enc_GInstr_correct : Lrewrite.

Instance term_GHalt : computable GHalt.
Proof. extract constructor. Qed.
Instance term_GLoadImm : computable GLoadImm.
Proof. extract constructor. Qed.
Instance term_GXfer : computable GXfer.
Proof. extract constructor. Qed.
Instance term_GAdd : computable GAdd.
Proof. extract constructor. Qed.
Instance term_GSub : computable GSub.
Proof. extract constructor. Qed.
Instance term_GMul : computable GMul.
Proof. extract constructor. Qed.
Instance term_GAnd : computable GAnd.
Proof. extract constructor. Qed.
Instance term_GOr : computable GOr.
Proof. extract constructor. Qed.
Instance term_GShl : computable GShl.
Proof. extract constructor. Qed.
Instance term_GShr : computable GShr.
Proof. extract constructor. Qed.
Instance term_GJump : computable GJump.
Proof. extract constructor. Qed.
Instance term_GJnez : computable GJnez.
Proof. extract constructor. Qed.
Instance term_hb : computable hb.
Proof. extract. Qed.
Instance term_bit : computable bit.
Proof. extract. Qed.
Instance term_pow2 : computable pow2.
Proof. extract. Qed.
Instance term_bnat : computable bnat.
Proof. extract. Qed.
Instance term_nbits : computable nbits.
Proof. extract. Qed.
Instance term_encode_nat : computable encode_nat.
Proof. extract. Qed.
Instance term_pun : computable pun.
Proof. extract. Qed.
Instance term_p1 : computable p1.
Proof. extract. Qed.
Instance term_pinstr : computable pinstr.
Proof. extract. Qed.
Instance term_pinstrs : computable pinstrs.
Proof. extract. Qed.
Instance term_dec_bits : computable dec_bits.
Proof. extract. Qed.
Instance term_dec : computable dec.
Proof. extract. Qed.
Instance term_gibits : computable gibits.
Proof. extract. Qed.

From Kernel Require Import VMSelfRice VMGuestExactEpilogue VMGuestEvalTuple.

Instance term_gpay : computable gpay. Proof. extract. Qed.
Instance term_gencT : computable gencT. Proof. extract. Qed.
Instance term_g_cost : computable g_cost. Proof. extract. Qed.
Instance term_nbitw : computable nbitw. Proof. extract. Qed.
Instance term_nand : computable nand. Proof. extract. Qed.
Instance term_nor : computable nor. Proof. extract. Qed.
Instance term_nshl : computable nshl. Proof. extract. Qed.
Instance term_nshr : computable nshr. Proof. extract. Qed.
Instance term_tget : computable tget. Proof. extract. Qed.
Instance term_tset : computable tset. Proof. extract. Qed.
Instance term_tnext : computable tnext. Proof. extract. Qed.
Instance term_tstep : computable tstep. Proof. extract. Qed.
Instance term_trun : computable trun. Proof. extract. Qed.
Instance term_tinput : computable tinput. Proof. extract. Qed.
Instance term_tz : computable tz. Proof. extract. Qed.
Instance term_unpair : computable unpair. Proof. extract. Qed.
Instance term_rpc : computable rpc. Proof. extract. Qed.
Instance term_reloc_i : computable reloc_i. Proof. extract. Qed.
Instance term_reloc : computable reloc. Proof. extract. Qed.
Instance term_sp_prefix : computable sp_prefix. Proof. extract. Qed.
Instance term_sp : computable sp. Proof. extract. Qed.
Instance term_epi_pow2 : computable VMGuestExactEpilogue.pow2. Proof. extract. Qed.
Instance term_tsum : computable tsum. Proof. extract. Qed.
Instance term_tbody : computable tbody. Proof. extract. Qed.
Instance term_tpack : computable tpack. Proof. extract. Qed.
Instance term_thfun : computable thfun. Proof. extract. Qed.

From Undecidability.L Require Import L Tactics.LTactics Datatypes.LNat Datatypes.LOptions Util.L_facts.
From Undecidability.L Require Import Computability.MuRec.
From Undecidability.L.Util Require Import ClosedLAdmissible.
From Kernel Require Import VMSelfGuest VMGuestEvalTuple.
Import L_Notations.

(** [mu_option] and its specification, copied unchanged from the vendored
    [Undecidability.L.Reductions.HaltMuRec_to_HaltL] (MPL 2.0) so that this
    file does not depend on the recursive-algebra development. *)
Definition mu_option : term := (lam (0 (mu (lam (1 0 (lam (enc true)) (enc false)))) (lam 0) (lam 0))).

Lemma mu_option_proc : proc mu_option.
Proof.
  unfold mu_option. Lproc.
Qed.
#[export] Hint Resolve mu_option_proc : Lproc.

From Undecidability Require Import LOptions.

Lemma mu_option_equiv {X} `{encodable X} s (b : X)  :
  proc s ->
  mu_option s == s (mu (lam (s 0 (lam (enc true)) (enc false)))) (lam 0) (lam 0).
Proof.
  unfold mu_option. intros Hs. now Lsimpl.
Qed.

Definition mu_option_spec {X} {ENC : encodable X} {I : encInj ENC} s (b : X)  :
  proc s ->
  (forall x : X, enc x <> lam 0) ->
 (forall n : nat, exists o : option X, s (enc n) == enc o) ->
  (forall b : X, forall m n : nat, s (enc n) == enc (Some b) -> m >= n -> s (enc m) == enc (Some b)) ->
  mu_option s == enc b <-> exists n : nat, s (enc n) == enc (Some b).
Proof.
  intros Hs Hinv Ht Hm.
  rewrite (@mu_option_equiv X); eauto.
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


Section Fuel.
  Variable X : Type.
  Context {encX : encodable X}.
  Variable f : X -> nat -> nat -> option nat.
  Context {Hf : computable f}.
  Variable d : X.
  Variable mono : forall n n' z m, f d n z = Some m -> n <= n' -> f d n' z = Some m.

  Lemma f_total : forall z n : nat, exists o : option nat,
    (lam (ext f (enc d) 0 (enc z))) (enc n) == enc o.
  Proof. intros z n. eexists. Lsimpl. reflexivity. Qed.

  Theorem L_computable_fuel :
    L_computable (fun (v : Vector.t nat 1) m => exists n, f d n (Vector.hd v) = Some m).
  Proof.
    exists (lam (mu_option (lam (ext f (enc d) 0 1)))).
    intros v.
    assert (Hv : v = Vector.cons nat (Vector.hd v) 0 (Vector.nil nat)).
    { rewrite (Vector.eta v) at 1. rewrite (Vector.nil_spec (Vector.tl v)). reflexivity. }
    rewrite Hv. generalize (Vector.hd v). clear Hv v. intro z.
    change (Vector.hd (Vector.cons nat z 0 (Vector.nil nat))) with z.
    cbn [Vector.fold_left].
    change (nat_enc z) with (enc z).
    assert (Hbeta : lam (mu_option (lam (ext f (enc d) 0 1))) (enc z) ==
                    mu_option (lam (ext f (enc d) 0 (enc z)))) by (unfold mu_option; now Lsimpl).
    split.
    - intros m. rewrite L_facts.eval_iff.
      assert (lambda (nat_enc m)) as [b Hb]. { change (lambda (enc m)). Lproc. }
      rewrite Hb, eproc_equiv.
      rewrite Hbeta, <- Hb. change (nat_enc m) with (enc m).
      rewrite mu_option_spec.
      + split.
        * intros [n Hn]. exists n. Lsimpl. rewrite Hn. reflexivity.
        * intros [n Hn]. exists n.
          assert (Hc : lam (ext f (enc d) 0 (enc z)) (enc n) == enc (f d n z)) by (now Lsimpl).
          rewrite Hc in Hn. apply enc_extinj in Hn. exact Hn.
      + unfold mu_option. Lproc.
      + intros []; cbv; congruence.
      + apply f_total.
      + intros b' n0 n1 Hn Hle.
        assert (Hc : forall k, lam (ext f (enc d) 0 (enc z)) (enc k) == enc (f d k z)) by (intro; now Lsimpl).
        rewrite Hc in *. apply enc_extinj in Hn. rewrite (mono Hn Hle). reflexivity.
    - intros o [H1 H2] % eval_iff.
      eapply star_equiv_subrelation in H1.
      rewrite Hbeta in H1.
      unfold mu_option in H1.
      match goal with [Hn : ?s == ?b |- _ ] => evar (t : term); assert (s == t) end.
      1: Lsimpl. all: subst t. 1: reflexivity.
      rewrite H in H1.
      match type of H1 with ?s == _ => assert (converges s) end.
      1: exists o; split; eassumption.
      eapply app_converges in H0 as [Hc _].
      eapply app_converges in Hc as [Hc _].
      eapply app_converges in Hc as [_ Hc].
      destruct Hc as [v'' [Hc1 Hc2]].
      pose proof (Hc1' := Hc1).
      eapply mu_sound in Hc1; eauto.
      + destruct Hc1 as [m [-> []]].
        rewrite Hc1' in H1.
        destruct (f d m z) eqn:E.
        * match type of H1 with ?s == ?b => evar (t : term); assert (s == t) end.
          1: Lsimpl. all: subst t. 1: reflexivity.
          rewrite H4, E in H1.
          match type of H1 with ?s == ?b => evar (t : term); assert (s == t) end.
          1: Lsimpl. all: subst t. 1: reflexivity.
          rewrite H5 in H1.
          eapply unique_normal_forms in H1. 2,3: Lproc.
          subst. exists n. reflexivity.
        * enough (true = false) by congruence. eapply enc_extinj.
          rewrite <- H0. Lsimpl. now rewrite E.
      + Lproc.
      + intros n. destruct (f d n z) eqn:EE; eexists; Lsimpl; rewrite EE; try Lsimpl; reflexivity.
  Qed.
End Fuel.

Lemma thfun_mono : forall D n n' z m,
  thfun D n z = Some m -> n <= n' -> thfun D n' z = Some m.
Proof.
  intros D n n' z m H Hle. rewrite thfun_spec in *.
  exact (hfun_mono H Hle).
Qed.

Definition RD (D : list GInstr) (v : Vector.t nat 1) (m : nat) : Prop :=
  exists n, thfun D n (Vector.hd v) = Some m.

Lemma RD_MMA : forall D, MMA_computable (RD D).
Proof.
  intro D. apply L_computable_to_MMA_computable.
  exact (@L_computable_fuel _ _ thfun _ D (fun n n' z m H Hle => @thfun_mono D n n' z m H Hle)).
Qed.

Print Assumptions L_computable_fuel.
Print Assumptions RD_MMA.
