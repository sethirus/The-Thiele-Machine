(** BitSearch2.v: an n-bit search on the multi-register host, and what its
    program does on every world.

    The old build's BitSearchEntitlement.v ran a search through a hidden
    n-bit value stored one bit per word of the VM's memory. The small
    machine's counterpart of that memory is the multi-register host of
    EarnedMulti.v, one counter per natural number, shown Thiele-complete in
    MultiThiele2.v. The hidden value sits in registers 0 to n-1, one bit per
    register. Question i asks whether register i holds the bit b: CHECK "at
    least 1" for a 1, CHECK "is 0" for a 0. The program asks k questions,
    COMMITs the claim of the first, and CERTIFYs.

    What is proved (every result closed under the global context):

      1. Lists of bits and a way to compare a candidate with a list of
         answers [ent2_agree, ent2_agree_true_iff].
      2. The program [ent2_qtrace] and the worlds [ent2_world], and what
         the program does on any world. If every answer is right and there
         are at most 16 questions, the record goes up and the ledger reads
         k + 2 [ent2_qtrace_run]; otherwise the CHECK that fails traps and
         the record stays down.
      3. A certified run asks at most 16 questions before the CERTIFY that
         raised the record: the fact table holds 16 facts, never evicts,
         and a CHECK on a full table traps [ent2_questions_cap]. This is a
         property of the machine, not of the program, and it is why the
         member in BitSearchMember2.v has k <= 16 where the VM's had
         k <= n <= 64.

    Dependencies: ThieleComplete.v, EntitlementSmall.v, MultiThiele2.v,
    EarnedCore.v and EarnedMulti.v. No axioms, no Admitted.               *)
From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Minimal.ThieleComplete.
Require Import Minimal.EntitlementSmall.
Require Import Minimal.MultiThiele2.
Require Minimal.EarnedCore.
Require Minimal.EarnedMulti.
Module E := Minimal.EarnedCore.
Module M := Minimal.EarnedMulti.

Local Notation mrun := (M.run E.prop_eqb E.eval).
Local Notation mexec := (M.exec E.prop_eqb E.eval).
Local Notation mstate := (@M.state E.prop).
Local Notation minstr := (@M.instr E.prop).

(* ================================================================= *)
(* 1. Lists of bits.                                                  *)
(* ================================================================= *)

Lemma ent2_in_all_bits : forall n x, In x (ent_all_bools n) <-> length x = n.
Proof.
  induction n as [| n IH]; intro x; simpl.
  - split; intro H.
    + destruct H as [<- | []]. reflexivity.
    + destruct x; [left; reflexivity | discriminate].
  - split; intro H.
    + apply in_app_iff in H as [H | H]; apply in_map_iff in H as [y [<- Hy]];
        simpl; f_equal; apply IH, Hy.
    + destruct x as [| b x]; [discriminate |]. simpl in H. injection H as H.
      apply in_app_iff. destruct b; [left | right]; apply in_map, IH, H.
Qed.

(* How a candidate agrees with a list of answers, bit by bit. A candidate
   too short to have the bit counts as mismatching. *)
Fixpoint ent2_agree (ans x : list bool) : list bool :=
  match ans, x with
  | [], _ => []
  | _ :: u, [] => false :: ent2_agree u []
  | a :: u, b :: v => Bool.eqb a b :: ent2_agree u v
  end.

Lemma ent2_agree_length : forall ans x, length (ent2_agree ans x) = length ans.
Proof.
  induction ans as [| a u IH]; intros [| b v]; simpl; auto.
Qed.

Lemma ent2_agree_app : forall ans u, ent2_agree ans (ans ++ u) = map (fun _ => true) ans.
Proof.
  induction ans as [| a ans IH]; intro u; simpl; [reflexivity |].
  rewrite Bool.eqb_reflx, IH. reflexivity.
Qed.

Lemma ent2_agree_flip : forall ans u,
  ent2_agree ans (map negb ans ++ u) = map (fun _ => false) ans.
Proof.
  induction ans as [| a ans IH]; intro u; simpl; [reflexivity |].
  rewrite IH. destruct a; reflexivity.
Qed.

Lemma ent2_agree_true_iff : forall ans x,
  forallb (fun b => b) (ent2_agree ans x) = true <-> exists u, x = ans ++ u.
Proof.
  induction ans as [| a ans IH]; intro x; simpl.
  - split; intros _; [exists x; reflexivity | reflexivity].
  - destruct x as [| b x].
    + split; intro H; [discriminate H |]. destruct H as [u H]. discriminate H.
    + simpl. rewrite andb_true_iff, Bool.eqb_true_iff, IH. split.
      * intros [<- [u ->]]. exists u. reflexivity.
      * intros [u H]. injection H as <- H. split; [reflexivity | exists u; exact H].
Qed.

(* ================================================================= *)
(* 2. The program and the worlds.                                     *)
(* ================================================================= *)

(* Question i asks whether register i holds the bit b: "at least 1" for a
   1, "is 0" for a 0. *)
Definition ent2_prop (b : bool) : E.prop := if b then E.PGe 1 else E.PZero.

Fixpoint ent2_checks (ans : list bool) (i0 : nat) : list minstr :=
  match ans with
  | [] => []
  | b :: r => M.CHECK (ent2_prop b) i0 :: ent2_checks r (S i0)
  end.

(* The program: ask every question, commit the claim of the first, certify. *)
Definition ent2_qtrace (ans : list bool) : list minstr :=
  ent2_checks ans 0 ++ [M.COMMIT (ent2_prop (hd false ans)) 0; M.CERTIFY].

(* The world whose hidden value is v: register i holds bit i of v, and every
   register past the end holds 0. *)
Definition ent2_vals (v : list bool) : nat -> nat := fun i => Nat.b2n (nth i v false).
Definition ent2_world (v : list bool) : mstate := M.start (ent2_vals v).

Lemma ent2_eval_prop : forall b x, E.eval (ent2_prop b) (Nat.b2n x) = Bool.eqb b x.
Proof. intros [|] [|]; reflexivity. Qed.

(* Whether every question's answer is right, read off the registers. *)
Fixpoint ent2_okb (ans : list bool) (i0 : nat) (vs : nat -> nat) : bool :=
  match ans with
  | [] => true
  | b :: r => E.eval (ent2_prop b) (vs i0) && ent2_okb r (S i0) vs
  end.

Lemma ent2_skipn_cons : forall (v : list bool) i,
  i < length v -> skipn i v = nth i v false :: skipn (S i) v.
Proof.
  induction v as [| a v IH]; intros [| i] H; simpl in *; try lia; [reflexivity |].
  apply IH. lia.
Qed.

Lemma ent2_okb_world : forall ans i0 v,
  i0 + length ans <= length v ->
  ent2_okb ans i0 (ent2_vals v) = forallb (fun b => b) (ent2_agree ans (skipn i0 v)).
Proof.
  induction ans as [| b r IH]; intros i0 v H; simpl in *; [reflexivity |].
  rewrite (ent2_skipn_cons v i0 ltac:(lia)). simpl.
  unfold ent2_vals at 1. rewrite ent2_eval_prop. f_equal. apply IH. lia.
Qed.

(* ================================================================= *)
(* 3. What the program does on a world.                               *)
(* ================================================================= *)

(* A trapped machine stays trapped and its flag stays as it was. *)
Lemma ent2_trapped_run : forall tr (s : mstate), M.err (M.core_of s) = true ->
  M.err (M.core_of (mrun tr s)) = true /\ M.cert (mrun tr s) = M.cert s.
Proof.
  induction tr as [| i tr IH]; intros s H; simpl; [auto |].
  assert (Hc : M.certify_ok (M.core_of s) = false)
    by (unfold M.certify_ok; rewrite H; reflexivity).
  assert (Hs : M.err (M.core_of (mexec s i)) = true /\ M.cert (mexec s i) = M.cert s).
  { unfold M.exec. simpl. rewrite (M.multi_cexec_trapped E.prop_eqb E.eval _ _ H).
    split; [exact H |].
    destruct i; unfold M.fires; rewrite ?Hc; apply orb_false_r. }
  destruct Hs as [Hs1 Hs2]. destruct (IH _ Hs1) as [H1 H2]. split; [exact H1 |].
  rewrite H2, Hs2. reflexivity.
Qed.

Lemma ent2_checks_pass : forall ans i0 (s : mstate),
  M.err (M.core_of s) = false ->
  ent2_okb ans i0 (M.vals (M.core_of s)) = true ->
  length (M.facts (M.core_of s)) + length ans <= 16 ->
  M.err (M.core_of (mrun (ent2_checks ans i0) s)) = false /\
  M.vals (M.core_of (mrun (ent2_checks ans i0) s)) = M.vals (M.core_of s) /\
  M.vers (M.core_of (mrun (ent2_checks ans i0) s)) = M.vers (M.core_of s) /\
  M.cert (mrun (ent2_checks ans i0) s) = M.cert s /\
  M.chan (M.core_of (mrun (ent2_checks ans i0) s)) = M.chan (M.core_of s) /\
  M.mu (mrun (ent2_checks ans i0) s) = M.mu s + length ans /\
  exists new : list (@M.fact E.prop),
    M.facts (M.core_of (mrun (ent2_checks ans i0) s)) = new ++ M.facts (M.core_of s) /\
    length new = length ans /\
    forall j, j < length ans ->
      In (M.mkfact (ent2_prop (nth j ans false)) (i0 + j) (M.vers (M.core_of s) (i0 + j))) new.
Proof.
  induction ans as [| b rest IH]; intros i0 s He Hok Hroom.
  - simpl. split; [exact He |]. split; [reflexivity |]. split; [reflexivity |].
    split; [reflexivity |]. split; [reflexivity |]. split; [lia |].
    exists []. simpl. split; [reflexivity |]. split; [reflexivity |]. intros j Hj. lia.
  - simpl in Hok. apply andb_true_iff in Hok as [Hev Hrest].
    simpl in Hroom.
    assert (Hck : M.check_ok E.eval (M.core_of s) (ent2_prop b) i0 = true).
    { unfold M.check_ok. rewrite He, Hev. simpl. apply Nat.ltb_lt. unfold M.fact_cap. lia. }
    pose proof (M.multi_exec_check_pass E.prop_eqb E.eval s (ent2_prop b) i0 Hck) as Hex.
    cbn [ent2_checks mrun]. rewrite Hex.
    set (s1 := M.mkst (M.record_fact (M.core_of s) (M.claim (M.core_of s) (ent2_prop b) i0))
                      (M.mu s + 1) (M.cert s)).
    assert (Hs1e : M.err (M.core_of s1) = false) by (exact He).
    assert (Hs1v : M.vals (M.core_of s1) = M.vals (M.core_of s)) by reflexivity.
    assert (Hs1r : M.vers (M.core_of s1) = M.vers (M.core_of s)) by reflexivity.
    assert (Hs1c : M.chan (M.core_of s1) = M.chan (M.core_of s)) by reflexivity.
    assert (Hs1f : M.facts (M.core_of s1) = M.claim (M.core_of s) (ent2_prop b) i0 :: M.facts (M.core_of s))
      by reflexivity.
    assert (Hs1m : M.mu s1 = M.mu s + 1) by reflexivity.
    assert (Hs1t : M.cert s1 = M.cert s) by reflexivity.
    destruct (IH (S i0) s1 Hs1e) as [H1 [H2 [H3 [H4 [H5 [H6 [new [H7 [H8 H9]]]]]]]]].
    + rewrite Hs1v. exact Hrest.
    + rewrite Hs1f. simpl. lia.
    + refine (conj H1 (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
      * rewrite H2, Hs1v. reflexivity.
      * rewrite H3, Hs1r. reflexivity.
      * rewrite H4, Hs1t. reflexivity.
      * rewrite H5, Hs1c. reflexivity.
      * rewrite H6, Hs1m. simpl. lia.
      * exists (new ++ [M.claim (M.core_of s) (ent2_prop b) i0]).
        split; [rewrite H7, Hs1f; simpl; rewrite <- app_assoc; reflexivity |].
        split; [rewrite app_length; simpl; lia |].
        intros j Hj. destruct j as [| j].
        -- apply in_app_iff. right. left. simpl. rewrite Nat.add_0_r. unfold M.claim. reflexivity.
        -- apply in_app_iff. left. simpl in Hj.
           specialize (H9 j ltac:(lia)). rewrite Hs1r in H9.
           replace (i0 + S j) with (S i0 + j) by lia. exact H9.
Qed.

Lemma ent2_checks_fail : forall ans i0 (s : mstate),
  M.err (M.core_of s) = false ->
  length (M.facts (M.core_of s)) <= 16 ->
  ~ (ent2_okb ans i0 (M.vals (M.core_of s)) = true /\
     length (M.facts (M.core_of s)) + length ans <= 16) ->
  M.err (M.core_of (mrun (ent2_checks ans i0) s)) = true /\
  M.cert (mrun (ent2_checks ans i0) s) = M.cert s.
Proof.
  induction ans as [| b rest IH]; intros i0 s He Hcap Hn.
  - exfalso. apply Hn. simpl. split; [reflexivity | lia].
  - cbn [ent2_checks mrun].
    destruct (M.check_ok E.eval (M.core_of s) (ent2_prop b) i0) eqn:Hck.
    + pose proof (M.multi_exec_check_pass E.prop_eqb E.eval s (ent2_prop b) i0 Hck) as Hex.
      assert (Hl : length (M.facts (M.core_of s)) < 16).
      { unfold M.check_ok in Hck. apply andb_true_iff in Hck as [_ Hck].
        apply Nat.ltb_lt in Hck. unfold M.fact_cap in Hck. exact Hck. }
      assert (Hev : E.eval (ent2_prop b) (M.vals (M.core_of s) i0) = true).
      { unfold M.check_ok in Hck. apply andb_true_iff in Hck as [Hck _].
        apply andb_true_iff in Hck as [_ Hck]. exact Hck. }
      rewrite Hex.
      refine (IH (S i0) (M.mkst (M.record_fact (M.core_of s) (M.claim (M.core_of s) (ent2_prop b) i0)) (M.mu s + 1) (M.cert s)) _ _ _).
      * simpl. exact He.
      * simpl. lia.
      * simpl. intros [H1 H2]. apply Hn. split.
        -- simpl. rewrite Hev. exact H1.
        -- simpl. lia.
    + pose proof (M.multi_exec_check_fail E.prop_eqb E.eval s (ent2_prop b) i0 He Hck) as Hex.
      rewrite Hex. destruct (ent2_trapped_run (ent2_checks rest (S i0))
        (M.mkst (M.trap (M.core_of s)) (M.mu s + 1) (M.cert s))) as [H1 H2];
        [reflexivity |]. split; [exact H1 | exact H2].
Qed.

Lemma ent2_qtrace_run : forall ans v, ans <> [] ->
  (ent2_okb ans 0 (ent2_vals v) = true /\ length ans <= 16 ->
     M.cert (mrun (ent2_qtrace ans) (ent2_world v)) = true /\
     M.mu (mrun (ent2_qtrace ans) (ent2_world v)) = length ans + 2 /\
     M.err (M.core_of (mrun (ent2_qtrace ans) (ent2_world v))) = false) /\
  (~ (ent2_okb ans 0 (ent2_vals v) = true /\ length ans <= 16) ->
     M.cert (mrun (ent2_qtrace ans) (ent2_world v)) = false).
Proof.
  intros ans v Hne. unfold ent2_qtrace. rewrite M.multi_run_app.
  set (s0 := ent2_world v).
  assert (He0 : M.err (M.core_of s0) = false) by reflexivity.
  assert (Hf0 : M.facts (M.core_of s0) = []) by reflexivity.
  assert (Hv0 : M.vals (M.core_of s0) = ent2_vals v) by reflexivity.
  assert (Hr0 : M.vers (M.core_of s0) = fun _ => 0) by reflexivity.
  assert (Hc0 : M.cert s0 = false) by reflexivity.
  assert (Hch0 : M.chan (M.core_of s0) = None) by reflexivity.
  assert (Hm0 : M.mu s0 = 0) by reflexivity.
  split.
  - intros [Hok Hle].
    destruct (ent2_checks_pass ans 0 s0 He0) as [H1 [H2 [H3 [H4 [H5 [H6 [new [H7 [H8 H9]]]]]]]]].
    + rewrite Hv0. exact Hok.
    + rewrite Hf0. simpl. lia.
    + set (s1 := mrun (ent2_checks ans 0) s0) in *.
      destruct ans as [| b rest]; [congruence |].
      assert (Hin : In (M.claim (M.core_of s1) (ent2_prop b) 0) (M.facts (M.core_of s1))).
      { rewrite H7. apply in_app_iff. left.
        specialize (H9 0 ltac:(simpl; lia)). simpl in H9.
        unfold M.claim. rewrite H3. exact H9. }
      assert (Hcm : M.commit_ok E.prop_eqb (M.core_of s1) (ent2_prop b) 0 = true).
      { apply (M.multi_commit_ok_iff E.prop_eqb ent2_prop_eqb_eq). split; assumption. }
      pose proof (M.multi_exec_commit_pass E.prop_eqb ent2_prop_eqb_eq E.eval s1 (ent2_prop b) 0 Hcm)
        as Hex.
      set (s2 := M.mkst (M.commit_to (M.core_of s1) (M.claim (M.core_of s1) (ent2_prop b) 0))
                        (M.mu s1 + 1) (M.cert s1)).
      assert (Hcf : M.certify_ok (M.core_of s2) = true).
      { unfold M.certify_ok. simpl. rewrite H1. reflexivity. }
      pose proof (M.multi_exec_certify_pass E.prop_eqb E.eval s2 Hcf) as Hex2.
      cbn [mrun hd]. rewrite Hex. fold s2. rewrite Hex2. simpl.
      split; [reflexivity |]. split; [| exact H1].
      rewrite H6, Hm0. simpl. lia.
  - intros Hn.
    destruct (ent2_checks_fail ans 0 s0 He0) as [H1 H2].
    + rewrite Hf0. simpl. lia.
    + rewrite Hv0, Hf0. simpl in *. exact Hn.
    + destruct (ent2_trapped_run [M.COMMIT (ent2_prop (hd false ans)) 0; M.CERTIFY]
                  (mrun (ent2_checks ans 0) s0) H1) as [H3 H4].
      rewrite H4, H2. reflexivity.
Qed.

(* ================================================================= *)
(* 4. A certified run asks at most 16 questions.                      *)
(* ================================================================= *)

Fixpoint ent2_count_checks (tr : list minstr) : nat :=
  match tr with
  | [] => 0
  | i :: r => (match i with M.CHECK _ _ => 1 | _ => 0 end) + ent2_count_checks r
  end.

Lemma ent2_err_back : forall tr (s : mstate),
  M.err (M.core_of (mrun tr s)) = false -> M.err (M.core_of s) = false.
Proof.
  intros tr s H. destruct (M.err (M.core_of s)) eqn:E; [| reflexivity].
  destruct (ent2_trapped_run tr s E) as [H1 _]. congruence.
Qed.

Lemma ent2_facts_le : forall tr (s : mstate),
  length (M.facts (M.core_of s)) <= 16 -> length (M.facts (M.core_of (mrun tr s))) <= 16.
Proof.
  induction tr as [| i tr IH]; intros s H; simpl; [exact H |].
  apply IH. unfold M.exec. simpl.
  exact (M.multi_facts_bounded_step E.prop_eqb E.eval _ i H).
Qed.

Lemma ent2_facts_count : forall tr (s : mstate),
  M.err (M.core_of (mrun tr s)) = false ->
  length (M.facts (M.core_of (mrun tr s))) = length (M.facts (M.core_of s)) + ent2_count_checks tr.
Proof.
  induction tr as [| i tr IH]; intros s H; simpl in *; [lia |].
  pose proof (ent2_err_back _ _ H) as Hs1.
  pose proof (ent2_err_back tr s) as _.
  assert (Hs : M.err (M.core_of s) = false).
  { destruct (M.err (M.core_of s)) eqn:E; [| reflexivity].
    assert (Hx : M.err (M.core_of (mexec s i)) = true).
    { unfold M.exec. simpl. rewrite (M.multi_cexec_trapped E.prop_eqb E.eval _ _ E). exact E. }
    congruence. }
  rewrite (IH _ H).
  unfold M.exec. simpl.
  destruct i as [d | d j | | p d | p d |]; unfold M.cexec; rewrite Hs; try reflexivity.
  - destruct (M.vals (M.core_of s) d); reflexivity.
  - destruct (M.check_ok E.eval (M.core_of s) p d) eqn:Hck; simpl; [lia |].
    exfalso. simpl in Hs1. unfold M.exec in Hs1. simpl in Hs1. unfold M.cexec in Hs1.
    rewrite Hs, Hck in Hs1. simpl in Hs1. congruence.
  - destruct (M.commit_ok E.prop_eqb (M.core_of s) p d); reflexivity.
  - destruct (M.certify_ok (M.core_of s)); reflexivity.
Qed.

(* A run from a clean start that raises the record asked at most 16
   questions before the CERTIFY that raised it: the fact table holds 16
   facts and never evicts, and a CHECK on a full table traps. *)
Theorem ent2_questions_cap : forall (s0 : mstate) tr,
  M.clean_start s0 -> M.cert (mrun tr s0) = true ->
  exists pre post, tr = pre ++ M.CERTIFY :: post /\ ent2_count_checks pre <= 16.
Proof.
  intros s0 tr H0 H1. pose proof H0 as [Hf [_ Hc0]].
  destruct (M.multi_cert_first E.prop_eqb E.eval s0 tr Hc0 H1) as [pre [post [Htr [_ Hok]]]].
  exists pre, post. split; [exact Htr |].
  assert (He : M.err (M.core_of (mrun pre s0)) = false).
  { unfold M.certify_ok in Hok. apply andb_true_iff in Hok as [Hok _].
    apply negb_true_iff in Hok. exact Hok. }
  pose proof (ent2_facts_le pre s0 ltac:(rewrite Hf; simpl; lia)) as Hle.
  pose proof (ent2_facts_count pre s0 He) as Hc. rewrite Hf in Hc. simpl in Hc. lia.
Qed.

(* ================================================================= *)
(* Assumption audit.                                                  *)
(* ================================================================= *)
Print Assumptions ent2_in_all_bits.
Print Assumptions ent2_agree_true_iff.
Print Assumptions ent2_okb_world.
Print Assumptions ent2_trapped_run.
Print Assumptions ent2_checks_pass.
Print Assumptions ent2_checks_fail.
Print Assumptions ent2_qtrace_run.
Print Assumptions ent2_questions_cap.
