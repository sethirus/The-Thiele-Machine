(** MultiThiele2.v: the multi-register host is Thiele-complete.

    EarnedMulti.v has the small machine's instructions, versions, fact
    table, channel, trap latch and ledger, with a counter for every natural
    number instead of two. ThieleComplete.v proves the two-counter machine
    Thiele-complete. This file does the same for the machine with memory:
    the same four clauses (universal base, earned record, exact toll,
    non-vacuity), with the property language of EarnedCore.v (PZero, PEven,
    PGe n) read at registers.

    What the proof reuses. Registers 0 and 1 are the two counters of the
    reference machine; every other register is untouched by the base, so a
    base move acts on the window exactly as on the reference. The earned
    chain is read off EarnedMulti's provenance theorems the way
    ThieleComplete.v reads the two-counter machine's.

    What is proved (every result closed under the global context):

      1. The machine and its interface [ent2_mmachine, ent2_minterface].
      2. All four clauses [ent2_mmachine_complete].
      3. Every Thiele-complete consequence of ThieleComplete.v and
         EntitlementSmall.v applies to it, in particular the representation
         theorem, so a search over memory can be run on it
         (BitSearch2.v).

    Dependencies: Coq standard library, ThieleComplete.v, EarnedCore.v and
    EarnedMulti.v (and the files they require). No axioms, no Admitted.    *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Minimal.ThieleComplete.
Require Minimal.EarnedCore.
Require Minimal.EarnedMulti.
Module E := Minimal.EarnedCore.
Module M := Minimal.EarnedMulti.

(* ================================================================= *)
(* 1. The machine and its interface.                                  *)
(* ================================================================= *)

Definition ent2_mstate : Type := @M.state E.prop.
Definition ent2_minstr : Type := @M.instr E.prop.

Definition ent2_exec : ent2_mstate -> ent2_minstr -> ent2_mstate :=
  M.exec E.prop_eqb E.eval.

Definition ent2_mmachine : machine :=
  mk_machine ent2_mstate ent2_minstr ent2_exec (@M.cost E.prop) (@M.cert E.prop).

Lemma ent2_run_mmachine : forall tr s,
  run ent2_mmachine tr s = M.run E.prop_eqb E.eval tr s.
Proof. induction tr; intros; simpl; auto. Qed.

Definition ent2_idx (r : reg) : nat := match r with RA => 0 | RB => 1 end.

(* The two counters of the reference machine are registers 0 and 1. *)
Definition ent2_mcompile (i : cm_instr) : ent2_minstr :=
  match i with
  | CINC r => M.INC (ent2_idx r)
  | CDEC r j => M.DEC (ent2_idx r) j
  end.

Definition ent2_mwindow (s : ent2_mstate) : cm_conf :=
  (M.pc (M.core_of s), (M.vals (M.core_of s) 0, M.vals (M.core_of s) 1)).

(* A start with registers 0 and 1 holding a and b and every other register 0. *)
Definition ent2_vals2 (a b : nat) : nat -> nat :=
  fun r => match r with 0 => a | 1 => b | _ => 0 end.

Definition ent2_mload (a b : nat) : ent2_mstate := M.start (ent2_vals2 a b).

Lemma ent2_msim : forall (s : ent2_mstate) i, M.err (M.core_of s) = false ->
  ent2_mwindow (ent2_exec s (ent2_mcompile i)) = cm_exec i (ent2_mwindow s) /\
  M.err (M.core_of (ent2_exec s (ent2_mcompile i))) = false.
Proof.
  intros [k m r] i He. simpl in *. unfold ent2_exec, M.exec, M.cexec. simpl.
  rewrite He.
  destruct i as [[|] | [|] j]; simpl; unfold ent2_mwindow; simpl.
  - unfold M.write, M.upd. simpl. auto.
  - unfold M.write, M.upd. simpl. auto.
  - destruct (M.vals k 0) eqn:Ha; unfold M.write, M.goto, M.upd; simpl; rewrite ?Ha; auto.
  - destruct (M.vals k 1) eqn:Hb; unfold M.write, M.goto, M.upd; simpl; rewrite ?Hb; auto.
Qed.

Definition ent2_mbase : universal_base ent2_mmachine :=
  mk_ub ent2_mmachine ent2_mwindow (fun s => M.err (M.core_of s) = false)
    ent2_mcompile ent2_mload
    (fun a b => eq_refl) (fun a b => eq_refl) ent2_msim.

Definition ent2_mkind (i : ent2_minstr) : kind (E.prop * nat) :=
  match i with
  | M.CHECK p r => KCheck (p, r)
  | M.COMMIT p r => KCommit (p, r)
  | M.CERTIFY => KCertify
  | _ => KBase
  end.

(* A claim is a property and a register. It means the property holds of the
   register's value; the checker is CHECK's own test; the thing a claim is
   about is unchanged when the register's version and value are. *)
Definition ent2_minterface : thiele_interface ent2_mmachine :=
  mk_ti ent2_mmachine ent2_mbase (E.prop * nat) ent2_mkind
    (fun pr s => E.holds (fst pr) (M.vals (M.core_of s) (snd pr)))
    (fun s pr => M.check_ok E.eval (M.core_of s) (fst pr) (snd pr))
    (fun pr s t => M.vers (M.core_of s) (snd pr) = M.vers (M.core_of t) (snd pr) /\
                   M.vals (M.core_of s) (snd pr) = M.vals (M.core_of t) (snd pr))
    (@M.clean_start E.prop) (@M.mu E.prop).

(* ================================================================= *)
(* 2. The four clauses.                                               *)
(* ================================================================= *)

(* An untouched stretch leaves the register's version and value as they
   were, at every point inside it. *)
Lemma ent2_untouched_prefix : forall s mid c,
  M.untouched E.prop_eqb E.eval s mid c ->
  forall t1 t2, mid = t1 ++ t2 ->
  M.vers (M.core_of (M.run E.prop_eqb E.eval t1 s)) c = M.vers (M.core_of s) c /\
  M.vals (M.core_of (M.run E.prop_eqb E.eval t1 s)) c = M.vals (M.core_of s) c.
Proof.
  intros s mid c Hu t1. induction t1 as [| i t1 IH] using rev_ind; intros t2 Hmid;
    [simpl; auto |].
  destruct (IH (i :: t2)) as [Hv Hw]; [rewrite Hmid, <- app_assoc; reflexivity |].
  destruct (Hu t1 i t2) as [Hv' Hw']; [rewrite Hmid, <- app_assoc; reflexivity |].
  rewrite M.multi_run_snoc. unfold M.exec. simpl. rewrite Hv', Hw'. auto.
Qed.

Lemma ent2_prop_eqb_eq : forall p q, E.prop_eqb p q = true <-> p = q.
Proof.
  intros p q. split.
  - destruct p as [| | n], q as [| | m]; simpl; intro H; try discriminate; try reflexivity.
    apply Nat.eqb_eq in H. subst. reflexivity.
  - intro H. subst. destruct q; simpl; auto using Nat.eqb_refl.
Qed.

Lemma ent2_chain_same : forall s0 pre1 p c (t1 t2 : list (@M.instr E.prop)),
  M.untouched E.prop_eqb E.eval (M.run E.prop_eqb E.eval (pre1 ++ [M.CHECK p c]) s0)
    (t1 ++ t2) c ->
  M.vers (M.core_of (M.run E.prop_eqb E.eval pre1 s0)) c =
  M.vers (M.core_of (M.run E.prop_eqb E.eval (pre1 ++ M.CHECK p c :: t1) s0)) c /\
  M.vals (M.core_of (M.run E.prop_eqb E.eval pre1 s0)) c =
  M.vals (M.core_of (M.run E.prop_eqb E.eval (pre1 ++ M.CHECK p c :: t1) s0)) c.
Proof.
  intros s0 pre1 p c t1 t2 Hun.
  assert (Hr : M.run E.prop_eqb E.eval (pre1 ++ M.CHECK p c :: t1) s0
               = M.run E.prop_eqb E.eval t1
                   (M.run E.prop_eqb E.eval (pre1 ++ [M.CHECK p c]) s0)).
  { rewrite <- M.multi_run_app. f_equal. rewrite <- app_assoc. reflexivity. }
  rewrite Hr.
  destruct (ent2_untouched_prefix _ _ _ Hun t1 t2 eq_refl) as [Hv Hw].
  rewrite Hv, Hw, M.multi_run_snoc. unfold M.exec. simpl.
  rewrite M.multi_ver_check, M.multi_val_check. split; reflexivity.
Qed.

Lemma ent2_chain_holds : forall s0 tr,
  M.clean_start s0 -> M.cert (M.run E.prop_eqb E.eval tr s0) = true ->
  earned_chain ent2_minterface s0 tr.
Proof.
  intros s0 tr H0 H1. pose proof H0 as [_ [Hch Hc0]].
  destruct (M.multi_cert_first E.prop_eqb E.eval s0 tr Hc0 H1)
    as [pre [post [Htr [Hpre Hok]]]].
  pose proof Hok as Hset. unfold M.certify_ok in Hset.
  apply andb_true_iff in Hset as [_ Hset].
  destruct (M.chan (M.core_of (M.run E.prop_eqb E.eval pre s0))) as [f |] eqn:Hf;
    [| discriminate].
  destruct (M.multi_chan_origin E.prop_eqb E.eval s0 pre f Hch Hf)
    as [preC [p [c [mid2 [HpreC [Hcm _]]]]]].
  destruct (M.multi_earned_commitment_provenance E.prop_eqb ent2_prop_eqb_eq
              E.eval s0 preC p c H0 Hcm)
    as [pre1 [mid1 [Hpre1 [Hck [_ [_ [_ Hun]]]]]]].
  assert (Hlist : pre1 ++ M.CHECK p c :: mid1 ++ M.COMMIT p c :: mid2 = pre)
    by (rewrite HpreC, Hpre1; list_eq).
  exists pre1, (p, c), (M.CHECK p c), mid1, (M.COMMIT p c), mid2, M.CERTIFY, post.
  split; [rewrite Htr, <- Hlist; list_eq |].
  split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
  split; [rewrite ent2_run_mmachine; exact Hck |].
  split.
  { intros t1 t2 Hm. rewrite !ent2_run_mmachine. rewrite Hm in Hun.
    exact (ent2_chain_same _ _ _ _ _ _ Hun). }
  assert (Hl2 : pre1 ++ M.CHECK p c :: mid1 ++ M.COMMIT p c :: mid2 ++ [M.CERTIFY]
                = pre ++ [M.CERTIFY]) by (rewrite <- Hlist; list_eq).
  assert (Hup : M.cert (M.run E.prop_eqb E.eval (pre ++ [M.CERTIFY]) s0) = true)
    by (rewrite M.multi_run_snoc; unfold M.exec; simpl; rewrite Hpre; exact Hok).
  rewrite <- Hl2 in Hup. rewrite <- Hlist in Hpre.
  split; rewrite ent2_run_mmachine; assumption.
Qed.

Theorem ent2_mmachine_complete : thiele_complete_with ent2_minterface.
Proof.
  split; [| split; [| split]].
  - split; [intros [[|] | [|] j]; reflexivity |].
    split; [intros a b; apply M.multi_start_clean |]. split.
    + intros s m Hk. destruct m; simpl in Hk; try discriminate; simpl;
        unfold ent2_exec, M.exec; simpl; apply orb_false_r.
    + intros s m H. simpl in *. apply (M.multi_cert_permanent E.prop_eqb E.eval), H.
  - split; [intros s [_ [_ H]]; exact H |]. split.
    + intros s0 tr H0 H1. apply ent2_chain_holds; [exact H0 |].
      rewrite <- ent2_run_mmachine. exact H1.
    + split.
      * intros s [p c] H. simpl in *. unfold M.check_ok in H.
        apply andb_true_iff in H as [H _]. apply andb_true_iff in H as [_ H].
        apply E.eval_iff, H.
      * intros [p c] s t [_ Hw] H. simpl in *. rewrite <- Hw. exact H.
  - split; [intros []; reflexivity |].
    intros s m. simpl. unfold ent2_exec, M.exec. reflexivity.
  - exists (E.PZero, 0), (M.CHECK E.PZero 0), (M.COMMIT E.PZero 0), M.CERTIFY.
    split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
    split; [| split; [exists 0, 0; reflexivity | exists 1, 0; simpl; intro H; discriminate H]].
    intros a b. destruct a as [| a]; simpl; split; intro H;
      try reflexivity; try discriminate H.
Qed.

(* ================================================================= *)
(* Assumption audit.                                                  *)
(* ================================================================= *)

Print Assumptions ent2_prop_eqb_eq.
Print Assumptions ent2_run_mmachine.
Print Assumptions ent2_msim.
Print Assumptions ent2_untouched_prefix.
Print Assumptions ent2_chain_holds.
Print Assumptions ent2_mmachine_complete.
