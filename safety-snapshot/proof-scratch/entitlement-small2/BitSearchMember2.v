(** BitSearchMember2.v: the n-bit search entitlement, on every Thiele-complete
    reading of the multi-register host.

    The member. A hidden value of n = k + m bits, one bit per register. The
    program of BitSearch2.v asks k questions, one per bit of the first k,
    commits the first claim and certifies. The prior is every n-bit value.
    The posterior is the 2^m values that begin with the answers. The tree is
    the complete tree of depth k; each survivor's fibre is the 2^k values
    that share its unasked bits.

    What is proved (every result closed under the global context):

      1. The posterior is exactly the set of rivals from which the program
         raises the record [ent2_search_certifies_iff,
         ent2_search_posterior_is_certified]. With more than 16 questions
         no start raises it [ent2_no_search_past_16].
      2. The structural-entitlement representation theorem applies, with
         every hypothesis a theorem [ent2_bit_search]: a strictly stronger
         test, the earned chain, index bits exactly k, record moves and
         ledger rise exactly k + 2, and the bound met with two to spare (the
         COMMIT and the CERTIFY). The 15-field shortcut record is inhabited
         [ent2_search_shortcut] and lands in the bound [ent2_search_lands].
      3. A floor with no supplied tree [ent2_search_questions_floor]. The
         questions are the claims the program's own CHECK moves asked.
         Asked of every world, they split the prior into classes of at most
         2^m, so the index-bit drop from 2^(k+m) to 2^m is at most the number
         of CHECK moves, which here is exactly k. The tree is not supplied;
         it is the run's own questions.

    Limits. The prior, posterior and fibres of item 2 are supplied; item 1
    ties the lists to the run in this member. The covering prices the size
    of the drop, not its reason. The number of questions is capped at 16 by
    the machine's fact table.

    Dependencies: ThieleComplete.v, EntitlementSmall.v, MultiThiele2.v,
    BitSearch2.v. No axioms, no Admitted.                                 *)
From Coq Require Import List Arith Lia Bool.
From Coq Require Import Logic.FinFun.
Import ListNotations.
Require Import Minimal.ThieleComplete.
Require Import Minimal.EntitlementSmall.
Require Import Minimal.MultiThiele2.
Require Import Minimal.BitSearch2.
Require Minimal.EarnedCore.
Require Minimal.EarnedMulti.
Module E := Minimal.EarnedCore.
Module M := Minimal.EarnedMulti.

Local Notation mrun := (M.run E.prop_eqb E.eval).
Local Notation mstate := (@M.state E.prop).
Local Notation minstr := (@M.instr E.prop).

(* ================================================================= *)
(* 1. The receipts.                                                   *)
(* ================================================================= *)

Definition ent2_is_check (i : minstr) : bool :=
  match i with M.CHECK _ _ => true | _ => false end.

(* The decoder reads the receipts: one "passed" per CHECK in them. *)
Definition ent2_decode (tr : list minstr) : list bool :=
  map (fun _ => true) (filter ent2_is_check tr).

Lemma ent2_checks_length : forall ans i0, length (ent2_checks ans i0) = length ans.
Proof. induction ans; intro i0; simpl; [reflexivity | rewrite IHans; reflexivity]. Qed.

Lemma ent2_filter_checks : forall ans i0,
  filter ent2_is_check (ent2_checks ans i0) = ent2_checks ans i0.
Proof. induction ans as [| b r IH]; intro i0; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma ent2_map_true : forall (l : list minstr) (ans : list bool),
  length l = length ans -> map (fun _ => true) l = map (fun _ => true) ans.
Proof.
  induction l as [| a l IH]; intros [| b r] H; simpl in *; try discriminate; [reflexivity |].
  rewrite (IH r) by lia. reflexivity.
Qed.

Lemma ent2_decode_qtrace : forall ans,
  ent2_decode (ent2_qtrace ans) = map (fun _ => true) ans.
Proof.
  intro ans. unfold ent2_decode, ent2_qtrace. rewrite filter_app, ent2_filter_checks.
  simpl. rewrite app_nil_r. apply ent2_map_true, ent2_checks_length.
Qed.

(* The record moves of the program: one per question, the COMMIT, the
   CERTIFY. *)
Lemma ent2_record_moves_checks : forall ans i0,
  record_moves ent2_minterface (ent2_checks ans i0) = length ans.
Proof.
  induction ans as [| b r IH]; intro i0; simpl; [reflexivity |].
  rewrite IH. reflexivity.
Qed.

Lemma ent2_record_moves_qtrace : forall ans,
  record_moves ent2_minterface (ent2_qtrace ans) = length ans + 2.
Proof.
  intro ans. unfold ent2_qtrace.
  rewrite record_moves_app, ent2_record_moves_checks. simpl. lia.
Qed.

(* ================================================================= *)
(* 2. The lists.                                                      *)
(* ================================================================= *)

Lemma ent2_sum_const : forall {A : Type} (f : A -> nat) c (l : list A),
  (forall x, In x l -> f x = c) -> fold_right Nat.add 0 (map f l) = length l * c.
Proof.
  intros A f c l. induction l as [| x l IH]; intro H; simpl; [reflexivity |].
  rewrite (H x (or_introl eq_refl)), IH by (intros y Hy; apply H; right; exact Hy). lia.
Qed.

(* Every n-bit value. *)
Definition ent2_prior (n : nat) : list (list bool) := ent_all_bools n.

(* The posterior: the values that begin with the answers, with m bits left. *)
Definition ent2_post (ans : list bool) (m : nat) : list (list bool) :=
  map (fun u => ans ++ u) (ent_all_bools m).

(* The fibre of a survivor: the 2^k values with its unasked bits. *)
Definition ent2_fibre (k : nat) (t : list bool) : list (list bool) :=
  map (fun w => w ++ skipn k t) (ent_all_bools k).

Lemma ent2_prior_length : forall n, length (ent2_prior n) = 2 ^ n.
Proof. exact ent_all_bools_length. Qed.

Lemma ent2_post_length : forall ans m, length (ent2_post ans m) = 2 ^ m.
Proof. intros. unfold ent2_post. rewrite map_length. apply ent_all_bools_length. Qed.

Lemma ent2_in_post : forall ans m t,
  In t (ent2_post ans m) <-> exists u, length u = m /\ t = ans ++ u.
Proof.
  intros ans m t. unfold ent2_post. rewrite in_map_iff. split.
  - intros [u [<- Hu]]. exists u. split; [apply ent2_in_all_bits, Hu | reflexivity].
  - intros [u [Hu ->]]. exists u. split; [reflexivity | apply ent2_in_all_bits, Hu].
Qed.

Lemma ent2_post_incl : forall ans m, incl (ent2_post ans m) (ent2_prior (length ans + m)).
Proof.
  intros ans m t Ht. apply ent2_in_post in Ht as [u [Hu ->]].
  unfold ent2_prior. apply ent2_in_all_bits. rewrite app_length. lia.
Qed.

Lemma ent2_skipn_app_len : forall (ans u : list bool), skipn (length ans) (ans ++ u) = u.
Proof. intros ans u. rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity. Qed.

Lemma ent2_reduction : forall ans m,
  ent_reduction (fun x => skipn (length ans) x) (ent_complete (length ans))
    (ent2_prior (length ans + m)) (ent2_post ans m).
Proof.
  intros ans m. exists (ent2_fibre (length ans)). split; [| split].
  - intros x Hx. unfold ent2_prior in Hx. apply ent2_in_all_bits in Hx.
    exists (ans ++ skipn (length ans) x). split.
    + apply ent2_in_post. exists (skipn (length ans) x). split; [| reflexivity].
      rewrite skipn_length. lia.
    + split.
      * unfold ent2_fibre. apply in_map_iff. exists (firstn (length ans) x). split.
        -- rewrite ent2_skipn_app_len. apply firstn_skipn.
        -- apply ent2_in_all_bits. rewrite firstn_length. lia.
      * rewrite ent2_skipn_app_len. reflexivity.
  - rewrite ent2_prior_length.
    rewrite (ent2_sum_const _ (2 ^ length ans)).
    + rewrite ent2_post_length. rewrite <- Nat.pow_add_r. rewrite Nat.add_comm. lia.
    + intros t _. unfold ent2_fibre. rewrite map_length. apply ent_all_bools_length.
  - intros t _. unfold ent2_fibre. rewrite map_length, ent_all_bools_length,
      ent_complete_leaves. lia.
Qed.

(* A rival that fails the first question differently from every survivor. *)
Definition ent2_rival (ans : list bool) (m : nat) : list bool :=
  map negb ans ++ repeat false m.

Lemma ent2_forallb_false : forall (a : bool) (r : list bool),
  forallb (fun b => b) (map (fun _ => false) (a :: r)) = false.
Proof. intros a r. reflexivity. Qed.

Lemma ent2_witness : forall ans m, ans <> [] ->
  In (ent2_rival ans m) (ent2_prior (length ans + m)) /\
  ~ In (ent2_rival ans m) (ent2_post ans m) /\
  ent_distinguishes (ent2_agree ans) (ent2_rival ans m) (ent2_post ans m).
Proof.
  intros ans m Hne. destruct ans as [| a r]; [congruence |].
  split; [| split].
  - unfold ent2_prior. apply ent2_in_all_bits. unfold ent2_rival.
    rewrite app_length, map_length, repeat_length. reflexivity.
  - intro H. apply ent2_in_post in H as [u [_ Hu]].
    assert (Hag : forallb (fun b => b) (ent2_agree (a :: r) (ent2_rival (a :: r) m)) = true).
    { apply ent2_agree_true_iff. exists u. exact Hu. }
    unfold ent2_rival in Hag. rewrite ent2_agree_flip in Hag.
    rewrite ent2_forallb_false in Hag. discriminate.
  - intros t Ht Heq. apply ent2_in_post in Ht as [u [_ ->]].
    unfold ent2_rival in Heq. rewrite ent2_agree_flip, ent2_agree_app in Heq.
    simpl in Heq. discriminate Heq.
Qed.

Lemma ent2_narrowing : forall ans m, ans <> [] ->
  ent_strict_sublist (ent2_post ans m) (ent2_prior (length ans + m)).
Proof.
  intros ans m Hne. split; [apply ent2_post_incl |].
  destruct (ent2_witness ans m Hne) as [H1 [H2 _]]. exists (ent2_rival ans m). auto.
Qed.

(* ================================================================= *)
(* 3. The run on the honest world.                                    *)
(* ================================================================= *)

Lemma ent2_okb_prefix : forall ans u, ent2_okb ans 0 (ent2_vals (ans ++ u)) = true.
Proof.
  intros ans u. rewrite ent2_okb_world by (rewrite app_length; lia).
  simpl. apply ent2_agree_true_iff. exists u. reflexivity.
Qed.

Lemma ent2_okb_iff : forall ans v, length ans <= length v ->
  ent2_okb ans 0 (ent2_vals v) = true <-> exists u, v = ans ++ u.
Proof.
  intros ans v H. rewrite ent2_okb_world by lia. simpl. apply ent2_agree_true_iff.
Qed.

(* The program raises the record from the world of v exactly when v begins
   with the answers (and there are at most 16 questions). *)
Theorem ent2_search_certifies_iff : forall ans v, ans <> [] -> length ans <= length v ->
  M.cert (mrun (ent2_qtrace ans) (ent2_world v)) = true <->
  (length ans <= 16 /\ exists u, v = ans ++ u).
Proof.
  intros ans v Hne Hlen. destruct (ent2_qtrace_run ans v Hne) as [Hp Hf]. split.
  - intro H. destruct (le_dec (length ans) 16) as [Hl | Hl].
    + split; [exact Hl |]. apply (ent2_okb_iff ans v Hlen).
      destruct (ent2_okb ans 0 (ent2_vals v)) eqn:Hok; [reflexivity |].
      exfalso.
      assert (Hn : ~ (false = true /\ length ans <= 16))
        by (intros [H1 _]; discriminate).
      rewrite (Hf Hn) in H. discriminate.
    + exfalso.
      assert (Hn : ~ (ent2_okb ans 0 (ent2_vals v) = true /\ length ans <= 16))
        by (intros [_ H1]; exact (Hl H1)).
      rewrite (Hf Hn) in H. discriminate.
  - intros [Hl Hu]. apply (proj1 (Hp (conj (proj2 (ent2_okb_iff ans v Hlen) Hu) Hl))).
Qed.

(* The posterior is exactly the set of rivals from which the program
   raises the record. *)
Theorem ent2_search_posterior_is_certified : forall ans m, ans <> [] -> length ans <= 16 ->
  forall v, In v (ent2_prior (length ans + m)) ->
    (In v (ent2_post ans m) <-> M.cert (mrun (ent2_qtrace ans) (ent2_world v)) = true).
Proof.
  intros ans m Hne Hle v Hv. unfold ent2_prior in Hv. apply ent2_in_all_bits in Hv.
  assert (Hlen : length ans <= length v) by lia.
  rewrite (ent2_search_certifies_iff ans v Hne Hlen). rewrite ent2_in_post. split.
  - intros [u [_ ->]]. split; [exact Hle | exists u; reflexivity].
  - intros [_ [u Hu]]. exists u. split; [| exact Hu].
    rewrite Hu, app_length in Hv. lia.
Qed.

(* A search of more than 16 questions never raises the record. *)
Theorem ent2_no_search_past_16 : forall ans v, ans <> [] -> 16 < length ans ->
  M.cert (mrun (ent2_qtrace ans) (ent2_world v)) = false.
Proof.
  intros ans v Hne Hl. destruct (ent2_qtrace_run ans v Hne) as [_ Hf]. apply Hf.
  intros [_ H]. lia.
Qed.

Lemma ent2_member_certified : forall ans u, ans <> [] -> length ans <= 16 ->
  ent_certified ent2_minterface (ent2_world (ans ++ u)) (ent2_qtrace ans) ent2_decode
    (ent_member ent_bools_eqb (ent2_agree ans) (ent2_post ans (length u))).
Proof.
  intros ans u Hne Hle. split.
  - change (M.cert (run ent2_mmachine (ent2_qtrace ans) (ent2_world (ans ++ u))) = true).
    rewrite ent2_run_mmachine.
    destruct (ent2_qtrace_run ans (ans ++ u) Hne) as [Hp _].
    exact (proj1 (Hp (conj (ent2_okb_prefix ans u) Hle))).
  - unfold ent_member. apply existsb_exists.
    exists (ans ++ repeat false (length u)). split.
    + apply ent2_in_post. exists (repeat false (length u)). split; [apply repeat_length | reflexivity].
    + apply ent_bools_eqb_eq. rewrite ent2_agree_app, ent2_decode_qtrace. reflexivity.
Qed.

(* ================================================================= *)
(* 4. The n-bit search entitlement.                                   *)
(* ================================================================= *)

(* THE MEMBER. A hidden value of n = k + m bits, one bit per register. The
   program asks k questions, one per bit of the first k, commits the first
   claim and certifies. Prior: every n-bit value. Posterior: the 2^m values
   that begin with the answers. Index bits: exactly k. Record moves and the
   ledger's rise: k + 2 (k CHECK, one COMMIT, one CERTIFY). *)
Theorem ent2_bit_search : forall (ans u : list bool),
  ans <> [] -> length ans <= 16 ->
  ent_strictly_stronger
    (ent_member ent_bools_eqb (ent2_agree ans) (ent2_post ans (length u)))
    (ent_member ent_bools_eqb (ent2_agree ans) (ent2_prior (length ans + length u))) /\
  earned_chain ent2_minterface (ent2_world (ans ++ u)) (ent2_qtrace ans) /\
  length (ent2_prior (length ans + length u)) = 2 ^ (length ans + length u) /\
  length (ent2_post ans (length u)) = 2 ^ length u /\
  Nat.log2_up (length (ent2_prior (length ans + length u))) -
    Nat.log2_up (length (ent2_post ans (length u))) = length ans /\
  record_moves ent2_minterface (ent2_qtrace ans) = length ans + 2 /\
  M.mu (mrun (ent2_qtrace ans) (ent2_world (ans ++ u))) -
    M.mu (ent2_world (ans ++ u)) = length ans + 2 /\
  Nat.log2_up (length (ent2_prior (length ans + length u))) -
    Nat.log2_up (length (ent2_post ans (length u)))
    <= M.mu (mrun (ent2_qtrace ans) (ent2_world (ans ++ u))) -
       M.mu (ent2_world (ans ++ u)).
Proof.
  intros ans u Hne Hle.
  assert (Hclean : ti_clean ent2_minterface (ent2_world (ans ++ u)))
    by (apply M.multi_start_clean).
  destruct (ent_representation ent2_mmachine ent2_minterface (list bool) (list bool)
              (ent2_world (ans ++ u)) (ent2_qtrace ans) ent2_decode (ent2_agree ans)
              (fun x => skipn (length ans) x) ent_bools_eqb
              (ent2_prior (length ans + length u)) (ent2_post ans (length u))
              (ent_complete (length ans)) ent2_mmachine_complete ent_bools_eqb_eq
              (ent2_narrowing ans (length u) Hne) (ex_intro _ _ (ent2_witness ans (length u) Hne))
              Hclean (ent2_member_certified ans u Hne Hle)
              ltac:(rewrite ent_complete_depth, ent2_record_moves_qtrace; lia)
              ltac:(rewrite ent2_post_length; apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia)
              (ent2_reduction ans (length u)))
    as [C1 [C2 [_ [C4 [C5 _]]]]].
  destruct (ent2_qtrace_run ans (ans ++ u) Hne) as [Hp _].
  destruct (Hp (conj (ent2_okb_prefix ans u) Hle)) as [_ [Hmu _]].
  assert (Hbits : Nat.log2_up (length (ent2_prior (length ans + length u))) -
                  Nat.log2_up (length (ent2_post ans (length u))) = length ans).
  { rewrite ent2_prior_length, ent2_post_length, !Nat.log2_up_pow2 by lia. lia. }
  assert (Hm0 : M.mu (ent2_world (ans ++ u)) = 0) by reflexivity.
  split; [exact C1 |]. split; [exact C2 |].
  split; [apply ent2_prior_length |]. split; [apply ent2_post_length |].
  split; [exact Hbits |]. split; [apply ent2_record_moves_qtrace |].
  rewrite Hmu, Hm0. split; [lia |]. lia.
Qed.

(* The shortcut record, inhabited by the search, and its landing. *)
Definition ent2_search_shortcut (ans u : list bool) (Hne : ans <> []) (Hle : length ans <= 16) :
  ent_shortcut ent2_minterface (list bool) (list bool)
    (ent2_world (ans ++ u)) (ent2_qtrace ans) :=
  @Build_ent_shortcut ent2_mmachine ent2_minterface (list bool) (list bool)
    (ent2_world (ans ++ u)) (ent2_qtrace ans)
    ent2_decode (ent2_agree ans) (fun x => skipn (length ans) x) ent_bools_eqb
    (ent2_prior (length ans + length u)) (ent2_post ans (length u))
    (ent_complete (length ans)) ent_bools_eqb_eq
    (ent2_narrowing ans (length u) Hne) (ex_intro _ _ (ent2_witness ans (length u) Hne))
    (M.multi_start_clean _) (ent2_member_certified ans u Hne Hle)
    ltac:(rewrite ent_complete_depth, ent2_record_moves_qtrace; lia)
    ltac:(rewrite ent2_post_length; apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia)
    (ent2_reduction ans (length u)).

Theorem ent2_search_lands : forall (ans u : list bool) (Hne : ans <> []) (Hle : length ans <= 16),
  Nat.log2_up (length (ent2_prior (length ans + length u))) -
    Nat.log2_up (length (ent2_post ans (length u)))
  <= M.mu (mrun (ent2_qtrace ans) (ent2_world (ans ++ u))) -
     M.mu (ent2_world (ans ++ u)).
Proof.
  intros ans u Hne Hle.
  destruct (ent_every_shortcut_lands_here ent2_mmachine ent2_minterface (list bool) (list bool)
              (ent2_world (ans ++ u)) (ent2_qtrace ans) (ent2_search_shortcut ans u Hne Hle)
              ent2_mmachine_complete) as [_ [_ [H _]]].
  simpl in H. rewrite ent2_run_mmachine in H. exact H.
Qed.

(* ================================================================= *)
(* 5. The floor with no supplied tree.                                *)
(* ================================================================= *)

(* The claims the program's CHECK moves ask, in order. *)
Fixpoint ent2_claims (ans : list bool) (i0 : nat) : list (E.prop * nat) :=
  match ans with
  | [] => []
  | b :: r => (ent2_prop b, i0) :: ent2_claims r (S i0)
  end.

Lemma ent2_checked_checks : forall ans i0,
  ent_checked ent2_minterface (ent2_checks ans i0) = ent2_claims ans i0.
Proof. induction ans as [| b r IH]; intro i0; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma ent2_checked_app : forall (l1 l2 : list minstr),
  ent_checked ent2_minterface (l1 ++ l2) =
  ent_checked ent2_minterface l1 ++ ent_checked ent2_minterface l2.
Proof.
  induction l1 as [| m l1 IH]; intro l2; simpl; [reflexivity |].
  destruct (ent2_mkind m); simpl; rewrite ?IH; reflexivity.
Qed.

Lemma ent2_checked_qtrace : forall ans,
  ent_checked ent2_minterface (ent2_qtrace ans) = ent2_claims ans 0.
Proof.
  intro ans. unfold ent2_qtrace.
  rewrite ent2_checked_app, ent2_checked_checks. simpl. rewrite app_nil_r. reflexivity.
Qed.

Lemma ent2_claims_length : forall ans i0, length (ent2_claims ans i0) = length ans.
Proof. induction ans; intro i0; simpl; [reflexivity | rewrite IHans; reflexivity]. Qed.

(* The answers at the world of v: what each question says of that value. *)
Lemma ent2_answers_world : forall ans i0 v,
  i0 + length ans <= length v ->
  map (ti_check ent2_minterface (ent2_world v)) (ent2_claims ans i0)
  = ent2_agree ans (skipn i0 v).
Proof.
  induction ans as [| b r IH]; intros i0 v H; simpl in *; [reflexivity |].
  rewrite (ent2_skipn_cons v i0 ltac:(lia)). simpl. f_equal.
  - unfold ti_check, ent2_minterface. simpl. unfold M.check_ok, M.fact_cap. simpl.
    unfold ent2_vals. rewrite ent2_eval_prop. rewrite andb_true_r. reflexivity.
  - apply IH. lia.
Qed.

Lemma ent2_agree_prefix : forall ans w v,
  length ans <= length w -> length ans <= length v ->
  ent2_agree ans w = ent2_agree ans v -> firstn (length ans) w = firstn (length ans) v.
Proof.
  induction ans as [| a r IH]; intros [| b w] [| c v] Hw Hv H; simpl in *; try lia; auto.
  injection H as H1 H2. f_equal.
  - destruct a, b, c; simpl in H1; congruence.
  - apply IH; [lia | lia | exact H2].
Qed.

Lemma ent2_nodup_join : forall {A : Type} (l l' : list A),
  NoDup l -> NoDup l' -> (forall a, In a l -> ~ In a l') -> NoDup (l ++ l').
Proof.
  intros A l l' Hl Hl' Hd. induction l as [| x xs IH]; simpl; [exact Hl' |].
  inversion Hl as [| ? ? Hn Hxs]; subst. constructor.
  - intro Hin. apply in_app_or in Hin as [Hin | Hin]; [exact (Hn Hin) |].
    exact (Hd x (or_introl eq_refl) Hin).
  - apply IH; [exact Hxs | intros a Ha; apply Hd; right; exact Ha].
Qed.

Lemma ent2_nodup_all_bits : forall n, NoDup (ent_all_bools n).
Proof.
  induction n as [| n IH]; simpl; [repeat constructor; simpl; intuition |].
  apply ent2_nodup_join.
  - apply Injective_map_NoDup; [intros x y H; injection H as H; exact H | exact IH].
  - apply Injective_map_NoDup; [intros x y H; injection H as H; exact H | exact IH].
  - intros x Hx Hx'. apply in_map_iff in Hx as [y [<- _]]. apply in_map_iff in Hx' as [z [Hz _]].
    discriminate Hz.
Qed.

Lemma ent2_filter_mono : forall {A : Type} (p q : A -> bool) (l : list A),
  (forall x, In x l -> p x = true -> q x = true) ->
  length (filter p l) <= length (filter q l).
Proof.
  intros A p q l. induction l as [| x l IH]; intro H; simpl; [lia |].
  assert (Hr : length (filter p l) <= length (filter q l))
    by (apply IH; intros y Hy; apply H; right; exact Hy).
  destruct (p x) eqn:Hp.
  - rewrite (H x (or_introl eq_refl) Hp). simpl. lia.
  - destruct (q x); simpl; lia.
Qed.

Lemma ent2_filter_map : forall {A B : Type} (f : B -> bool) (g : A -> B) (l : list A),
  filter f (map g l) = map g (filter (fun x => f (g x)) l).
Proof.
  intros A B f g l. induction l as [| x l IH]; simpl; [reflexivity |].
  destruct (f (g x)); simpl; rewrite IH; reflexivity.
Qed.

(* No more than 2^m of the (k+m)-bit values share a given first k bits. *)
Lemma ent2_prefix_class : forall k m v,
  length v = k + m ->
  length (filter (fun w => ent_bools_eqb (firstn k w) (firstn k v)) (ent_all_bools (k + m)))
    <= 2 ^ m.
Proof.
  intros k m v Hv.
  set (F := filter (fun w => ent_bools_eqb (firstn k w) (firstn k v)) (ent_all_bools (k + m))).
  assert (HF : NoDup F) by (apply NoDup_filter, ent2_nodup_all_bits).
  assert (Hincl : incl F (map (fun u => firstn k v ++ u) (ent_all_bools m))).
  { intros w Hw. apply filter_In in Hw as [Hw1 Hw2]. apply ent_bools_eqb_eq in Hw2.
    apply ent2_in_all_bits in Hw1. apply in_map_iff.
    exists (skipn k w). split.
    - rewrite <- Hw2. apply firstn_skipn.
    - apply ent2_in_all_bits. rewrite skipn_length. lia. }
  pose proof (NoDup_incl_length HF Hincl) as H. rewrite map_length, ent_all_bools_length in H.
  exact H.
Qed.

(* THE FLOOR WITH NO TREE. The prior is the worlds of all (k+m)-bit values.
   The program's own questions are the claims its CHECK moves asked. Asked
   of every world, they split the prior by answers into classes of at most
   2^m, whichever world is the truth. So the index-bit drop from the prior
   to 2^m is at most the CHECK moves, at most the record moves, which are
   the ledger's rise; and here the CHECK moves number exactly k, so the
   floor is met with equality. *)
Theorem ent2_search_questions_floor : forall (ans : list bool) (m : nat),
  ans <> [] ->
  let prior := map ent2_world (ent_all_bools (length ans + m)) in
  let I := ent2_minterface in
  let tr := ent2_qtrace ans in
  length (ent_checked I tr) = length ans /\
  Nat.log2_up (length prior) - Nat.log2_up (2 ^ m) = length ans /\
  Nat.log2_up (length prior) - Nat.log2_up (2 ^ m) <= length (ent_checked I tr) /\
  length (ent_checked I tr) <= record_moves I tr.
Proof.
  intros ans m Hne prior I tr.
  pose proof ent2_mmachine_complete as [_ [_ [Htoll _]]].
  assert (Hchk : length (ent_checked I tr) = length ans).
  { unfold I, tr. rewrite ent2_checked_qtrace. apply ent2_claims_length. }
  assert (Hbits : Nat.log2_up (length prior) - Nat.log2_up (2 ^ m) = length ans).
  { unfold prior. rewrite map_length, ent_all_bools_length, !Nat.log2_up_pow2 by lia. lia. }
  destruct (ent_questions_floor ent2_mmachine I Htoll (ent2_world (ans ++ ans)) tr prior (2 ^ m)
              ltac:(apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia)) as [H1 [H2 _]].
  - intros x Hx. unfold prior in Hx. apply in_map_iff in Hx as [v [<- Hv]].
    apply ent2_in_all_bits in Hv.
    unfold prior. rewrite ent2_filter_map, map_length.
    eapply Nat.le_trans; [| apply (ent2_prefix_class (length ans) m v Hv)].
    apply ent2_filter_mono. intros w Hw Hp. apply ent2_in_all_bits in Hw.
    apply ent_bools_eqb_eq in Hp. apply ent_bools_eqb_eq.
    unfold ent_answers in Hp. unfold I, tr in Hp. rewrite ent2_checked_qtrace in Hp.
    rewrite (ent2_answers_world ans 0 w ltac:(lia)), (ent2_answers_world ans 0 v ltac:(lia)) in Hp.
    simpl in Hp. apply ent2_agree_prefix; [lia | lia | exact Hp].
  - split; [exact Hchk |]. split; [exact Hbits |]. split; [lia | lia].
Qed.

(* ================================================================= *)
(* Assumption audit.                                                  *)
(* ================================================================= *)
Print Assumptions ent2_decode_qtrace.
Print Assumptions ent2_record_moves_qtrace.
Print Assumptions ent2_reduction.
Print Assumptions ent2_witness.
Print Assumptions ent2_narrowing.
Print Assumptions ent2_search_certifies_iff.
Print Assumptions ent2_search_posterior_is_certified.
Print Assumptions ent2_no_search_past_16.
Print Assumptions ent2_member_certified.
Print Assumptions ent2_bit_search.
Print Assumptions ent2_search_shortcut.
Print Assumptions ent2_search_lands.
Print Assumptions ent2_nodup_all_bits.
Print Assumptions ent2_prefix_class.
Print Assumptions ent2_search_questions_floor.
