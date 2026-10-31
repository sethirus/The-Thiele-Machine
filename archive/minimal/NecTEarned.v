(** NecTEarned.v: the earned-record clause of Thiele-complete is necessary.

    Take any Thiele-complete machine and add one move ZAP that costs 1 and
    raises the record from every state, with the ledger counting it. The
    new machine still has a universal base (clause (a)), an exact toll
    (clause (c)) and a claim that can fail (clause (d)), and its checker is
    sound and respects "unchanged", but it does not earn its record: the
    one-move run ZAP from a clean start ends with the record up and no
    CHECK, COMMIT or CERTIFY in it. The machine is not Thiele-complete
    through any interface.

    What is proved (every result closed under the global context):

      [nec_t_zap_meets_all_but_chain]  for every Thiele-complete interface I,
        the interface of the machine with ZAP meets the base clause, the
        exact toll and non-vacuity, and the clean-start, soundness and
        unchanged conjuncts of the earned-record clause, and does not meet
        the earned-record clause.
      [nec_t_zap_not_thiele_complete]  the machine with ZAP is not
        Thiele-complete, through any interface. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Minimal.ThieleComplete.

Definition zap_state (M : machine) : Type := (m_state M * bool * nat)%type.

Definition zap_step (M : machine) (s : zap_state M) (o : option (m_move M)) : zap_state M :=
  match s with
  | (x, f, n) =>
      match o with
      | Some m => (m_step M x m, f, n)
      | None => (x, true, S n)
      end
  end.

Definition zap_cost (M : machine) (o : option (m_move M)) : nat :=
  match o with Some m => m_cost M m | None => 1 end.

Definition zap_rec (M : machine) (s : zap_state M) : bool :=
  match s with (x, f, n) => m_record M x || f end.

(* The machine with one extra move, ZAP, written None. *)
Definition zap_machine (M : machine) : machine :=
  mk_machine (zap_state M) (option (m_move M)) (zap_step M) (zap_cost M) (zap_rec M).

Lemma zap_run_some : forall M tr x f n,
  run (zap_machine M) (map (@Some (m_move M)) tr) (x, f, n) = (run M tr x, f, n).
Proof.
  intros M. induction tr as [| m tr IH]; intros x f n; simpl; [reflexivity |].
  apply IH.
Qed.

Definition zap_base {M : machine} (U : universal_base M) : universal_base (zap_machine M) :=
  mk_ub (zap_machine M)
    (fun s => ub_window U (fst (fst s)))
    (fun s => ub_live U (fst (fst s)))
    (fun i => Some (ub_compile U i))
    (fun a b => (ub_load U a b, false, 0))
    (fun a b => ub_load_window U a b)
    (fun a b => ub_load_live U a b)
    (fun s i Hl => match s as s0 return
         ub_live U (fst (fst s0)) ->
         ub_window U (fst (fst (zap_step M s0 (Some (ub_compile U i))))) =
           cm_exec i (ub_window U (fst (fst s0))) /\
         ub_live U (fst (fst (zap_step M s0 (Some (ub_compile U i))))) with
       | (x, f, n) => fun Hl' => ub_sim U x i Hl'
       end Hl).

Definition zap_interface {M : machine} (I : thiele_interface M) :
  thiele_interface (zap_machine M) :=
  mk_ti (zap_machine M) (zap_base (ti_base I)) (ti_claim I)
    (fun o => match o with Some m => ti_kind I m | None => KCertify end)
    (fun c s => ti_meaning I c (fst (fst s)))
    (fun s c => ti_check I (fst (fst s)) c)
    (fun c s t => ti_same I c (fst (fst s)) (fst (fst t)))
    (fun s => ti_clean I (fst (fst s)) /\ snd (fst s) = false /\ snd s = 0)
    (fun s => ti_ledger I (fst (fst s)) + snd s).

(* The earned-record clause without its chain conjunct. *)
Definition earned_record_clause_no_chain {M : machine} (I : thiele_interface M) : Prop :=
  (forall s, ti_clean I s -> m_record M s = false) /\
  (forall s c, ti_check I s c = true -> ti_meaning I c s) /\
  (forall c s s', ti_same I c s s' -> ti_meaning I c s -> ti_meaning I c s').

Theorem nec_t_zap_meets_all_but_chain : forall M (I : thiele_interface M),
  thiele_complete_with I ->
  universal_base_clause (zap_interface I) /\
  earned_record_clause_no_chain (zap_interface I) /\
  exact_toll_clause (zap_interface I) /\
  non_vacuity_clause (zap_interface I) /\
  ~ earned_record_clause (zap_interface I).
Proof.
  intros M I HC.
  destruct HC as [[Hk [Hclean [Hbase Hperm]]] [[Hb1 [_ [Hb3 Hb4]]] [[Hc1 Hc2] Hd]]].
  split; [| split; [| split; [| split]]].
  - (* universal base clause *)
    split; [intro i; simpl; apply Hk |].
    split; [intros a b; simpl; split; [apply Hclean | split; reflexivity] |].
    split.
    + intros [[x f] n] [m |] Hkm; simpl in Hkm |- *; [| discriminate Hkm].
      rewrite (Hbase x m Hkm). reflexivity.
    + intros [[x f] n] [m |] H; simpl in H |- *.
      * apply orb_true_iff in H as [H | H]; apply orb_true_iff;
          [left; apply Hperm; exact H | right; exact H].
      * apply orb_true_iff. right. reflexivity.
  - (* clean, sound, unchanged *)
    split; [| split].
    + intros [[x f] n] [Hc [Hf Hn]]. simpl in *. subst f.
      rewrite (Hb1 x Hc). reflexivity.
    + intros [[x f] n] c H. simpl in *. apply Hb3, H.
    + intros c [[x f] n] [[y g] k] H. simpl in *. apply Hb4, H.
  - (* exact toll *)
    split.
    + intros [m |]; simpl; [apply Hc1 | reflexivity].
    + intros [[x f] n] [m |]; simpl.
      * rewrite Hc2. lia.
      * lia.
  - (* non-vacuity *)
    destruct Hd as [c [chk [cmt [crt [Hk1 [Hk2 [Hk3 [Hiff [Hyes Hno]]]]]]]]].
    exists c, (Some chk), (Some cmt), (Some crt).
    split; [exact Hk1 |]. split; [exact Hk2 |]. split; [exact Hk3 |].
    split; [| split; [exact Hyes | exact Hno]].
    intros a b.
    unfold load. cbn [zap_interface ti_base zap_base ub_load ti_meaning].
    change (run (zap_machine M) [Some chk; Some cmt; Some crt]
              (ub_load (ti_base I) a b, false, 0))
      with (run (zap_machine M) (map (@Some (m_move M)) [chk; cmt; crt])
              (ub_load (ti_base I) a b, false, 0)).
    cbn [m_record zap_machine].
    rewrite zap_run_some. cbn [zap_rec]. rewrite orb_false_r. apply Hiff.
  - (* the chain conjunct fails: ZAP from a clean start raises the record
       with no CHECK, COMMIT, CERTIFY *)
    intros [_ [Hchain _]].
    destruct Hd as [c [chk [cmt [crt [Hk1 [Hk2 [Hk3 [Hiff [Hyes Hno]]]]]]]]].
    destruct (Hchain (ub_load (ti_base I) 0 0, false, 0) [None]) as
      [pre [c' [chk' [mid1 [cmt' [mid2 [crt' [post [Htr _]]]]]]]]].
    + simpl. split; [apply Hclean | split; reflexivity].
    + simpl. apply orb_true_r.
    + apply (f_equal (@length _)) in Htr. simpl in Htr.
      rewrite !app_length in Htr. simpl in Htr. rewrite app_length in Htr. simpl in Htr.
      lia.
Qed.

(* No interface at all makes the machine with ZAP Thiele-complete. *)
Theorem nec_t_zap_not_thiele_complete : forall M, ~ thiele_complete (zap_machine M).
Proof.
  intros M. apply one_move_record_excluded.
  exists None. intros [[x f] n]. simpl. apply orb_true_r.
Qed.

Print Assumptions nec_t_zap_meets_all_but_chain.
Print Assumptions nec_t_zap_not_thiele_complete.
