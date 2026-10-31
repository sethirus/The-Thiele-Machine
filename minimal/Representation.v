(* SCOPE NOTE: standalone proof scope.
   Counts states needed to decode independently realizable historical verdicts.
   The stated interface supplies the hypotheses; no concrete native-machine
   implementation is assumed. *)

From Coq Require Import List Bool Arith Lia.
Import ListNotations.

(* Histories are arbitrary programs from the same supplied clean start.
   No assumption of computational universality is used or needed. *)
Section HistoricalVerdict.
 Context {State History Base : Type}.
 Variable endpoint : History -> State.
 Variable observation : State -> Base.
 Variable earned : History -> bool.
 Variable verdict : State -> bool.
 Hypothesis exact_verdict : forall h, verdict(endpoint h)=earned h.

 Theorem unchecked_reachability_excludes_positive_verdict :
   (forall s,exists h,endpoint h=s /\ earned h=false) ->
   ~exists h,earned h=true.
 Proof.
  intros Hreach [h Hyes]. destruct (Hreach(endpoint h)) as [g [Hg Hno]].
  pose proof (exact_verdict h); pose proof (exact_verdict g).
  rewrite Hg in H0; congruence.
 Qed.
 Theorem same_workspace_different_history_forces_distinct_states : forall h g,
   observation(endpoint h)=observation(endpoint g) -> earned h<>earned g ->
   endpoint h<>endpoint g.
 Proof. intros h g Hob Hdiff He; apply Hdiff; rewrite <-!exact_verdict,He; reflexivity. Qed.
 Theorem workspace_verdict_impossible : forall h g,
   observation(endpoint h)=observation(endpoint g) -> earned h<>earned g ->
   ~exists decode,forall p,decode(observation(endpoint p))=earned p.
 Proof.
  intros h g Hob Hdiff [decode Hd]. apply Hdiff.
  rewrite <-(Hd h),<-(Hd g),Hob; reflexivity.
 Qed.
End HistoricalVerdict.

(* A finite family of distinguishable earned profiles forces that many states
   in ONE observed fibre. Reachability of the representatives is an explicit
   application premise, not inferred from the number of predicate names. *)
Lemma map_injective_nodup {A B} (f:A->B) : forall xs,
 NoDup xs -> (forall a b,In a xs -> In b xs -> f a=f b -> a=b) -> NoDup(map f xs).
Proof.
 intros xs; induction xs as [|a xs IH]; intros Hnd Hi; simpl; [constructor|].
 inversion Hnd; subst; constructor.
 - rewrite in_map_iff; intros [b [He Hb]]; apply H1.
   assert(a=b) by (apply Hi; simpl; auto). subst; exact Hb.
 - apply IH; auto. intros; apply Hi; simpl; auto.
Qed.
Lemma nodup_append_separate {A} : forall xs ys:list A,
 NoDup xs -> NoDup ys -> (forall x,In x xs -> ~In x ys) -> NoDup(xs++ys).
Proof.
 intros xs; induction xs as [|a xs IH]; intros ys Hx Hy Hdis; simpl; [exact Hy|].
 inversion Hx; subst; constructor.
 - rewrite in_app_iff; intros [Ha|Ha]; [contradiction|apply (Hdis a); simpl; auto].
 - apply IH; auto. intros; apply Hdis; simpl; auto.
Qed.
Fixpoint profiles m : list (list bool) :=
 match m with 0=>[[]] | S n=>map (cons false) (profiles n)++map (cons true) (profiles n) end.
Lemma profiles_length : forall m,length(profiles m)=2^m.
Proof. induction m; simpl; [reflexivity|rewrite app_length,!map_length,IHm; lia]. Qed.
Lemma profiles_complete : forall m xs,In xs (profiles m)<->length xs=m.
Proof.
 induction m; intros xs; simpl.
 - destruct xs; simpl; intuition discriminate.
 - rewrite in_app_iff,!in_map_iff; split.
   + intros [[ys [<- Hy]]|[ys [<- Hy]]]; simpl; apply IHm in Hy; lia.
   + destruct xs as [|b ys]; [discriminate|]; simpl; intro H.
     assert (Hy:In ys(profiles m)) by (apply IHm; lia).
     destruct b; [right|left]; exists ys; auto.
Qed.
Lemma profiles_nodup : forall m,NoDup(profiles m).
Proof.
 induction m; simpl; [repeat constructor; simpl; tauto|].
 apply nodup_append_separate.
 - apply map_injective_nodup; auto. intros; congruence.
 - apply map_injective_nodup; auto. intros; congruence.
 - intros xs Hf Ht; apply in_map_iff in Hf as [a [Ha _]].
   apply in_map_iff in Ht as [b [Hb _]]; congruence.
Qed.
Theorem independent_profiles_capacity {State Base}
 (observation:State->Base) (decode:State->list bool)
 (representative:list bool->State) (b:Base) : forall m fibre,
 (forall bits,length bits=m -> observation(representative bits)=b /\ decode(representative bits)=bits) ->
 (forall s,observation s=b -> In s fibre) -> 2^m<=length fibre.
Proof.
 intros m fibre Hr Hf.
 assert(Hnd:NoDup(map representative(profiles m))).
 { apply map_injective_nodup; [apply profiles_nodup|].
   intros a c Ha Hc He; apply profiles_complete in Ha,Hc.
   pose proof (proj2(Hr a Ha)); pose proof (proj2(Hr c Hc)); congruence. }
 pose proof (NoDup_incl_length (l':=fibre) Hnd) as H.
 rewrite map_length,profiles_length in H; apply H.
 intros s Hin; apply in_map_iff in Hin as [bits [<- Hb]].
 apply Hf; apply Hr; apply profiles_complete; exact Hb.
Qed.

(* A list of m Boolean cells attains exactly 2^m admissible profiles. No
   versions, timestamps, ledger or append-only table are needed for this task. *)
Theorem bitmask_capacity_attained : forall m,
 NoDup(profiles m) /\ length(profiles m)=2^m /\
 (forall bits,length bits=m <-> In bits(profiles m)).
Proof. intro m; split; [apply profiles_nodup|]; split; [apply profiles_length|].
 intro bits; symmetry; apply profiles_complete. Qed.

Fixpoint true_count (xs:list bool) : nat := match xs with
 | []=>0 | b::rest=>(if b then 1 else 0)+true_count rest end.
Fixpoint legal_profiles (truths:list bool) : list(list bool) := match truths with
 | []=>[[]]
 | false::rest=>map(cons false)(legal_profiles rest)
 | true::rest=>map(cons false)(legal_profiles rest)++map(cons true)(legal_profiles rest)
 end.
Theorem legal_profiles_count : forall truths,
 length(legal_profiles truths)=2^(true_count truths).
Proof.
 induction truths as [|b rest IH]; [reflexivity|destruct b; simpl].
 - rewrite app_length,!map_length,IH; lia.
 - rewrite map_length,IH; reflexivity.
Qed.
Lemma legal_profiles_distinct : forall truths,NoDup(legal_profiles truths).
Proof.
 induction truths as [|b rest IH]; simpl; [repeat constructor; simpl; tauto|].
 destruct b.
 - apply nodup_append_separate.
   + apply map_injective_nodup; auto; intros; congruence.
   + apply map_injective_nodup; auto; intros; congruence.
   + intros xs Hf Ht; apply in_map_iff in Hf as [a [Ha _]].
     apply in_map_iff in Ht as [c [Hc _]]; congruence.
 - apply map_injective_nodup; auto; intros; congruence.
Qed.
Section TotalRepresentation.
 Context {Base State : Type}.
 Variable truth : Base -> list bool.
 Definition descriptions (bases:list Base) :=
   flat_map (fun b=>map (pair b)(legal_profiles(truth b))) bases.
 Fixpoint capacity (bases:list Base) := match bases with
 | []=>0 | b::rest=>2^(true_count(truth b))+capacity rest end.
 Lemma descriptions_count : forall bases,length(descriptions bases)=capacity bases.
 Proof.
  induction bases as [|b rest IH]; simpl; [reflexivity|].
  unfold descriptions in *; simpl; rewrite app_length,map_length,legal_profiles_count,IH; reflexivity.
 Qed.
 Lemma descriptions_distinct : forall bases,NoDup bases -> NoDup(descriptions bases).
 Proof.
  intros bases; induction bases as [|b rest IH]; intro H; simpl; [constructor|].
  inversion H; subst; apply nodup_append_separate.
  - apply map_injective_nodup; [apply legal_profiles_distinct|intros; congruence].
  - apply IH; assumption.
  - intros [x bits] Hfirst Hrest; apply in_map_iff in Hfirst as [ys [He Hy]].
    injection He as He1 He2; subst x bits.
    apply in_flat_map in Hrest as [c [Hc Hcm]].
    apply in_map_iff in Hcm as [zs [He Hz]]. injection He as He1 He2; subst c; contradiction.
 Qed.
 Theorem exact_profile_representation_lower_bound
  (decode:State->Base*list bool) (representative:Base*list bool->State) : forall bases all,
  NoDup bases ->
  (forall d,In d(descriptions bases) -> decode(representative d)=d) ->
  (forall d,In d(descriptions bases) -> In(representative d) all) ->
  capacity bases<=length all.
 Proof.
  intros bases all Hb Hr Ha.
  assert(Hnd:NoDup(map representative(descriptions bases))).
  { apply map_injective_nodup; [apply descriptions_distinct; exact Hb|].
    intros a b H1 H2 He; pose proof(Hr a H1); pose proof(Hr b H2); congruence. }
  pose proof(NoDup_incl_length (l':=all) Hnd) as Hlen.
  rewrite map_length,descriptions_count in Hlen; apply Hlen.
  intros s Hin; apply in_map_iff in Hin as [d [<- Hd]]; apply Ha; exact Hd.
 Qed.
End TotalRepresentation.
