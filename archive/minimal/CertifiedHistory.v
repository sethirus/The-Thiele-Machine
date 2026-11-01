From Coq Require Import List Bool Arith Lia.
From Minimal Require Import EarnedCore.
Import ListNotations.

(* R is observed as a finite set, through membership, not by list order. *)
Definition insert_fact(f:fact)(rs:list fact):list fact :=
 if existsb (fact_eqb f) rs then rs else f::rs.
Lemma insert_membership : forall f g rs,In g(insert_fact f rs) <-> g=f \/ In g rs.
Proof.
 intros f g rs; unfold insert_fact; destruct(existsb(fact_eqb f)rs) eqn:E.
 - apply existsb_exists in E as [x [Hx He]]; apply fact_eqb_eq in He; subst x; intuition congruence.
 - simpl; intuition congruence.
Qed.
Lemma insert_nodup : forall f rs,NoDup rs -> NoDup(insert_fact f rs).
Proof.
 intros f rs H; unfold insert_fact; destruct(existsb(fact_eqb f)rs) eqn:E; auto.
 constructor; auto. intro Hin.
 assert(existsb(fact_eqb f)rs=true).
 { apply existsb_exists; exists f; split; auto. apply fact_eqb_eq; reflexivity. }
 congruence.
Qed.
Definition emit(s:state)(i:instr):option fact :=
 if fires(core_of s)i then chan(core_of s) else None.
Definition update_record(s:state)(i:instr)(rs:list fact):list fact :=
 match emit s i with None=>rs|Some f=>insert_fact f rs end.
Definition coarse(rs:list fact):bool:=match rs with []=>false|_=>true end.
Lemma emit_iff_fires : forall s i,coarse(match emit s i with None=>[]|Some f=>[f]end)=fires(core_of s)i.
Proof.
 intros s i; unfold emit; destruct(fires(core_of s)i) eqn:E; simpl; auto.
 destruct i; simpl in E; try discriminate.
 unfold certify_ok in E; apply andb_true_iff in E as [_ H].
 destruct(chan(core_of s)); simpl in *; congruence.
Qed.
Lemma coarse_insert : forall f rs,coarse(insert_fact f rs)=true.
Proof.
 intros; unfold insert_fact; destruct rs; simpl; auto.
 destruct(fact_eqb f f0 || existsb(fact_eqb f)rs); reflexivity.
Qed.
Theorem boolean_latch_step : forall s i rs,
 coarse(update_record s i rs)=coarse rs || fires(core_of s)i.
Proof.
 intros; pose proof(emit_iff_fires s i) as H.
 unfold update_record; destruct(emit s i); simpl in H; rewrite <-H.
 - rewrite coarse_insert,orb_true_r; reflexivity.
 - rewrite orb_false_r; reflexivity.
Qed.

Definition recorded_state := (state*list fact)%type.
Definition recorded_step(i:instr)(s:recorded_state):recorded_state :=
 (exec(fst s)i,update_record(fst s)i(snd s)).
Fixpoint recorded_run(word:list instr)(s:recorded_state):recorded_state :=
 match word with []=>s|i::rest=>recorded_run rest(recorded_step i s)end.

Theorem native_projection : forall word s rs,
 fst(recorded_run word(s,rs))=run word s.
Proof. induction word; intros; simpl; [reflexivity|apply IHword]. Qed.
Theorem exact_native_boolean_shadow : forall word s rs,
 coarse rs=cert s -> coarse(snd(recorded_run word(s,rs)))=cert(run word s).
Proof.
 induction word as [|i word IH]; intros s rs H; simpl; auto.
 apply IH. change (coarse(update_record s i rs)=cert s || fires(core_of s)i).
 rewrite boolean_latch_step,H; reflexivity.
Qed.
Theorem clean_boolean_shadow : forall word s,
 clean_start s -> coarse(snd(recorded_run word(s,[])))=cert(run word s).
Proof. intros word s [_ [_ H]]; apply exact_native_boolean_shadow; simpl; congruence. Qed.
Theorem horizontal_cannot_change_record : forall i s rs,
 cost i=0 -> snd(recorded_step i(s,rs))=rs.
Proof. intros [] s rs H; simpl in H; try discriminate; reflexivity. Qed.

(* Independent trace event relation: the fact really was the channel payload
   of a successful CERTIFY at some point in the execution. *)
Inductive published_from : state -> list instr -> fact -> Prop :=
| published_here : forall s i word f,emit s i=Some f -> published_from s(i::word)f
| published_later : forall s i word f,published_from(exec s i)word f -> published_from s(i::word)f.

Theorem exact_history_membership : forall word s rs f,
 In f(snd(recorded_run word(s,rs))) <-> In f rs \/ published_from s word f.
Proof.
 induction word as [|i word IH]; intros s rs f; simpl.
 - split; [auto|intros [H|H]; auto; inversion H].
 - unfold recorded_step; cbn [fst snd]. rewrite IH. unfold update_record.
   destruct(emit s i) as [g|] eqn:E.
   + rewrite insert_membership. split.
     * intros [[He|Hin]|Hpub]; [subst; right; apply published_here; exact E|auto|right; apply published_later; exact Hpub].
     * intros [Hin|Hpub]; [auto|inversion Hpub; subst; [left; left; congruence|auto]].
   + split.
     * intros [Hin|Hpub]; [auto|right; apply published_later; exact Hpub].
     * intros [Hin|Hpub]; [auto|inversion Hpub; subst; [congruence|auto]].
Qed.
Theorem no_horizontal_forgery : forall word s rs f,
 (forall i,In i word -> cost i=0) ->
 In f(snd(recorded_run word(s,rs))) <-> In f rs.
Proof.
 induction word as [|i word IH]; intros; simpl; [tauto|].
 unfold recorded_step; cbn [fst snd]. rewrite IH.
 - assert(cost i=0) by (apply H; simpl; auto).
   destruct i; simpl in H0; try discriminate; tauto.
 - intros j Hj; apply H; simpl; auto.
Qed.
Theorem historical_records_persist : forall word s rs f,
 In f rs -> In f(snd(recorded_run word(s,rs))).
Proof. intros; apply exact_history_membership; auto. Qed.
Theorem record_remains_a_set : forall word s rs,
 NoDup rs -> NoDup(snd(recorded_run word(s,rs))).
Proof.
 induction word; intros; simpl; [assumption|]. apply IHword.
 unfold recorded_step; simpl. unfold update_record; destruct(emit s a); auto using insert_nodup.
Qed.

Theorem boolean_shadow_loses_claim_identity :
 coarse [mkfact PZero CA 0]=coarse [mkfact PZero CB 0] /\
 ~In (mkfact PZero CA 0) [mkfact PZero CB 0].
Proof. split; [reflexivity|simpl; intuition discriminate]. Qed.

(* Native commitment survives a later write, but the publication keeps its OLD
   edition label. It does not relabel the old check as a new-edition check. *)
Theorem publication_after_edit_keeps_old_binding :
 let s:=recorded_run [CHECK PZero CA;COMMIT PZero CA;INC CA;CERTIFY](start 0 0,[]) in
 snd s=[mkfact PZero CA 0] /\ va(core_of(fst s))=1 /\
 ~In(mkfact PZero CA 1)(snd s).
Proof. simpl; repeat split; intuition discriminate. Qed.

Theorem native_checked_facts_are_not_certified_records :
 let s:=recorded_run [CHECK PZero CA](start 0 0,[]) in
 facts(core_of(fst s))=[mkfact PZero CA 0] /\ snd s=[] /\ cert(fst s)=false.
Proof. repeat split; reflexivity. Qed.

Lemma publication_event_origin : forall word s f,published_from s word f ->
 exists pre post,word=pre++CERTIFY::post /\ chan(core_of(run pre s))=Some f.
Proof.
 intros word s f H; induction H.
 - unfold emit in H; destruct(fires(core_of s)i) eqn:E; [|discriminate].
   destruct i; simpl in E; try discriminate.
   exists [],word; simpl; auto.
 - destruct IHpublished_from as [pre [post [Hw Hchan]]].
   exists(i::pre),post; simpl; split; [rewrite Hw; reflexivity|assumption].
Qed.
Theorem every_record_has_earned_check_commit_chain : forall word s0 f,
 clean_start s0 -> In f(snd(recorded_run word(s0,[]))) ->
 exists prepub postpub preC p c midC preCheck midCheck,
 word=prepub++CERTIFY::postpub /\ prepub=preC++COMMIT p c::midC /\
 preC=preCheck++CHECK p c::midCheck /\
 check_ok(core_of(run preCheck s0))p c=true /\
 commit_ok(core_of(run preC s0))p c=true /\
 ver(core_of(run preCheck s0))c=ver(core_of(run preC s0))c /\
 f=claim(core_of(run preC s0))p c.
Proof.
 intros word s0 f Hclean Hin; apply exact_history_membership in Hin.
 destruct Hin as [Hin|Hpub]; [contradiction|].
 destruct(publication_event_origin word s0 f Hpub) as [prepub [postpub [Hw Hch]]].
 pose proof Hclean as [_ [Hempty _]].
 destruct(chan_origin s0 prepub f Hempty Hch) as [preC [p [c [midC [Hpc [Hok Hf]]]]]].
 destruct(earned_commitment_provenance s0 preC p c Hclean Hok)
 as [preCheck [midCheck [Hcheck [Hpass [_ [_ [Hver _]]]]]]].
 exists prepub,postpub,preC,p,c,midC,preCheck,midCheck; repeat split; assumption.
Qed.
