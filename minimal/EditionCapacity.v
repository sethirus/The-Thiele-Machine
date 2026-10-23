(* SCOPE NOTE: standalone proof scope.
   Counts independently recoverable edition histories in the explicit archive interface.
   The stated interface supplies the hypotheses; no concrete native-machine
   implementation is assumed. *)

From Coq Require Import List Bool Arith Lia.
From Minimal Require Import Representation.
Import ListNotations.

Inductive progress := Raw | Checked | Committed | Published.
Inductive command := Write (b:bool) | Idle | Check | Commit | Certify.
Record state := mkstate { workspace:bool; archive:list bool; stage:progress }.
Definition raised(p:progress):bool:=match p with Published=>true|_=>false end.
Definition step(i:command)(s:state):state :=
 match i with
 | Write b=>mkstate b (archive s++[raised(stage s)]) Raw
 | Idle=>s
 | Check=>mkstate(workspace s)(archive s)
              (match stage s with Raw=>if workspace s then Checked else Raw|p=>p end)
 | Commit=>mkstate(workspace s)(archive s)(match stage s with Checked=>Committed|p=>p end)
 | Certify=>mkstate(workspace s)(archive s)(match stage s with Committed=>Published|p=>p end)
 end.
Fixpoint run(w:list command)(s:state):state:=
 match w with []=>s|i::rest=>run rest(step i s)end.
Definition query(s:state)(edition:nat):bool:=nth edition(archive s++[raised(stage s)])false.
Definition block(b:bool):list command:=(if b then [Check;Commit;Certify] else [])++[Write true].
Fixpoint program(bits:list bool):list command:=match bits with
 | []=>[]|b::rest=>block b++program rest end.
Lemma run_append : forall u v s,run(u++v)s=run v(run u s).
Proof. induction u; intros; simpl; auto. Qed.
Lemma block_effect : forall b old,run(block b)(mkstate true old Raw)=mkstate true(old++[b])Raw.
Proof. intros [] old; reflexivity. Qed.
Theorem realize_every_history : forall bits old,
 run(program bits)(mkstate true old Raw)=mkstate true(old++bits)Raw.
Proof.
 induction bits as [|b rest IH]; intro old; simpl.
 - rewrite app_nil_r; reflexivity.
 - rewrite run_append,block_effect,IH,<-app_assoc; reflexivity.
Qed.
Lemma trailing_false_irrelevant : forall bits j,
 nth j(bits++[false])false=nth j bits false.
Proof.
 induction bits as [|b rest IH]; intros [|j]; simpl; auto.
 destruct j; reflexivity.
Qed.
Theorem exact_edition_queries : forall bits j,
 query(run(program bits)(mkstate true [] Raw))j=nth j bits false.
Proof. intros; rewrite realize_every_history; simpl; apply trailing_false_irrelevant. Qed.
Theorem common_workspace : forall bits,
 workspace(run(program bits)(mkstate true [] Raw))=true.
Proof. intros; rewrite realize_every_history; reflexivity. Qed.
Theorem distinct_histories_same_workspace : forall a b,
 a<>b -> length a=length b ->
 run(program a)(mkstate true [] Raw)<>run(program b)(mkstate true [] Raw).
Proof. intros a b Hne Hlen He; rewrite !realize_every_history in He; injection He; auto. Qed.

(* General lower bound: an arbitrary host, not necessarily the model above,
   supplies a final state for each independently chosen edition history. *)
Section LowerBound.
 Context {S:Type}.
 Variable endpoint:list bool->S.
 Variable observe:S->nat->bool.
 Hypothesis exact_queries:forall bits j,observe(endpoint bits)j=nth j bits false.
 Theorem edition_history_capacity : forall n fibre,
 (forall bits,length bits=n -> In(endpoint bits)fibre) -> 2^n<=length fibre.
 Proof.
  intros n fibre Hcover.
  assert(Hnd:NoDup(map endpoint(profiles n))).
  { apply map_injective_nodup; [apply profiles_nodup|].
    intros a b Ha Hb He; apply profiles_complete in Ha,Hb.
    apply nth_ext with (d:=false)(d':=false); [lia|].
    intros j Hj; rewrite <-(exact_queries a j),<-(exact_queries b j),He; reflexivity. }
  pose proof(NoDup_incl_length (l':=fibre) Hnd) as H.
  rewrite map_length,profiles_length in H; apply H.
  intros s Hin; apply in_map_iff in Hin as [bits [<- Hb]].
  apply Hcover; apply profiles_complete; assumption.
 Qed.
 Theorem no_finite_history_cover : ~exists fibre,forall bits,In(endpoint bits)fibre.
 Proof.
  intros [fibre Hcover].
  pose proof(edition_history_capacity (Nat.succ(length fibre)) fibre (fun bits _=>Hcover bits)) as H.
  assert(length fibre < 2^(Nat.succ(length fibre))).
  { generalize (length fibre); intro n; induction n; simpl in *; lia. }
  lia.
 Qed.
End LowerBound.

Theorem model_attains_exact_profile_count : forall n,
 NoDup(map(fun bits=>run(program bits)(mkstate true [] Raw))(profiles n)) /\
 length(map(fun bits=>run(program bits)(mkstate true [] Raw))(profiles n))=2^n /\
 (forall bits,length bits=n -> workspace(run(program bits)(mkstate true [] Raw))=true).
Proof.
 intro n; split.
 - apply map_injective_nodup; [apply profiles_nodup|].
   intros a b Ha Hb H; rewrite !realize_every_history in H; injection H; auto.
 - split; [rewrite map_length,profiles_length; reflexivity|intros; apply common_workspace].
Qed.

Theorem workspace_write_preserves_historical_queries : forall s b j,
 query(step(Write b)s)j=query s j.
Proof.
 intros [old bits p] b j; unfold query,step; simpl.
 apply trailing_false_irrelevant.
Qed.
Theorem workspace_step_independent_of_history : forall b s,
 workspace(step(Write b)s)=b.
Proof. reflexivity. Qed.

Theorem current_certification_is_not_the_permanent_boolean :
 let s:=run [Check;Commit;Certify;Write false](mkstate true [] Raw) in
 query s 0=true /\ raised(stage s)=false /\ workspace s=false.
Proof. repeat split; reflexivity. Qed.
