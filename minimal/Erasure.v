(* SCOPE NOTE: standalone proof scope.
   Characterizes exact recovery of a predicate from an arbitrary retained observation.
   The stated interface supplies the hypotheses; no concrete native-machine
   implementation is assumed. *)

From Coq Require Import List Bool Arith Lia.
Import ListNotations.

Section Observation.
 Context {X Y:Type}.
 Variable f:X->Y.
 Variable P:X->bool.

 Theorem mixed_fibre_excludes_final_verifier : forall good bad,
 f good=f bad -> P good=true -> P bad=false ->
 ~exists verify:Y->bool,forall x,verify(f x)=P x.
 Proof.
  intros good bad E Hg Hb [verify H].
  pose proof(H good); pose proof(H bad); congruence.
 Qed.

 Theorem verifier_requires_fibre_constancy :
 (exists verify:Y->bool,forall x,verify(f x)=P x) ->
 forall x z,f x=f z -> P x=P z.
 Proof. intros [verify H] x z E; rewrite <-!H,E; reflexivity. Qed.

 Theorem fibre_constancy_suffices_with_representatives : forall choose:Y->X,
 (forall x,f(choose(f x))=f x) ->
 (forall x z,f x=f z -> P x=P z) ->
 forall x,P(choose(f x))=P x.
 Proof. intros choose Hc Hp x; apply Hp; apply Hc. Qed.

 Theorem searching_a_valid_preimage_is_not_actual_history : forall good bad,
 f good=f bad -> P good=true -> P bad=false ->
 (exists x,f x=f bad /\ P x=true) /\ P bad=false.
 Proof. intros; split; [exists good; auto|assumption]. Qed.

 Definition inspected_state(x:X):Y*bool:=(f x,P x).
 Theorem inline_reading_is_exact : forall x,snd(inspected_state x)=P x.
 Proof. reflexivity. Qed.
 Theorem mixed_fibre_forces_distinct_enriched_states : forall x z,
 f x=f z -> P x<>P z -> inspected_state x<>inspected_state z.
 Proof. intros x z E H He; inversion He; contradiction. Qed.
End Observation.

(* Information loss matters only if it loses the requested property. *)
Theorem collision_does_not_always_prevent_verification :
 let f:=fun x:bool*bool=>fst x in
 f(true,false)=f(true,true) /\
 (forall x,fst x=f x).
Proof. split; reflexivity. Qed.

Fixpoint iterate {X}(F:X->X)(n:nat)(x:X):X:=
 match n with 0=>x|S k=>F(iterate F k x)end.
Theorem fixed_length_injective_history : forall X (F:X->X),
 (forall x y,F x=F y -> x=y) ->
 forall n x y,iterate F n x=iterate F n y -> x=y.
Proof. intros X F H n; induction n; intros; simpl in *; auto. Qed.

Theorem unknown_duration_can_hide_history_under_injective_steps :
 (forall x y:bool,negb x=negb y -> x=y) /\
 iterate negb 1 false=iterate negb 2 true /\ false<>true.
Proof. split; [intros [] []; simpl; congruence|split; discriminate || reflexivity]. Qed.

Theorem different_injective_programs_can_hide_history :
 (forall x y:bool,negb x=negb y -> x=y) /\
 (forall x y:bool,(fun z=>z)x=(fun z=>z)y -> x=y) /\
 negb false=(fun z:bool=>z)true /\ false<>true.
Proof. repeat split; intros; try assumption; try discriminate; destruct x,y; simpl in *; congruence. Qed.
