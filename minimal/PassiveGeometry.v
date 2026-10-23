(* SCOPE NOTE: standalone proof scope.
   Derives projection and record preservation from explicitly supplied horizontal transition laws.
   The stated interface supplies the hypotheses; no concrete native-machine
   implementation is assumed. *)

From Coq Require Import List.
Import ListNotations.
Section Geometry.
 Context {S B R I:Type}.
 Variable view:S->B.
 Variable record:S->R.
 Variable H:I->S->S.
 Variable h:I->B->B.
 Hypothesis autonomous:forall i s,view(H i s)=h i(view s).
 Hypothesis passive:forall i s,record(H i s)=record s.
 Fixpoint runH(word:list I)(s:S):S:=match word with []=>s|i::rest=>runH rest(H i s)end.
 Fixpoint runB(word:list I)(b:B):B:=match word with []=>b|i::rest=>runB rest(h i b)end.
 Theorem horizontal_projection : forall word s,view(runH word s)=runB word(view s).
 Proof. induction word; intros; simpl; auto. rewrite IHword,autonomous; reflexivity. Qed.
 Theorem horizontal_preserves_record : forall word s,record(runH word s)=record s.
 Proof. induction word; intros; simpl; auto. rewrite IHword,passive; reflexivity. Qed.
 Theorem permanent_trajectory_blindness : forall s t,
 view s=view t -> record s<>record t -> forall word,
 view(runH word s)=view(runH word t) /\ record(runH word s)<>record(runH word t).
 Proof. intros; rewrite !horizontal_projection,!horizontal_preserves_record; split; congruence. Qed.
 Theorem no_in_view_decoder : forall s t,
 view s=view t -> record s<>record t ->
 ~exists decode:B->R,forall x,decode(view x)=record x.
 Proof. intros s t Hv Hr [decode Hd]; specialize(Hd s) as Hs; specialize(Hd t) as Ht; congruence. Qed.
 Theorem vertical_change_forces_nontrivial_fibre : forall V:S->S,
 (forall s,view(V s)=view s) -> forall s,
 record(V s)<>record s -> s<>V s /\ view(V s)=view s.
 Proof. intros V Hv s Hr; split; [intro He; rewrite <-He in Hr; contradiction|apply Hv]. Qed.
End Geometry.
