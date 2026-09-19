(** Preservation of the declared register schema by actual CPU rule execution. *)
Require Import Kami.Kami Kami.Semantics.
From KamiHW Require Import ThieleTypes ThieleCPUCore ActionEvaluator
  DispatchExecution CoreRules CoreExecution.
From Coq Require Import List String.

Definition register_kind (old : RegsT) (name : string) : option FullKind :=
  option_map (@projT1 FullKind (fullType type)) (M.find name old).

Definition cpu_register_kind := register_kind dispatch_reset_state.

Definition registers_match (schema : string -> option FullKind) (old : RegsT) :=
  forall name, register_kind old name = schema name.

Definition updates_match (schema : string -> option FullKind) (u : UpdatesT) :=
  forall name value, M.find name u = Some value ->
    schema name = Some (projT1 value).

Lemma empty_updates_match : forall schema, updates_match schema (M.empty _).
Proof.
  intros schema name value H. rewrite M.find_empty in H. discriminate.
Qed.

Lemma added_update_matches : forall schema u name kind value,
  updates_match schema u -> schema name = Some kind ->
  updates_match schema (M.add name (existT (fullType type) kind value) u).
Proof.
  intros schema u name kind value Hu Hkind key actual H.
  destruct (string_dec key name) as [He|Hne].
  - subst key. rewrite M.find_add_1 in H. inversion H; subst. exact Hkind.
  - rewrite M.find_add_2 in H by exact Hne. eapply Hu. exact H.
Qed.

Lemma update_preserves_registers : forall schema old u,
  registers_match schema old -> updates_match schema u ->
  registers_match schema (M.union u old).
Proof.
  intros schema old u Hs Hu name. unfold register_kind.
  rewrite M.find_union. destruct (M.find name u) as [value|] eqn:He.
  - cbn. symmetry. eapply Hu. exact He.
  - exact (Hs name).
Qed.

Fixpoint declared_writes {k} (schema : string -> option FullKind)
  (a : ActionT type k) : Prop :=
  match a with
  | Let_ _ cont => forall value, declared_writes schema (cont value)
  | ReadReg _ _ cont => forall value, declared_writes schema (cont value)
  | @WriteReg _ _ name kind _ cont =>
      schema name = Some kind /\ declared_writes schema cont
  | Assert_ _ cont => declared_writes schema cont
  | Displ _ cont => declared_writes schema cont
  | Return _ => True
  | _ => False
  end.

Theorem evaluated_updates_match : forall schema k old (a : ActionT type k) u ret,
  declared_writes schema a ->
  eval_linear_action old a = Some (u, ret) -> updates_match schema u.
Proof.
  intros schema k old a. induction a; intros u ret Hd Hr;
    cbn [declared_writes] in Hd; try contradiction;
    cbn [eval_linear_action] in Hr.
  - eapply H; [apply Hd|exact Hr].
  - destruct (action_read old r k) as [value|] eqn:He; [|discriminate].
    eapply H; [apply Hd|exact Hr].
  - destruct Hd as [Hkind Hd].
    destruct (eval_linear_action old a) as [[updates value]|] eqn:He;
      [|discriminate].
    destruct (M.find r updates); [discriminate|]. inversion Hr; subst.
    apply added_update_matches; [eapply IHa; eauto|exact Hkind].
  - destruct (evalExpr e); [eapply IHa; eassumption|discriminate].
  - eapply IHa; eassumption.
  - inversion Hr; subst. apply empty_updates_match.
Qed.

Lemma cpu_writes_declared :
  Forall (fun r : cpu_rule => declared_writes cpu_register_kind (attrType r type))
    (getRules thieleCore).
Proof.
  cbn [getRules].
  let rec solve_declared :=
    cbn [declared_writes];
    first [exact I | intro; solve_declared |
           split; [vm_compute; reflexivity | solve_declared]] in
  repeat (apply Forall_cons; [cbn [attrType]; solve_declared|]).
  apply Forall_nil.
Qed.

Theorem cpu_selected_update_matches : forall old name u,
  select_cpu_rule old (getRules thieleCore) = Some (name, u) ->
  updates_match cpu_register_kind u.
Proof.
  intros old name u Hs.
  destruct (selected_cpu_rule _ _ _ _ Hs) as [r [Hin [_ He]]].
  pose proof (proj1 (Forall_forall _ _) cpu_writes_declared r Hin) as Hd.
  unfold eval_cpu_rule in He.
  destruct (eval_linear_action old (attrType r type)) as [[updates ret]|] eqn:Hr;
    [|discriminate].
  inversion He; subst.
  eapply (evaluated_updates_match cpu_register_kind Void old (attrType r type));
    [exact Hd|exact Hr].
Qed.

Theorem cpu_run_preserves_register_schema : forall fuel old,
  registers_match cpu_register_kind old ->
  registers_match cpu_register_kind (fst (run_cpu_rules fuel old)).
Proof.
  induction fuel as [|fuel IH]; intros old Hs; cbn [run_cpu_rules]; [exact Hs|].
  destruct (select_cpu_rule old (getRules thieleCore)) as [[name u]|] eqn:He.
  - specialize (IH (M.union u old)).
    destruct (run_cpu_rules fuel (M.union u old)) as [final labels].
    cbn [fst] in *. apply IH. eapply update_preserves_registers; [exact Hs|].
    eapply cpu_selected_update_matches. exact He.
  - exact Hs.
Qed.

Theorem cpu_reset_run_register_schema : forall fuel,
  registers_match cpu_register_kind (fst (run_cpu_rules fuel dispatch_reset_state)).
Proof.
  intro fuel. apply cpu_run_preserves_register_schema. intro name. reflexivity.
Qed.
