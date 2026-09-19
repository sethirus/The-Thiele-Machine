(** Executable semantics for deterministic, linear Kami actions.
    Reads use the pre-state, assertions may disable the rule, and duplicate
    writes are rejected exactly as required by [SemWriteReg]. Native reads,
    method calls, nondeterminism and action-level branches are unsupported;
    expression-level conditionals are evaluated normally by [evalExpr]. *)
Require Import Kami.Kami Kami.Semantics.
From Coq Require Import List String.
Import ListNotations.
Open Scope string_scope.

Definition action_read_syntax (old : RegsT) (r : string) (k : Kind)
    : option (type k) :=
  match M.find r old with
  | Some (existT _ (SyntaxKind actual) value) =>
      match decKind actual k with
      | left eq => Some (eq_rect actual type value k eq)
      | right _ => None
      end
  | _ => None
  end.

Definition action_read (old : RegsT) (r : string) (k : FullKind)
    : option (fullType type k) :=
  match k with
  | SyntaxKind k => action_read_syntax old r k
  | NativeKind _ => None
  end.

Lemma action_read_sound : forall old r k v,
  action_read old r k = Some v ->
  M.find r old = Some (existT (fullType type) k v).
Proof.
  intros old r [k|native] v H; [|discriminate].
  unfold action_read, action_read_syntax in H.
  destruct (M.find r old) as [[actual value]|] eqn:Hr; try discriminate.
  destruct actual as [actual|native]; try discriminate.
  destruct (decKind actual k) as [He|Hne]; try discriminate.
  subst k. cbn in H. inversion H; subst. reflexivity.
Qed.

Lemma action_read_complete : forall old r k v,
  M.find r old = Some (existT (fullType type) (SyntaxKind k) v) ->
  action_read old r (SyntaxKind k) = Some v.
Proof.
  intros old r k v H. unfold action_read, action_read_syntax.
  rewrite H, kind_eq. reflexivity.
Qed.

Fixpoint eval_linear_action {k} (old : RegsT) (a : ActionT type k)
    : option (UpdatesT * type k) :=
  match a with
  | Let_ e cont => eval_linear_action old (cont (evalExpr e))
  | ReadReg r kind cont =>
      match action_read old r kind with
      | Some v => eval_linear_action old (cont v)
      | None => None
      end
  | WriteReg r e cont =>
      match eval_linear_action old cont with
      | Some (updates, ret) =>
          match M.find r updates with
          | None => Some (M.add r (existT _ _ (evalExpr e)) updates, ret)
          | Some _ => None
          end
      | None => None
      end
  | Assert_ p cont =>
      if evalExpr p then eval_linear_action old cont else None
  | Displ _ cont => eval_linear_action old cont
  | Return e => Some (M.empty _, evalExpr e)
  | _ => None
  end.

Theorem eval_linear_action_sound : forall k old (a : ActionT type k) u ret,
  eval_linear_action old a = Some (u, ret) ->
  SemAction old a u (M.empty _) ret.
Proof.
  intros k old a. induction a; intros u ret Hrun; cbn in Hrun; try discriminate.
  - apply SemLet. eapply H; eauto.
  - destruct (action_read old r k) as [v|] eqn:Hr; try discriminate.
    eapply SemReadReg; [eapply action_read_sound; exact Hr|]. eapply H; eauto.
  - destruct (eval_linear_action old a) as [[updates value]|] eqn:Ha; try discriminate.
    destruct (M.find r updates) eqn:Hr; try discriminate.
    inversion Hrun; subst. eapply SemWriteReg; [exact Hr|reflexivity|].
    eapply IHa; eauto.
  - destruct (evalExpr e) eqn:He; try discriminate.
    apply SemAssertTrue; [exact He|]. eapply IHa; eauto.
  - apply SemDispl. eapply IHa; eauto.
  - inversion Hrun; subst. apply SemReturn. reflexivity.
Qed.

Fixpoint linear_action {k} (a : ActionT type k) : Prop :=
  match a with
  | Let_ e cont => forall v, linear_action (cont v)
  | ReadReg _ (SyntaxKind _) cont => forall v, linear_action (cont v)
  | WriteReg _ _ cont => linear_action cont
  | Assert_ _ cont => linear_action cont
  | Displ _ cont => linear_action cont
  | Return _ => True
  | _ => False
  end.

Theorem eval_linear_action_complete : forall old k (a : ActionT type k) u calls ret,
  linear_action a -> SemAction old a u calls ret ->
  eval_linear_action old a = Some (u, ret) /\ calls = M.empty _.
Proof.
  intros old k a u calls ret Hlinear Hsem. induction Hsem;
    cbn [linear_action] in Hlinear; try contradiction;
    cbn [eval_linear_action].
  - apply IHHsem. apply Hlinear.
  - destruct regT as [kind|native]; [|contradiction].
    rewrite (action_read_complete _ _ _ _ HRegVal).
    apply IHHsem. apply Hlinear.
  - destruct (IHHsem Hlinear) as [He Hcalls]. rewrite He, HDisjRegs.
    subst. split; reflexivity.
  - rewrite HTrue. apply IHHsem. exact Hlinear.
  - apply IHHsem. exact Hlinear.
  - subst. split; reflexivity.
Qed.

Theorem linear_action_deterministic : forall old k (a : ActionT type k)
    u1 c1 r1 u2 c2 r2,
  linear_action a ->
  SemAction old a u1 c1 r1 -> SemAction old a u2 c2 r2 ->
  u1 = u2 /\ c1 = c2 /\ r1 = r2.
Proof.
  intros old k a u1 c1 r1 u2 c2 r2 Hl H1 H2.
  destruct (eval_linear_action_complete _ _ _ _ _ _ Hl H1) as [E1 C1].
  destruct (eval_linear_action_complete _ _ _ _ _ _ Hl H2) as [E2 C2].
  rewrite E1 in E2. inversion E2; subst. auto.
Qed.
