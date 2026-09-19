(** A projection of successful linear actions. This is deliberately not an
    enabledness test: assertions and the suffix after the selected write are
    justified by the separate [SemAction] premise. No update map is computed. *)
Require Import Kami.Kami Kami.Semantics.
From KamiHW Require Import ActionEvaluator.
From Coq Require Import String.
Open Scope string_scope.

Fixpoint observe_action_write {k} (old : RegsT) (key : string)
    (a : ActionT type k) : option { k : FullKind & fullType type k } :=
  match a with
  | Let_ e cont => observe_action_write old key (cont (evalExpr e))
  | ReadReg r kind cont =>
      match action_read old r kind with
      | Some v => observe_action_write old key (cont v)
      | None => None
      end
  | WriteReg r e cont =>
      if string_dec key r then Some (existT _ _ (evalExpr e))
      else observe_action_write old key cont
  | Assert_ _ cont => observe_action_write old key cont
  | Displ _ cont => observe_action_write old key cont
  | _ => None
  end.

Theorem observe_action_write_correct : forall old k (a : ActionT type k) u calls ret,
  linear_action a -> SemAction old a u calls ret ->
  forall key, observe_action_write old key a = M.find key u.
Proof.
  intros old k a u calls ret Hl Hs. induction Hs;
    cbn [linear_action] in Hl; try contradiction;
    intro key; cbn [observe_action_write].
  - apply IHHs. apply Hl.
  - destruct regT as [kind|native]; [|contradiction].
    rewrite (action_read_complete _ _ _ _ HRegVal).
    apply IHHs. apply Hl.
  - subst. destruct (string_dec key r) as [He|Hne].
    + subst. rewrite M.find_add_1. reflexivity.
    + rewrite M.find_add_2 by exact Hne. apply IHHs. exact Hl.
  - apply IHHs. exact Hl.
  - apply IHHs. exact Hl.
  - subst. rewrite M.find_empty. reflexivity.
Qed.
