(** The start method of the CPU.

    The hardware holds [hardware_reset_state] at reset, where the CPU is
    halted, so a program can be written into instruction memory through
    [loadInstr] before anything executes. One call of [start] then gives
    exactly [dispatch_reset_state], the registers execution begins from:
    not halted, program counter zero, every other register as at reset.
    Every theorem stated from [dispatch_reset_state] therefore describes the
    machine from the moment it is started. *)
Require Import Kami.Kami Kami.Semantics.
From KamiHW Require Import ThieleTypes ThieleCPUCore ActionEvaluator
  DispatchExecution.
From Coq Require Import List String.
Import ListNotations.
Open Scope string_scope.

(** A method body that does nothing, used only as the default of [nth]. *)
Definition no_method : DefMethT :=
  {| attrName := "none";
     attrType := existT MethodT {| arg := Void; ret := Void |}
                   (fun ty (_ : fullType ty (SyntaxKind Void)) =>
                      Return (Const ty (natToWord 0 0))) |}.

Definition start_method : DefMethT := nth 1 (getDefsBodies thieleCore) no_method.

Lemma start_method_name : attrName start_method = "start".
Proof. reflexivity. Qed.

Lemma start_method_in : In start_method (getDefsBodies thieleCore).
Proof. unfold start_method. apply nth_In. cbn. repeat constructor. Qed.

Definition start_action : ActionT type Void :=
  projT2 (attrType start_method) type WO.

Lemma start_action_linear : linear_action start_action.
Proof.
  unfold start_action, start_method. cbn.
  repeat (cbn [linear_action]; intro).
  exact I.
Qed.

Lemma start_reset_halted :
  M.find "halted" hardware_reset_state =
    Some (existT (fullType type) (SyntaxKind Bool) true).
Proof. vm_compute. reflexivity. Qed.

(** Starting from reset writes exactly the halted flag and the program
    counter, calls no other method, and the result is the state execution
    begins from. *)
Theorem start_from_reset : forall u cs ret,
  SemAction hardware_reset_state start_action u cs ret ->
  cs = M.empty _ /\ M.union u hardware_reset_state = dispatch_reset_state.
Proof.
  intros u cs ret H.
  destruct (eval_linear_action_complete _ _ _ _ _ _ start_action_linear H)
    as [He Hc].
  split; [exact Hc|].
  assert (Hu : u = M.add "halted" (existT (fullType type) (SyntaxKind Bool) false)
                     (M.add "pc"
                        (existT (fullType type) (SyntaxKind (Bit WordSz)) (natToWord WordSz 0))
                        (M.empty _))).
  { vm_compute in He. inversion He. subst. vm_compute. reflexivity. }
  subst u. unfold dispatch_reset_state.
  M.ext k. rewrite M.find_union.
  rewrite !M.F.P.F.add_o.
  destruct (M.F.P.F.eq_dec "halted" k); [subst k; reflexivity|].
  destruct (M.F.P.F.eq_dec "pc" k); [subst k; reflexivity|].
  rewrite M.find_empty. reflexivity.
Qed.

(** The call is a step of the module: from reset, the [start] method moves
    the CPU to the state execution begins from. *)
Theorem start_substep : forall u,
  SemAction hardware_reset_state start_action u (M.empty _) WO ->
  Substep thieleCore hardware_reset_state u
    (Meth (Some {| attrName := "start";
                   attrType := existT _ {| arg := Void; ret := Void |} (WO, WO) |}))
    (M.empty _).
Proof.
  intros u H.
  eapply SingleMeth with (f := start_method) (argV := WO) (retV := WO).
  - exact start_method_in.
  - exact H.
  - reflexivity.
Qed.
