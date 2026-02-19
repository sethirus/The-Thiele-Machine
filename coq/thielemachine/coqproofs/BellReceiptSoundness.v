From Coq Require Import List String Ascii Bool.
Import ListNotations.
Open Scope string_scope.

From ThieleMachine Require Import BellReceiptSemantics.
From ThieleMachine Require Import BellInequality.
From ThieleMachine Require Import ThieleMachineConcrete.

(** Receipt soundness for CHSH.

    Goal: any CHSH trial decoded from receipt metadata must correspond to an
    actual [CHSH_TRIAL x y a b] witness step, and the decoded bits are the ones
    carried by that opcode.

    This is the bridge from “origin is non-forgeable” to “measurement channel is
    sound”: you can’t smuggle malformed trials through unrelated steps.
*)

Definition bit_of_nat01 (n : nat) : Bit :=
  if Nat.eqb n 0 then B0 else B1.

Definition trial_of_nat_params (x y a b : nat) : option Trial :=
  if (is_bit_nat x && is_bit_nat y && is_bit_nat a && is_bit_nat b)%bool then
    Some {| t_x := bit_of_nat01 x;
            t_y := bit_of_nat01 y;
            t_a := bit_of_nat01 a;
            t_b := bit_of_nat01 b |}
  else None.

(** [is_bit_nat_true_cases]: formal specification. *)
Lemma is_bit_nat_true_cases :
  forall n, is_bit_nat n = true -> n = 0 \/ n = 1.
Proof.
  intros n H.
  destruct n as [|n].
  - left; reflexivity.
  - destruct n as [|n].
    + right; reflexivity.
    + unfold is_bit_nat in H.
      simpl in H.
      discriminate.
Qed.

(** [andb4_true]: formal specification. *)
Lemma andb4_true :
  forall b1 b2 b3 b4,
    (b1 && b2 && b3 && b4)%bool = true ->
    b1 = true /\ b2 = true /\ b3 = true /\ b4 = true.
Proof.
  intros b1 b2 b3 b4 H.
  destruct b1, b2, b3, b4; simpl in H; try discriminate; repeat split; reflexivity.
Qed.

(** [trial_of_metadata_cert_for_chsh_trial]: formal specification. *)
Lemma trial_of_metadata_cert_for_chsh_trial :
  forall x y a b,
    is_bit_nat x = true ->
    is_bit_nat y = true ->
    is_bit_nat a = true ->
    is_bit_nat b = true ->
    trial_of_metadata (cert_for_chsh_trial x y a b).(metadata) =
      Some {| t_x := bit_of_nat01 x;
              t_y := bit_of_nat01 y;
              t_a := bit_of_nat01 a;
              t_b := bit_of_nat01 b |}.
Proof.
  intros x y a b Hx Hy Ha Hb.
  unfold trial_of_metadata.
  (* Reduce the prefix/length checks, then compute the 4-char payload decode. *)
  cbn.
  (* Use the 0/1 cases to avoid the “any nonzero maps to '1'” ambiguity. *)
  destruct (is_bit_nat_true_cases x Hx) as [Hx0 | Hx1];
  destruct (is_bit_nat_true_cases y Hy) as [Hy0 | Hy1];
  destruct (is_bit_nat_true_cases a Ha) as [Ha0 | Ha1];
  destruct (is_bit_nat_true_cases b Hb) as [Hb0 | Hb1];
  subst; vm_compute; reflexivity.
Qed.

(** [trial_of_metadata_concrete_step]: formal specification. *)
Lemma trial_of_metadata_concrete_step :
  forall instr s,
    trial_of_metadata ((concrete_step instr s).(observation).(cert).(metadata)) =
      match instr with
      | CHSH_TRIAL x y a b => trial_of_nat_params x y a b
      | _ => None
      end.
Proof.
  intros instr s.
  destruct instr; cbn.
  - (* LASSERT *) vm_compute. reflexivity.
  - (* MDLACC *) vm_compute. reflexivity.
  - (* PNEW *) vm_compute. reflexivity.
  - (* PYEXEC *)
    (* cert_for_pyexec always leaves metadata empty in this model. *)
    rewrite cert_for_pyexec_metadata_empty.
    vm_compute. reflexivity.
  - (* CHSH_TRIAL *)
    unfold trial_of_nat_params.
    destruct (is_bit_nat n && is_bit_nat n0 && is_bit_nat n1 && is_bit_nat n2)%bool eqn:Hbits.
    + (* Well-formed bits: concrete_step emits cert_for_chsh_trial. *)
      destruct (andb4_true (is_bit_nat n) (is_bit_nat n0) (is_bit_nat n1) (is_bit_nat n2) Hbits)
        as [Hx [Hy [Ha Hb]]].
      destruct (is_bit_nat_true_cases n Hx) as [Hn|Hn];
      destruct (is_bit_nat_true_cases n0 Hy) as [Hn0|Hn0];
      destruct (is_bit_nat_true_cases n1 Ha) as [Hn1|Hn1];
      destruct (is_bit_nat_true_cases n2 Hb) as [Hn2|Hn2];
      subst; vm_compute; reflexivity.
    + (* Ill-formed bits: concrete_step emits default_cert, whose metadata is empty. *)
      vm_compute. reflexivity.
  - (* EMIT *) vm_compute. reflexivity.
Qed.

Fixpoint trials_of_concrete_receipts (rs : list ConcreteReceipt) : list Trial :=
  match rs with
  | [] => []
  | r :: tl =>
      match trial_of_metadata (r.(receipt_obs).(cert).(metadata)) with
      | Some t => t :: trials_of_concrete_receipts tl
      | None => trials_of_concrete_receipts tl
      end
  end.

Fixpoint trials_of_prog (prog : list ThieleInstr) : list Trial :=
  match prog with
  | [] => []
  | instr :: tl =>
      match instr with
      | CHSH_TRIAL x y a b =>
          match trial_of_nat_params x y a b with
          | Some t => t :: trials_of_prog tl
          | None => trials_of_prog tl
          end
      | _ => trials_of_prog tl
      end
  end.

(** [trials_of_concrete_receipts_of]: formal specification. *)
Theorem trials_of_concrete_receipts_of :
  forall s prog,
    trials_of_concrete_receipts (concrete_receipts_of s prog) =
    trials_of_prog prog.
Proof.
  intros s prog.
  revert s.
  induction prog as [|instr tl IH]; intros s; simpl; auto.
  cbn.
  (* Head receipt’s metadata is exactly the step metadata. *)
  rewrite trial_of_metadata_concrete_step.
  destruct instr; cbn.
  - (* LASSERT *) apply IH.
  - (* MDLACC *) apply IH.
  - (* PNEW *) apply IH.
  - (* PYEXEC *) apply IH.
  - (* CHSH_TRIAL *)
    destruct (trial_of_nat_params n n0 n1 n2) eqn:Ht; cbn;
      rewrite IH; reflexivity.
  - (* EMIT *) apply IH.
Qed.

(** [trials_from_concrete_receipts_are_sound]: formal specification. *)
Theorem trials_from_concrete_receipts_are_sound :
  forall instr s t,
    trial_of_metadata ((concrete_step instr s).(observation).(cert).(metadata)) = Some t ->
    exists x y a b,
      instr = CHSH_TRIAL x y a b /\
      is_bit_nat x = true /\ is_bit_nat y = true /\ is_bit_nat a = true /\ is_bit_nat b = true /\
      t = {| t_x := bit_of_nat01 x;
             t_y := bit_of_nat01 y;
             t_a := bit_of_nat01 a;
             t_b := bit_of_nat01 b |}.
Proof.
  intros instr s t Ht.
  rewrite trial_of_metadata_concrete_step in Ht.
  destruct instr; try discriminate.
  unfold trial_of_nat_params in Ht.
  destruct (is_bit_nat n && is_bit_nat n0 && is_bit_nat n1 && is_bit_nat n2)%bool eqn:Hbits;
    try discriminate.
  inversion Ht; subst.
  destruct (andb4_true (is_bit_nat n) (is_bit_nat n0) (is_bit_nat n1) (is_bit_nat n2) Hbits)
    as [Hx [Hy [Ha Hb]]].
  exists n, n0, n1, n2.
  repeat split; try reflexivity; try assumption.
Qed.
