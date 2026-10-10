(** LiftMacro.v: the two-counter presentation of clause (a) loses nothing.

    Clause (a) of ThieleComplete.v asks for one move per two-counter
    instruction, and LiftConverse.v shows a box with finitely many levers
    (a fixed table) has no such base [lift_finite_moves_not_a_base]. This
    file states clause (a) by simulation instead and proves the two forms
    agree once moves are grouped.

      sim_base M0           a base by simulation: a window reading a
                            two-counter configuration off the state (any
                            encoding), a class of live states, for each
                            two-counter instruction a finite LIST of the box's
                            own moves, and a loaded live state for each start,
                            such that from every live state the list acts on
                            the window exactly as the instruction acts on a
                            configuration and keeps the state live.

      macro_machine M0      the same box whose moves are finite lists of its
                            moves, a list run in order.

      ub_to_sim             every universal base is a base by simulation
                            (each list has one move).
      sim_to_macro_ub       every base by simulation is a universal base of
                            the macro machine.
      sim_macro_runs        the macro machine's runs are the box's runs: a
                            list of lists runs as their concatenation.
      sim_base_lifts        so every base by simulation lifts: the lift of
                            its macro machine, with the window claims, is
                            Thiele-complete.

      The witness that the gap is real: fl_box, a box with four levers
      (increment A, increment B, add one to a jump target, and
      decrement-A-or-B-and-jump-to-the-target), has a base by simulation
      [fl_sim_base], has no universal base [fl_no_universal_base], and its
      macro machine lifts to a Thiele-complete machine [fl_macro_lifts].

    What this does not do: it does not give a fixed-table Turing machine
    with a tape. The four-lever box is a register box; it shows that a
    finite lever set is not what fails, the one-move-per-instruction
    presentation is.

    Dependencies: ThieleComplete.v, LiftCore.v, LiftConverse.v. No axioms,
    no Admitted. *)

From Coq Require Import List Arith Lia.
Import ListNotations.
Require Minimal.ThieleComplete.
Module T := Minimal.ThieleComplete.
From Minimal Require Import LiftCore LiftConverse.

(* ================================================================= *)
(* Clause (a) by simulation.                                          *)
(* ================================================================= *)

Record sim_base (M0 : T.machine) : Type := mk_sb {
  sb_window : T.m_state M0 -> T.cm_conf;
  sb_live : T.m_state M0 -> Prop;
  sb_compile : T.cm_instr -> list (T.m_move M0);
  sb_load : nat -> nat -> T.m_state M0;
  sb_load_window : forall a b, sb_window (sb_load a b) = (1, (a, b));
  sb_load_live : forall a b, sb_live (sb_load a b);
  sb_sim : forall s i, sb_live s ->
    sb_window (T.run M0 (sb_compile i) s) = T.cm_exec i (sb_window s) /\
    sb_live (T.run M0 (sb_compile i) s)
}.

Arguments sb_window {M0} _ _.
Arguments sb_live {M0} _ _.
Arguments sb_compile {M0} _ _.
Arguments sb_load {M0} _ _ _.
Arguments sb_load_window {M0} _ _ _.
Arguments sb_load_live {M0} _ _ _.
Arguments sb_sim {M0} _ _ _ _.

Fixpoint sum_costs (M0 : T.machine) (l : list (T.m_move M0)) : nat :=
  match l with [] => 0 | m :: r => T.m_cost M0 m + sum_costs M0 r end.

(* The box with its moves grouped into finite lists. *)
Definition macro_machine (M0 : T.machine) : T.machine :=
  T.mk_machine (T.m_state M0) (list (T.m_move M0)) (fun s l => T.run M0 l s)
    (sum_costs M0) (T.m_record M0).

Theorem sim_macro_runs : forall M0 (ls : list (list (T.m_move M0))) s,
  T.run (macro_machine M0) ls s = T.run M0 (concat ls) s.
Proof.
  intros M0 ls. induction ls as [| l ls IH]; intro s; simpl; [reflexivity |].
  rewrite IH, T.run_app. reflexivity.
Qed.

(* A universal base is a base by simulation, one move per list. *)
Definition ub_to_sim {M0} (U : T.universal_base M0) : sim_base M0.
Proof.
  refine (mk_sb M0 (T.ub_window U) (T.ub_live U) (fun i => [T.ub_compile U i])
            (T.ub_load U) (T.ub_load_window U) (T.ub_load_live U) _).
  intros s i Hl. simpl. exact (T.ub_sim U s i Hl).
Defined.

(* A base by simulation is a universal base of the macro machine. *)
Definition sim_to_macro_ub {M0} (B : sim_base M0) : T.universal_base (macro_machine M0) :=
  T.mk_ub (macro_machine M0) (sb_window B) (sb_live B) (sb_compile B) (sb_load B)
    (sb_load_window B) (sb_load_live B) (sb_sim B).

Theorem ub_to_sim_inhabited : forall M0,
  inhabited (T.universal_base M0) -> inhabited (sim_base M0).
Proof. intros M0 [U]. exact (inhabits (ub_to_sim U)). Qed.

Theorem sim_to_macro_inhabited : forall M0,
  inhabited (sim_base M0) -> inhabited (T.universal_base (macro_machine M0)).
Proof. intros M0 [B]. exact (inhabits (sim_to_macro_ub B)). Qed.

(* Every base by simulation lifts: the lift of the macro machine with the
   window claims is Thiele-complete, for every cap of at least 1. *)
Theorem sim_base_lifts : forall M0 (B : sim_base M0) cap,
  0 < cap ->
  T.thiele_complete
    (lift_machine (macro_machine M0) (lift_window_lang (macro_machine M0) (sim_to_macro_ub B)) cap).
Proof.
  intros M0 B cap Hcap. apply lift_window_thiele_complete. exact Hcap.
Qed.

(* ================================================================= *)
(* A box with four levers.                                            *)
(* ================================================================= *)

(* State: (line, (A, B), jump target). *)
Definition fl_state : Type := (T.cm_conf * nat)%type.

Inductive fl_lever : Type :=
| FL_INC (r : T.reg)     (* add one to r, go to the next line *)
| FL_TGT                  (* add one to the jump target *)
| FL_DEC (r : T.reg).    (* if r is above 0, take one off and jump to the
                             target; else go to the next line; the target
                             goes back to 0 either way *)

Definition fl_step (s : fl_state) (m : fl_lever) : fl_state :=
  let '(x, t) := s in
  match m with
  | FL_INC r => (T.cm_exec (T.CINC r) x, 0)
  | FL_TGT => (x, S t)
  | FL_DEC r => (T.cm_exec (T.CDEC r t) x, 0)
  end.

Definition fl_box : T.machine :=
  T.mk_machine fl_state fl_lever fl_step (fun _ => 0) (fun _ => false).

Lemma fl_run_tgt : forall n x t,
  T.run fl_box (repeat FL_TGT n) (x, t) = (x, n + t).
Proof.
  induction n as [| n IH]; intros x t; simpl; [reflexivity |].
  rewrite IH. f_equal. lia.
Qed.

Definition fl_compile (i : T.cm_instr) : list fl_lever :=
  match i with
  | T.CINC r => [FL_INC r]
  | T.CDEC r j => repeat FL_TGT j ++ [FL_DEC r]
  end.

Definition fl_sim_base : sim_base fl_box.
Proof.
  refine (mk_sb fl_box fst (fun s => snd s = 0) fl_compile
            (fun a b => ((1, (a, b)), 0)) (fun a b => eq_refl) (fun a b => eq_refl) _).
  intros [x t] i Hl. simpl in Hl. subst t. destruct i as [r | r j]; simpl.
  - split; reflexivity.
  - rewrite T.run_app, fl_run_tgt. simpl. rewrite Nat.add_0_r. split; reflexivity.
Defined.

Definition fl_index (m : fl_lever) : nat :=
  match m with
  | FL_INC T.RA => 0 | FL_INC T.RB => 1 | FL_TGT => 2
  | FL_DEC T.RA => 3 | FL_DEC T.RB => 4
  end.

Theorem fl_no_universal_base : ~ inhabited (T.universal_base fl_box).
Proof.
  intro H. apply (lift_finite_moves_not_a_base fl_box 5 fl_index); [| | exact H].
  - intros [[|] | | [|]]; simpl; lia.
  - intros [[|] | | [|]] [[|] | | [|]]; simpl; intro E; try discriminate; reflexivity.
Qed.

Theorem fl_has_sim_base : inhabited (sim_base fl_box).
Proof. exact (inhabits fl_sim_base). Qed.

Theorem fl_macro_lifts : forall cap, 0 < cap ->
  T.thiele_complete
    (lift_machine (macro_machine fl_box)
       (lift_window_lang (macro_machine fl_box) (sim_to_macro_ub fl_sim_base)) cap).
Proof. intros cap Hcap. apply sim_base_lifts. exact Hcap. Qed.

Print Assumptions sim_macro_runs.
Print Assumptions ub_to_sim_inhabited.
Print Assumptions sim_to_macro_inhabited.
Print Assumptions sim_base_lifts.
Print Assumptions fl_has_sim_base.
Print Assumptions fl_no_universal_base.
Print Assumptions fl_macro_lifts.
