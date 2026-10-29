(** AxDgPre: the program that computes one bit about its own number, cleans up,
    and then becomes one of two given programs.

    The program V = ax_dg_V nn Pm yes no is laid out as

      lines 1..3          move register 1 (the input x) into register RX = N,
                          where N = nn + 3 is the number of counters of the MMA
                          program;
      lines 4..3+lp       the MMA program Pm as a host program, moved down;
      then N-1 lines      empty registers 1 .. N-1 (the program leaves its
                          working counters dirty);
      then 3 lines        move RX back into register 1;
      one line            DEC 0 (the first line of yes): the bit in register 0
                          decides, a 1 jumps to yes, a 0 falls into no;
      the block no, moved down;
      one line            HALT;
      the block yes, moved down, last.

    The MMA program is run from a state that has c in register 2 and 0 in
    register 1, and puts a bit in register 0.  Everything it did to the
    registers is undone before the choice, so that the program enters yes or
    no in a state that has x in register 1, every other register 0, no fact,
    no channel, no trap, ledger 0 and flag down.  Only the versions of the
    registers differ from a start; AxDgBlock.v handles those.

    Results (all closed):

      ax_dg_prelude   if the MMA program, from the vector (0, 0, c, 0, ...),
                      outputs 0 in register 0, then from the state that the
                      s-m-n prefix leaves (c in register 2, x in register 1,
                      program counter put to 1) the program reaches a clean
                      state at the first line of no, and with output 1 at the
                      first line of yes; in both the registers are those of the
                      start on x;
      ax_dg_embeds_no, ax_dg_embeds_yes, ax_dg_exit_no, ax_dg_exit_yes
                      the two blocks sit where AxDgBlock.v needs them. *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is recursion theory on the multi-register host machine (the layout of the program that the diagonal builds), built for
   the content diagonal of AxDgFixed.v. That file connects it to the axis
   (AxCore.v); the host machine's link to the abstract record lives in
   UniversalInterpreterLinks.v. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Undecidability.Shared.Libs.DLW.Vec Require Import pos vec.
From Undecidability.Shared.Libs.DLW.Code Require Import subcode sss.
From Undecidability.MinskyMachines Require Import MM MMA.
From Undecidability.MinskyMachines.MMA Require Import mma_defs.
Require Minimal.EarnedMulti Minimal.UniversalCodes.
Require Import Minimal.SmHostBlocks Minimal.SmCodes Minimal.SmInterp Kernel.SmMMAHost Kernel.SmNoExact
  Kernel.SmHostRice Kernel.SmKleene.
From Minimal Require Import AxDgBlock.
From Kernel Require Import AxDgLoops.
Module M := Minimal.EarnedMulti.
Module UC := Minimal.UniversalCodes.
Unset Implicit Arguments.

Local Notation hinstr := (@M.instr UC.hprop).
Local Notation hcore := (@M.core UC.hprop).
Local Notation hstate := (@M.state UC.hprop).
Local Notation hstep := (M.step UC.hprop_eqb UC.heval).
Local Notation hrun_prog := (M.run_prog UC.hprop_eqb UC.heval).


(** * 0. Small helpers *)

Lemma ax_dg_seq : forall (Q : list hinstr) s (P R : hstate -> Prop),
  (exists n, P (hrun_prog n Q s)) ->
  (forall s', P s' -> exists n, R (hrun_prog n Q s')) ->
  exists n, R (hrun_prog n Q s).
Proof.
  intros Q s P R [n1 H1] HR. destruct (HR _ H1) as [n2 H2].
  exists (n1 + n2). rewrite sm_run_add. exact H2.
Qed.

Lemma ax_dg_rj_one : forall off len, sm_rj off len 1 = S off.
Proof. intros off len. unfold sm_rj. destruct len as [| len]; reflexivity. Qed.

Lemma ax_dg_plain_run : forall (B : list hinstr),
  (forall i, In i B -> M.plain i = true) ->
  forall n s,
    M.facts (M.core_of (hrun_prog n B s)) = M.facts (M.core_of s) /\
    M.chan (M.core_of (hrun_prog n B s)) = M.chan (M.core_of s) /\
    M.err (M.core_of (hrun_prog n B s)) = M.err (M.core_of s) /\
    M.mu (hrun_prog n B s) = M.mu s /\ M.cert (hrun_prog n B s) = M.cert s.
Proof.
  intros B HB n. induction n as [| n IH]; intros s; [auto |].
  rewrite sm_run_succ. destruct (IH (hstep B s)) as (H1 & H2 & H3 & H4 & H5).
  rewrite H1, H2, H3, H4, H5. unfold M.step.
  destruct (M.next_instr B (M.core_of s)) as [i |] eqn:Hn; [| auto].
  destruct (sm_plain_exec UC.hprop_eqb UC.heval s i (HB i (sm2_next_in B _ i Hn)))
    as (G1 & G2 & G3 & G4 & G5).
  auto.
Qed.

(** A plain program that has stopped, without a trap, has its counter outside
    the program. *)
Lemma ax_dg_halted_out : forall (B : list hinstr) (k : hcore),
  (forall i, In i B -> M.plain i = true) ->
  M.halted B k -> M.err k = false -> ~ (1 <= M.pc k <= length B).
Proof.
  intros B k HB Hh He [H1 H2]. unfold M.halted, M.next_instr in Hh. rewrite He in Hh.
  destruct (M.pc k) as [| p]; [lia |]. cbn [M.fetch] in Hh.
  assert (Hlt : p < length B) by lia.
  destruct (nth_error B p) as [i |] eqn:E.
  - assert (Hi : In i B) by (eapply nth_error_In; exact E).
    pose proof (HB i Hi) as Hpl. destruct i; simpl in Hpl; try discriminate; discriminate Hh.
  - apply nth_error_None in E. lia.
Qed.

(** * 1. The layout *)

Section Layout.

Variable nn : nat.
Variable Pm : list (mm_instr (pos (S (S (S nn))))).
Variable yes no : list hinstr.

Definition ax_dg_N : nat := S (S (S nn)).
Definition ax_dg_RX : nat := ax_dg_N.
Definition ax_dg_Pre : list hinstr := sm_mma_host (S (S (S nn))) Pm.
Definition ax_dg_lp : nat := length Pm.
Definition ax_dg_base : nat := 3 + ax_dg_lp.
Definition ax_dg_Ld : nat := ax_dg_base + ax_dg_N.
Definition ax_dg_Le : nat := ax_dg_Ld + 3.
Definition ax_dg_offN : nat := ax_dg_Le.
Definition ax_dg_offY : nat := ax_dg_offN + length no + 1.

Definition ax_dg_A : list hinstr := [M.INC ax_dg_RX; M.DEC 1 1; M.DEC ax_dg_RX 4].
Definition ax_dg_Cl : list hinstr :=
  map (fun i => M.DEC i (ax_dg_base + i)) (seq 1 (ax_dg_N - 1)).
Definition ax_dg_D : list hinstr := [M.INC 1; M.DEC ax_dg_RX ax_dg_Ld; M.DEC 1 (ax_dg_Ld + 3)].
Definition ax_dg_E : hinstr := M.DEC 0 (S ax_dg_offY).

Definition ax_dg_Pfx : list hinstr :=
  ax_dg_A ++ sm_reloc 3 ax_dg_Pre ++ ax_dg_Cl ++ ax_dg_D ++ [ax_dg_E].

Definition ax_dg_V : list hinstr :=
  ax_dg_Pfx ++ sm_reloc ax_dg_offN no ++ M.HALT :: sm_reloc ax_dg_offY yes.

Lemma ax_dg_lp_len : length ax_dg_Pre = ax_dg_lp.
Proof. unfold ax_dg_Pre, ax_dg_lp, sm_mma_host, sm_mma_prog. rewrite !map_length. reflexivity. Qed.

Lemma ax_dg_Cl_len : length ax_dg_Cl = ax_dg_N - 1.
Proof. unfold ax_dg_Cl. rewrite map_length, seq_length. reflexivity. Qed.

Lemma ax_dg_Pfx_len : length ax_dg_Pfx = ax_dg_Le.
Proof.
  unfold ax_dg_Pfx. rewrite !app_length, sm_reloc_length, ax_dg_lp_len, ax_dg_Cl_len.
  unfold ax_dg_A, ax_dg_D, ax_dg_Le, ax_dg_Ld, ax_dg_base, ax_dg_N. simpl. lia.
Qed.

Lemma ax_dg_V_len : length ax_dg_V = ax_dg_offY + length yes.
Proof.
  unfold ax_dg_V. rewrite !app_length, sm_reloc_length, ax_dg_Pfx_len. simpl.
  rewrite sm_reloc_length. unfold ax_dg_offY, ax_dg_offN. lia.
Qed.

(** Fetching from the prefix. *)
Lemma ax_dg_fetch_pfx : forall n, n <= ax_dg_Le -> M.fetch ax_dg_V n = M.fetch ax_dg_Pfx n.
Proof.
  intros n Hn. unfold ax_dg_V. apply sm_fetch_app_left. rewrite ax_dg_Pfx_len. exact Hn.
Qed.

Lemma ax_dg_fetch_app_right : forall (X Y : list hinstr) n,
  length X < n -> M.fetch (X ++ Y) n = M.fetch Y (n - length X).
Proof.
  intros X Y n Hn. destruct n as [| n]; [lia |].
  replace (S n - length X) with (S (n - length X)) by lia.
  cbn [M.fetch]. rewrite nth_error_app2 by lia. reflexivity.
Qed.

Lemma ax_dg_fetch_A : forall n, 1 <= n <= 3 -> M.fetch ax_dg_V n = M.fetch ax_dg_A n.
Proof.
  intros n Hn. rewrite ax_dg_fetch_pfx.
  - unfold ax_dg_Pfx. apply sm_fetch_app_left. unfold ax_dg_A. simpl. lia.
  - unfold ax_dg_Le, ax_dg_Ld, ax_dg_base, ax_dg_N. lia.
Qed.

Lemma ax_dg_fetch_Cl : forall i, 1 <= i <= ax_dg_N - 1 ->
  M.fetch ax_dg_V (ax_dg_base + i) = Some (M.DEC i (ax_dg_base + i)).
Proof.
  intros i Hi. rewrite ax_dg_fetch_pfx.
  - unfold ax_dg_Pfx.
    rewrite (app_assoc ax_dg_A (sm_reloc 3 ax_dg_Pre) (ax_dg_Cl ++ ax_dg_D ++ [ax_dg_E])).
    rewrite ax_dg_fetch_app_right.
    + rewrite app_length, sm_reloc_length, ax_dg_lp_len.
      replace (ax_dg_base + i - (length ax_dg_A + ax_dg_lp)) with i.
      * rewrite sm_fetch_app_left by (rewrite ax_dg_Cl_len; lia).
        unfold ax_dg_Cl. destruct i as [| i']; [lia |]. cbn [M.fetch].
        rewrite nth_error_map. rewrite (nth_error_nth' _ (0 : nat)) by (rewrite seq_length; lia).
        rewrite seq_nth by lia. simpl. f_equal.
      * unfold ax_dg_base, ax_dg_A. simpl. lia.
    + rewrite app_length, sm_reloc_length, ax_dg_lp_len. unfold ax_dg_base, ax_dg_A. simpl. lia.
  - unfold ax_dg_Le, ax_dg_Ld, ax_dg_base, ax_dg_N in *. lia.
Qed.

Lemma ax_dg_fetch_D : forall j, 0 <= j <= 2 ->
  M.fetch ax_dg_V (ax_dg_Ld + j) = nth_error ax_dg_D j.
Proof.
  intros j Hj. rewrite ax_dg_fetch_pfx by (unfold ax_dg_Le; lia).
  unfold ax_dg_Pfx.
  rewrite (app_assoc (sm_reloc 3 ax_dg_Pre) ax_dg_Cl (ax_dg_D ++ [ax_dg_E])).
  rewrite (app_assoc ax_dg_A (sm_reloc 3 ax_dg_Pre ++ ax_dg_Cl) (ax_dg_D ++ [ax_dg_E])).
  rewrite ax_dg_fetch_app_right.
  - rewrite !app_length, sm_reloc_length, ax_dg_lp_len, ax_dg_Cl_len.
    replace (ax_dg_Ld + j - (length ax_dg_A + (ax_dg_lp + (ax_dg_N - 1)))) with (S j).
    + rewrite sm_fetch_app_left by (unfold ax_dg_D; simpl; lia).
      destruct j as [| [| [| j]]]; try reflexivity; try lia.
    + unfold ax_dg_Ld, ax_dg_base, ax_dg_A, ax_dg_N. simpl. lia.
  - rewrite !app_length, sm_reloc_length, ax_dg_lp_len, ax_dg_Cl_len.
    unfold ax_dg_Ld, ax_dg_base, ax_dg_A, ax_dg_N. simpl. lia.
Qed.

Lemma ax_dg_fetch_E : M.fetch ax_dg_V ax_dg_Le = Some ax_dg_E.
Proof.
  unfold ax_dg_V. rewrite sm_fetch_app_left by (rewrite ax_dg_Pfx_len; lia).
  unfold ax_dg_Pfx.
  rewrite (app_assoc ax_dg_Cl ax_dg_D [ax_dg_E]).
  rewrite (app_assoc (sm_reloc 3 ax_dg_Pre) (ax_dg_Cl ++ ax_dg_D) [ax_dg_E]).
  rewrite (app_assoc ax_dg_A (sm_reloc 3 ax_dg_Pre ++ ax_dg_Cl ++ ax_dg_D) [ax_dg_E]).
  rewrite ax_dg_fetch_app_right.
  - replace (ax_dg_Le - length (ax_dg_A ++ sm_reloc 3 ax_dg_Pre ++ ax_dg_Cl ++ ax_dg_D)) with 1.
    + reflexivity.
    + rewrite !app_length, sm_reloc_length, ax_dg_lp_len, ax_dg_Cl_len.
      unfold ax_dg_Le, ax_dg_Ld, ax_dg_base, ax_dg_N, ax_dg_A, ax_dg_D. simpl. lia.
  - rewrite !app_length, sm_reloc_length, ax_dg_lp_len, ax_dg_Cl_len.
    unfold ax_dg_Le, ax_dg_Ld, ax_dg_base, ax_dg_N, ax_dg_A, ax_dg_D. simpl. lia.
Qed.

(** The three blocks sit inside V. *)
Lemma ax_dg_embeds_pre : sm_embeds ax_dg_V ax_dg_Pre 3.
Proof.
  unfold ax_dg_V, ax_dg_Pfx. rewrite <- !app_assoc.
  replace 3 with (length ax_dg_A) by reflexivity.
  apply sm_embeds_app.
Qed.

Lemma ax_dg_embeds_no : sm_embeds ax_dg_V no ax_dg_offN.
Proof.
  unfold ax_dg_V.
  pose proof (sm_embeds_app ax_dg_Pfx no (M.HALT :: sm_reloc ax_dg_offY yes)) as H.
  rewrite ax_dg_Pfx_len in H. exact H.
Qed.

Lemma ax_dg_embeds_yes : sm_embeds ax_dg_V yes ax_dg_offY.
Proof.
  unfold ax_dg_V.
  set (Z := ax_dg_Pfx ++ sm_reloc ax_dg_offN no ++ [M.HALT]).
  assert (Hz : length Z = ax_dg_offY).
  { unfold Z. rewrite !app_length, sm_reloc_length, ax_dg_Pfx_len. cbn [length].
    unfold ax_dg_offY, ax_dg_offN. lia. }
  assert (HV : ax_dg_Pfx ++ sm_reloc ax_dg_offN no ++ M.HALT :: sm_reloc ax_dg_offY yes
               = Z ++ sm_reloc (length Z) yes ++ []).
  { rewrite Hz. unfold Z. rewrite <- !app_assoc. simpl. rewrite app_nil_r. try reflexivity. }
  rewrite HV. rewrite <- Hz. apply sm_embeds_app.
Qed.

Lemma ax_dg_exit_no : M.fetch ax_dg_V (S (length no + ax_dg_offN)) = Some M.HALT.
Proof.
  unfold ax_dg_V. rewrite ax_dg_fetch_app_right.
  - replace (S (length no + ax_dg_offN) - length ax_dg_Pfx) with (S (length no)).
    + rewrite ax_dg_fetch_app_right.
      * rewrite sm_reloc_length. replace (S (length no) - length no) with 1 by lia. reflexivity.
      * rewrite sm_reloc_length. lia.
    + rewrite ax_dg_Pfx_len. unfold ax_dg_offN. lia.
  - rewrite ax_dg_Pfx_len. unfold ax_dg_offN. lia.
Qed.

Lemma ax_dg_exit_yes : M.fetch ax_dg_V (S (length yes + ax_dg_offY)) = None.
Proof. apply sm_fetch_out. rewrite ax_dg_V_len. lia. Qed.

End Layout.
