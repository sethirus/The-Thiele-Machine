Require Import List.
Import ListNotations.

Lemma firstn_app_blank :
  forall (A : Type) (l : list A) (x : A),
    firstn (length l) (l ++ [x]) = l.
Proof.
  intros A l x.
  induction l as [|a l' IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Require Import TuringMachine.
Require Import ThieleCPU.

Definition encode_bin_tm_tape (tape : list TuringMachine.BinSymbol) : list nat :=
  map (fun s => match s with
                | TuringMachine.Zero => 0
                | TuringMachine.One => 1
                | TuringMachine.Blank => 2
                end) tape.

Definition encode_bin_tm_state (q : BinState) (tape : list TuringMachine.BinSymbol) : ThieleCPU.CPUStateCPU nat nat :=
  {| ThieleCPU.registers := [(0, match q with QStart => 0 | QInc => 1 | QHalt => 2 end)];
     ThieleCPU.memory := encode_bin_tm_tape tape;
     ThieleCPU.pc := 0;
     ThieleCPU.halted := if TuringMachine.BinState_eq_dec q TuringMachine.QHalt then true else false |}.

Definition decode_bin_cpu_state (st : ThieleCPU.CPUStateCPU nat nat) : (TuringMachine.BinState * list TuringMachine.BinSymbol * nat) :=
  let q :=
    match List.find (fun '(r,_) => Nat.eqb r 0) (@ThieleCPU.registers nat nat st) with
    | Some (_, 0) => TuringMachine.QStart
    | Some (_, 1) => TuringMachine.QInc
    | Some (_, 2) => TuringMachine.QHalt
    | _ => TuringMachine.QHalt
    end in
  let mem := @ThieleCPU.memory nat nat st in
  let head := @ThieleCPU.pc nat nat st in
  let mem_padded :=
    if Nat.ltb head (List.length mem) then mem
    else mem ++ repeat 2 (head - List.length mem) in
  let tape := map (fun n =>
    match n with
    | 0 => TuringMachine.Zero
    | 1 => TuringMachine.One
    | _ => TuringMachine.Blank
    end) mem_padded in
  (q, tape, head).

(* Specialized simulation relation and proof for the binary incrementer *)
Definition simulates_bin_tm
  (tm_conf : TuringMachine.BinState * list TuringMachine.BinSymbol * nat)
  (cpu : ThieleCPU.ThieleCPURecCPU nat nat ThieleCPU.SimpleInstr)
  (encode_tm_state : TuringMachine.BinState -> list TuringMachine.BinSymbol -> ThieleCPU.CPUStateCPU nat nat)
  (decode_cpu_state : ThieleCPU.CPUStateCPU nat nat -> TuringMachine.BinState * list TuringMachine.BinSymbol * nat)
  : Prop :=
  exists n : nat,
    let cpu_init := encode_tm_state (fst (fst tm_conf)) (snd (fst tm_conf)) in
    let cpu_final := ThieleCPU.step_n cpu cpu_init n in
    let '(q', tape', head') := TuringMachine.tm_step TuringMachine.bin_tm tm_conf in
    let '(q'', tape'', head'') := decode_cpu_state cpu_final in
      q' = q'' /\ head' = head'' /\ firstn (length tape') tape'' = tape'.

Lemma simple_bin_incrementer_simulation :
  let tm_conf := (TuringMachine.QStart, [TuringMachine.One], 0) in
  simulates_bin_tm
    tm_conf
    ThieleCPU.simple_cpu
    (fun q tape => encode_bin_tm_state q tape)
    decode_bin_cpu_state.
Proof.
  unfold simulates_bin_tm.
  exists 1%nat.
  simpl.
  remember (TuringMachine.tm_step TuringMachine.bin_tm (TuringMachine.QStart, [TuringMachine.One], 0)) as tm_next eqn:HTM.
  set (cpu_init := {| ThieleCPU.registers := [(0, 0)];
                      ThieleCPU.memory := [1];
                      ThieleCPU.pc := 0;
                      ThieleCPU.halted := false |}).
  pose (cpu_init).
  pose (ThieleCPU.memory nat nat cpu_init).
  remember (ThieleCPU.step_n ThieleCPU.simple_cpu cpu_init 1) as cpu_next eqn:HCPU.
  pose (ThieleCPU.memory nat nat cpu_next).
  remember (decode_bin_cpu_state cpu_next) as cpu_decoded eqn:HDEC.
  (* Manually compute and compare the values *)
  subst tm_next.
  subst cpu_decoded.
  simpl in *.
  compute in *.
  destruct ((tm_step bin_tm (QStart, [One], 0))) as [[q' tape'] head'] eqn:HTM'.
  destruct (decode_bin_cpu_state (step_n simple_cpu (encode_bin_tm_state QStart [One]) 1)) as [[q'' tape''] head''] eqn:HDEC'.
  pose tape'.
  pose tape''.
  pose head'.
  pose head''.
  pose tape'.
  pose tape''.
  pose head'.
  pose head''.
  compute in q', q'', tape', tape''.
  destruct (BinState_eq_dec q' q'') as [Heq|Hneq].
  - subst q''.
    injection HTM' as Hq' Htape' Hhead'. subst q' tape' head'.
    injection HDEC' as Htape'' Hhead''.
    subst tape''.
    compute in *.
    pose (tape' := tape').
    pose (tape'' := tape'').
    pose (head' := head').
    pose (head'' := head'').
    split; [reflexivity | split; [now compute | reflexivity]].
  - exfalso; apply Hneq; reflexivity.
Qed.
  Variable decode_cpu_state : ThieleCPU.CPUStateCPU Register Word -> (StateTM * list Symbol * nat).


Section Subsumption.


(* Simulation relation: Thiele CPU simulates a Turing machine if there exists an encoding of TM states/tape into CPU state/memory,
   and for every TM step, the CPU can perform a finite sequence of steps to match the TM's behavior. *)

Section SimulationRelation.
  Variables Symbol StateTM StateCPU Register Word : Type.
  Variable tm : TuringMachine.TM Symbol StateTM.
  Variable cpu : ThieleCPU.ThieleCPURecCPU Word Register StateCPU.

  (* Encoding functions (to be defined): *)
  Variable encode_tm_state : StateTM -> ThieleCPU.CPUState.
  Variable encode_tm_tape : list Symbol -> list Word.

  (* Simulation relation: the CPU, starting from the encoded TM configuration, can reach a state corresponding to the TM's next configuration after a finite number of steps. *)
  Definition simulates_tm
    (tm_conf : StateTM * list Symbol * nat)
    (tm : TuringMachine.TM Symbol StateTM)
    (cpu : ThieleCPU.ThieleCPU Word Register Instr)
    (encode_tm_state : StateTM -> ThieleCPU.CPUStateCPU Register Word)
    (encode_tm_tape : list Symbol -> list Word)
  : Prop :=
    let '(q, tape, head) := tm_conf in
    let cpu_init := encode_tm_state q in
    (* For some n, after n CPU steps, the CPU state corresponds to the TM's next configuration *)
    exists n : nat,
      let cpu_final := ThieleCPU.step_n cpu cpu_init n in
      let tm_conf' := decode_cpu_state cpu_final in
      (* TODO: Relate tm_conf' to the expected TM configuration after one step *)
      tm_conf' = tm_step TuringMachine.bin_tm tm_conf.
End SimulationRelation.

(* Main theorem: For every Turing machine, there exists a Thiele CPU and encodings such that the CPU simulates the TM *)
Theorem thiele_cpu_subsumes_turing :
  forall (Symbol StateTM StateCPU Register Word : Type)
         (tm : TuringMachine.TM Symbol StateTM),
    exists (cpu : ThieleCPU.ThieleCPU Word Register StateCPU)
           (encode_tm_state : StateTM -> StateCPU)
           (encode_tm_tape : list Symbol -> list Word),
      (* For every TM configuration, there is a CPU configuration simulating it *)
      forall (tm_conf : StateTM * list Symbol),
        exists (cpu_conf : StateCPU * list Word),
          simulates_tm Symbol StateTM StateCPU Register Word tm cpu encode_tm_state encode_tm_tape tm_conf cpu_conf.


End Subsumption.
