From Coq Require Import List Bool Arith.PeanoNat ZArith.
From Coq Require Import Strings.String Strings.Ascii.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(** CertCheck: Certificate verification for SAT/UNSAT claims

    When the VM claims "this formula is SAT" or "this formula is UNSAT", it
    has to provide a certificate anyone can check. Saying "I computed X"
    without proof is worthless. I don't believe my own claims unless I can
    verify them mechanically — that's what this file is.

    Two problems:
    1. SAT: Certificate = satisfying assignment. Verification = substitute,
       check all clauses true.
    2. UNSAT: Certificate = LRAT proof. Verification = check RUP (Reverse
       Unit Propagation) steps.

    Formats: DIMACS CNF for formulas, space-separated variable assignments
    for SAT certificates, LRAT for UNSAT proofs.

    This Coq code is the canonical specification. It's extracted to OCaml
    (build/thiele_core.ml) — same parsing, same checks, same outputs. If the
    OCaml extraction accepts, Coq accepts. If Coq rejects, the extraction
    rejects. They're the same thing looked at differently.

    If you find a formula and assignment where this checker says SAT but the
    formula isn't satisfied — or an LRAT proof this checker accepts but the
    formula is actually SAT — the cross-layer parity tests will catch it.
*)

Module CertCheck.

  (** String/list utilities: split on whitespace, trim, walk by ASCII.
      Certificate formats are text-based (DIMACS, LRAT), so I need basic
      string primitives. These are pure functional walks on ASCII character
      lists — deterministic and formal, no external libraries. Everything
      below (DIMACS parser, LRAT parser, assignment parser) bottoms out here. *)

  Fixpoint string_to_list (s : string) : list ascii :=
    match s with
    | EmptyString => []
    | String c s' => c :: string_to_list s'
    end.

  Fixpoint list_to_string (l : list ascii) : string :=
    match l with
    | [] => EmptyString
    | c :: l' => String c (list_to_string l')
    end.

  Definition ascii_nat (c : ascii) : nat := nat_of_ascii c.

  Definition is_space (c : ascii) : bool :=
    match ascii_nat c with
    | 9%nat (* \t *) => true
    | 10%nat (* \n *) => true
    | 13%nat (* \r *) => true
    | 32%nat (* space *) => true
    | _ => false
    end.

  Fixpoint trim_left_list (l : list ascii) : list ascii :=
    match l with
    | [] => []
    | c :: l' => if is_space c then trim_left_list l' else l
    end.

  Definition trim_left (s : string) : string :=
    list_to_string (trim_left_list (string_to_list s)).

  Fixpoint split_lines_aux (l : list ascii) (cur : list ascii) : list (list ascii) :=
    match l with
    | [] => [rev cur]
    | c :: l' =>
        if Nat.eqb (ascii_nat c) 10%nat (* \n *) then
          rev cur :: split_lines_aux l' []
        else
          split_lines_aux l' (c :: cur)
    end.

  Definition split_lines (s : string) : list string :=
    map list_to_string (split_lines_aux (string_to_list s) []).

  Fixpoint split_ws_aux (l : list ascii) (cur : list ascii) : list (list ascii) :=
    match l with
    | [] =>
        match rev cur with
        | [] => []
        | tok => [tok]
        end
    | c :: l' =>
        if is_space c then
          match rev cur with
          | [] => split_ws_aux l' []
          | tok => tok :: split_ws_aux l' []
          end
        else
          split_ws_aux l' (c :: cur)
    end.

  Definition split_ws (s : string) : list string :=
    map list_to_string (split_ws_aux (string_to_list s) []).

  Definition starts_with_char (ch : ascii) (s : string) : bool :=
    match trim_left s with
    | EmptyString => false
    | String c _ => Ascii.eqb c ch
    end.

  (** Integer parsing: ASCII decimal strings → Coq Z/nat.
      DIMACS uses integers for literals; LRAT uses them for clause IDs.
      Standard decimal with optional '+'/'-' prefix — e.g. "42", "-7", "+3".
      parse_int "0" = Some 0, parse_int "-123" = Some (-123)%Z,
      malformed input = None. *)

  Definition is_digit (c : ascii) : bool :=
    let n := ascii_nat c in
    Nat.leb 48 n && Nat.leb n 57.

  Fixpoint parse_nat_digits (l : list ascii) (acc : nat) : option nat :=
    match l with
    | [] => Some acc
    | c :: l' =>
        if is_digit c then
          let d := Nat.sub (ascii_nat c) 48 in
          parse_nat_digits l' (Nat.add (Nat.mul 10 acc) d)
        else None
    end.

  Definition parse_int (s : string) : option Z :=
    let l := string_to_list (trim_left s) in
    match l with
    | [] => None
    | c :: rest =>
        if Ascii.eqb c (Ascii.ascii_of_nat 45) (* '-' *) then
          match parse_nat_digits rest 0 with
          | Some n => Some (- (Z.of_nat n))
          | None => None
          end
        else if Ascii.eqb c (Ascii.ascii_of_nat 43) (* '+' *) then
          match parse_nat_digits rest 0 with
          | Some n => Some (Z.of_nat n)
          | None => None
          end
        else
          match parse_nat_digits l 0 with
          | Some n => Some (Z.of_nat n)
          | None => None
          end
    end.

  Definition parse_nat (s : string) : option nat :=
    match parse_int s with
    | Some z =>
        (* SAFE: guard (z <? 0) ensures z >= 0 before Z.to_nat *)
        if (z <? 0)%Z then None else Some (Z.to_nat z)
    | None => None
    end.

  (** DIMACS CNF parsing: the standard format every SAT solver uses.
      If I claim to solve SAT, I have to speak DIMACS.

      Format:
      - Lines starting with 'c': comments, skip
      - "p cnf <num_vars> <num_clauses>": header
      - Space-separated integers terminated by 0: a clause
        e.g. "1 -2 3 0" means (x₁ ∨ ¬x₂ ∨ x₃)

      Line-by-line scanner: skip comments, grab num_vars from header,
      accumulate clauses. This should accept exactly what standard DIMACS
      parsers accept — the cross-layer parity tests verify agreement with
      the OCaml extraction. *)

  (** Parsed CNF formula. cnf_num_vars is the variable count (1..num_vars);
      cnf_clauses is the list of clauses, each clause a list of literals.
      Positive integer k → variable k is true; negative -k → variable k is false.
      Example: {{cnf_num_vars := 3; cnf_clauses := [[1; -2]; [-1; 3]; [2; -3]]}}
      represents (x₁ ∨ ¬x₂) ∧ (¬x₁ ∨ x₃) ∧ (x₂ ∨ ¬x₃). *)
  Record dimacs_cnf :=
    { cnf_num_vars : nat;
      cnf_clauses : list (list Z) }.

  Definition take_until_zero (zs : list Z) : list Z :=
    let fix go (l : list Z) (acc : list Z) :=
      match l with
      | [] => rev acc
      | z :: l' => if Z.eqb z 0 then rev acc else go l' (z :: acc)
      end
    in go zs [].

  Definition parse_clause_tokens (toks : list string) : option (list Z) :=
    let ints :=
      let fix go (ts : list string) (acc : list Z) :=
        match ts with
        | [] => Some (rev acc)
        | t :: ts' =>
            match parse_int t with
            | Some z => go ts' (z :: acc)
            | None => None
            end
        end
      in go toks []
    in
    match ints with
    | Some zs => Some (take_until_zero zs)
    | None => None
    end.

  Definition parse_dimacs (text : string) : option dimacs_cnf :=
    let lines := split_lines text in
    let fix go (ls : list string) (num_vars : option nat) (clauses : list (list Z)) :=
      match ls with
      | [] =>
          match num_vars with
          | Some nv => Some {| cnf_num_vars := nv; cnf_clauses := rev clauses |}
          | None => None
          end
      | line :: ls' =>
          let line' := trim_left line in
          match line' with
          | EmptyString => go ls' num_vars clauses
          | String c _ =>
              if Ascii.eqb c (Ascii.ascii_of_nat 99) (* 'c' *) then
                go ls' num_vars clauses
              else if Ascii.eqb c (Ascii.ascii_of_nat 112) (* 'p' *) then
                let toks := split_ws line' in
                match toks with
                | _p :: _cnf :: nv :: _nc :: _ =>
                    match parse_nat nv with
                    | Some nv' => go ls' (Some nv') clauses
                    | None => None
                    end
                | _ => None
                end
              else
                match parse_clause_tokens (split_ws line') with
                | Some cl => go ls' num_vars (cl :: clauses)
                | None => None
                end
          end
      end
    in go lines None [].

  (** SAT model checking: given a formula and an assignment, verify the
      assignment satisfies every clause.

      Algorithm: parse the assignment into (variable, bool) pairs; for each
      clause check if any literal is satisfied. If all clauses are true,
      the certificate is valid. Mechanical substitution — no search,
      no heuristics. O(formula_size), linear in literals.

      This is WHY certificates work: finding a satisfying assignment is hard,
      but checking one is easy. If check_model(F, A) = true and A doesn't
      actually satisfy F, something is broken. It's just substitution. *)

  Fixpoint lookup_bool (x : nat) (m : list (nat * bool)) : option bool :=
    match m with
    | [] => None
    | (k, v) :: m' => if Nat.eqb k x then Some v else lookup_bool x m'
    end.

  Definition insert_bool (x : nat) (v : bool) (m : list (nat * bool)) : list (nat * bool) :=
    (x, v) :: m.

  Definition remove_prefix_v (s : string) : string :=
    match s with
    | String c rest =>
        if orb (Ascii.eqb c (Ascii.ascii_of_nat 118)) (* 'v' *)
               (Ascii.eqb c (Ascii.ascii_of_nat 86)) (* 'V' *)
        then rest else s
    | _ => s
    end.

  Fixpoint split_on_eq_aux (l : list ascii) (acc : list ascii) : option (list ascii * list ascii) :=
    match l with
    | [] => None
    | c :: l' =>
        if Nat.eqb (ascii_nat c) 61%nat (* '=' *) then
          Some (rev acc, l')
        else
          split_on_eq_aux l' (c :: acc)
    end.

  Definition split_on_eq (s : string) : option (string * string) :=
    match split_on_eq_aux (string_to_list s) [] with
    | Some (l1, l2) => Some (list_to_string l1, list_to_string l2)
    | None => None
    end.

  Definition value_is_false (s : string) : bool :=
    (* Treats "0", "false", "f" as false; everything else true. *)
    let t := trim_left s in
    orb (String.eqb t "0") (orb (String.eqb t "false") (String.eqb t "f")).

  Definition parse_assignment_token (tok : string) : option (nat * bool) :=
    if String.eqb tok "0" then None
    else
      match split_on_eq tok with
      | Some (lhs, rhs) =>
          match parse_nat (remove_prefix_v lhs) with
          | Some var => Some (var, negb (value_is_false rhs))
          | None => None
          end
      | None =>
          match parse_int tok with
          | Some lit =>
              if Z.eqb lit 0 then None
              else
                (* SAFE: Z.abs returns non-negative; Z.to_nat is exact *)
                let var := Z.to_nat (Z.abs lit) in
                Some (var, (lit >? 0)%Z)
          | None => None
          end
      end.

  Definition parse_assignment (text : string) : option (list (nat * bool)) :=
    let toks := split_ws text in
    let fix go (ts : list string) (acc : list (nat * bool)) :=
      match ts with
      | [] => Some acc
      | t :: ts' =>
          match parse_assignment_token t with
          | Some (var, v) => go ts' (insert_bool var v acc)
          | None => go ts' acc
          end
      end
    in go toks [].

  (** clause_satisfied: a clause is a disjunction, so it's true if at least
      one literal is satisfied. For each literal: extract the variable number
      (|literal|), look up its value, check sign match. Empty clause → false
      (nothing to satisfy). Variable not in assignment → unsatisfied
      (conservative). Pure Boolean logic, no approximation. *)
  Definition clause_satisfied (asgn : list (nat * bool)) (cl : list Z) : bool :=
    let fix go (lits : list Z) : bool :=
      match lits with
      | [] => false
      | lit :: lits' =>
          (* SAFE: Z.abs returns non-negative; Z.to_nat is exact *)
          let var := Z.to_nat (Z.abs lit) in
          match lookup_bool var asgn with
          | Some b => if Bool.eqb b (lit >? 0)%Z then true else go lits'
          | None => false
          end
      end
    in go cl.

  (** check_model: top-level SAT certificate checker.
      Input: DIMACS CNF text + space-separated assignment text.
      Output: true iff assignment satisfies the formula.

      Steps: parse formula, parse assignment, verify assignment length ≥
      num_vars (all variables must be assigned), check every clause with
      forallb. Returns false if any parse fails or any clause is unsatisfied.

      This is the gate the VM goes through to verify SAT claims. If I say
      "formula F is satisfiable", I have to provide an A such that
      check_model(F, A) = true. No escape. The check is mechanical — no
      heuristics, no approximation. *)
  Definition check_model (cnf_text : string) (assignment_text : string) : bool :=
    match parse_dimacs cnf_text, parse_assignment assignment_text with
    | Some cnf, Some asgn =>
        if (Nat.ltb (List.length asgn) cnf.(cnf_num_vars)) then false
        else
          forallb (clause_satisfied asgn) cnf.(cnf_clauses)
    | _, _ => false
    end.

  (** LRAT / RUP checking for UNSAT proofs.

      SAT is easy to check — just test the assignment. UNSAT is harder: how
      do you prove NO assignment works? The answer is LRAT proofs (Linear
      Resolution Asymmetric Tautology). Each step either adds a clause derived
      by RUP or deletes old ones for memory efficiency.

      RUP check for clause C from database DB:
      1. Assume ¬C (negate all literals)
      2. Run unit propagation on DB ∪ {¬C}
      3. If it reaches a contradiction: C is valid. If not: invalid.

      This works because RUP is sound by resolution. If ¬C is inconsistent
      with DB, then C must follow from DB. Iterating until you derive the
      empty clause (FALSE) proves the formula is unsatisfiable.

      O(proof_size × formula_size) — polynomial to check even though finding
      the proof is NP-hard. That asymmetry is WHY proof certificates work
      for UNSAT. If I find a satisfiable formula and an LRAT proof this
      checker accepts, the RUP checks are broken. *)

  Definition assoc_remove (k : nat) (db : list (nat * list Z)) : list (nat * list Z) :=
    filter (fun kv => negb (Nat.eqb (fst kv) k)) db.

  Definition db_clauses (db : list (nat * list Z)) : list (list Z) :=
    map snd db.

  Definition eval_clause (asgn : list (nat * bool)) (cl : list Z) : (bool * list Z) :=
    let fix go (lits : list Z) (undec : list Z) : (bool * list Z) :=
      match lits with
      | [] => (false, rev undec)
      | lit :: lits' =>
          (* SAFE: Z.abs returns non-negative; Z.to_nat is exact *)
          let var := Z.to_nat (Z.abs lit) in
          match lookup_bool var asgn with
          | Some b =>
              if Bool.eqb b (lit >? 0)%Z then (true, []) else go lits' undec
          | None => go lits' (lit :: undec)
          end
      end
    in go cl [].

  (** unit_conflict_fuel: core RUP propagation loop, fuel-bounded for
      termination. Unit propagation can run long; fuel caps iterations
      and returns false if exhausted (proof invalid, not infinite loop).

      Loop: pop a literal from the queue. If it contradicts the current
      assignment, we have a conflict — return true. Otherwise assign it
      and scan all clauses: unsatisfied clause → conflict (return true);
      unit clause (one undecided literal) → add that literal to queue;
      otherwise continue. Returns false when queue is empty with no conflict.

      This is DPLL unit propagation. For RUP I assume ¬C and run this —
      if it finds a conflict, C must follow from the database. Fuel is set
      to num_vars + queue_length + 10, generous but finite. *)
  Fixpoint unit_conflict_fuel
    (fuel : nat)
    (num_vars : nat)
    (clauses : list (list Z))
    (asgn : list (nat * bool))
    (queue : list Z)
    : bool :=
    match fuel with
    | 0%nat => false
    | S fuel' =>
        match queue with
        | [] => false
        | lit :: queue' =>
            (* SAFE: Z.abs returns non-negative; Z.to_nat is exact *)
            let var := Z.to_nat (Z.abs lit) in
            let value := (lit >? 0)%Z in
            match lookup_bool var asgn with
            | Some b =>
                if Bool.eqb b value then
                  unit_conflict_fuel fuel' num_vars clauses asgn queue'
                else true
            | None =>
                let asgn' := insert_bool var value asgn in
                (* scan clauses for conflict / new unit literals *)
                let fix scan (cls : list (list Z)) (q : list Z) : option (list Z) :=
                  match cls with
                  | [] => Some q
                  | cl :: cls' =>
                      let '(sat, undec) := eval_clause asgn' cl in
                      if sat then scan cls' q
                      else
                        match undec with
                        | [] => None
                        | [u] => scan cls' (u :: q)
                        | _ => scan cls' q
                        end
                  end
                in
                match scan clauses queue' with
                | None => true
                | Some q' => unit_conflict_fuel fuel' num_vars clauses asgn' q'
                end
            end
        end
    end.

  (** unit_conflict: wrapper that seeds unit_conflict_fuel.
      Collects existing unit clauses from the formula, prepends the caller's
      assumptions, and launches propagation. Returns true if assumptions
      reach a contradiction, false if they don't (or fuel runs out). *)
  Definition unit_conflict
    (num_vars : nat)
    (clauses : list (list Z))
    (assumptions : list Z)
    : bool :=
    let unit_lits :=
      fold_right
        (fun cl acc => match cl with | [u] => u :: acc | _ => acc end)
        []
        clauses
    in
    let queue := (assumptions ++ unit_lits)%list in
    let fuel := (num_vars + List.length queue + 10)%nat in
    unit_conflict_fuel fuel num_vars clauses [] queue.

  (** verify_rup_clause: check that C is derivable by RUP from DB.
      Negates C (map Z.opp), then runs unit_conflict. If ¬C leads to
      contradiction with DB, C must follow from DB — RUP holds. If not,
      this step is invalid and the LRAT proof is rejected. *)
  Definition verify_rup_clause
    (num_vars : nat)
    (db : list (nat * list Z))
    (clause : list Z)
    : bool :=
    unit_conflict num_vars (db_clauses db) (map Z.opp clause).

  (** lrat_step: one parsed line of an LRAT proof.
      Either a derivation (add a new clause by RUP) or a deletion
      (remove old clauses to keep memory bounded).

      Fields: lrat_id (clause ID), lrat_clause (literals), lrat_deletions
      (IDs to remove), lrat_is_delete (true = deletion step).

      Derivation line: "<id> <lit>* 0 [<hint>* 0] <del>* 0"
      Deletion line: "d <id>* 0"
      Example: "5 1 -2 0 0 2 3 0" → derive clause #5 = (x₁ ∨ ¬x₂),
      hints from clauses #2 and #3, no deletions.

      Deletions don't affect soundness — a derived clause stays valid; we
      just drop it from memory once it's no longer needed for future steps. *)
  Record lrat_step :=
    { lrat_id : nat;
      lrat_clause : list Z;
      lrat_deletions : list nat;
      lrat_is_delete : bool }.

  Definition parse_nat_list (toks : list string) : option (list nat) :=
    let fix go (ts : list string) (acc : list nat) :=
      match ts with
      | [] => Some (rev acc)
      | t :: ts' =>
          match parse_nat t with
          | Some n => if Nat.eqb n 0%nat then Some (rev acc) else go ts' (n :: acc)
          | None => None
          end
      end
    in go toks [].

  Definition parse_z_list (toks : list string) : option (list Z) :=
    let fix go (ts : list string) (acc : list Z) :=
      match ts with
      | [] => Some (rev acc)
      | t :: ts' =>
          match parse_int t with
          | Some z => if Z.eqb z 0 then Some (rev acc) else go ts' (z :: acc)
          | None => None
          end
      end
    in go toks [].

  Definition drop_until_zero (toks : list string) : list string :=
    let fix go (ts : list string) :=
      match ts with
      | [] => []
      | t :: ts' =>
          if String.eqb t "0" then ts' else go ts'
      end
    in go toks.

  Definition parse_lrat_line (line : string) : option lrat_step :=
    let t := trim_left line in
    if String.eqb t "" then None
    else if starts_with_char (Ascii.ascii_of_nat 99) t (* 'c' *) then None
    else
      let toks := split_ws t in
      match toks with
      | [] => None
      | first :: rest =>
          if String.eqb first "d" then
            match parse_nat_list rest with
            | Some dels =>
                Some {| lrat_id := 0%nat;
                        lrat_clause := [];
                        lrat_deletions := dels;
                        lrat_is_delete := true |}
            | None => None
            end
          else
            match parse_nat first with
            | Some cid =>
                match parse_z_list rest with
                | Some clause =>
                    let after_clause := drop_until_zero rest in
                    let after_hints := drop_until_zero after_clause in
                    match parse_nat_list after_hints with
                    | Some dels =>
                        Some {| lrat_id := cid;
                                lrat_clause := clause;
                                lrat_deletions := dels;
                                lrat_is_delete := false |}
                    | None => None
                    end
                | None => None
                end
            | None => None
            end
      end.

  Fixpoint build_initial_db (clauses : list (list Z)) (idx : nat) : list (nat * list Z) :=
    match clauses with
    | [] => []
    | cl :: cls => (idx, cl) :: build_initial_db cls (S idx)
    end.

  Fixpoint apply_deletions (db : list (nat * list Z)) (dels : list nat) : list (nat * list Z) :=
    match dels with
    | [] => db
    | d :: ds => apply_deletions (assoc_remove d db) ds
    end.

  (** check_lrat_lines: walk the parsed LRAT proof line by line.

      For each line: if it's a deletion, remove those clause IDs from the
      database. If it's a derivation, verify the clause by RUP from the
      current database — reject immediately if that check fails. If the
      derived clause is empty, set the derived_empty flag.

      State: db (current clause database as (id, clause) pairs),
      derived_empty (have we derived FALSE yet?).

      Returns true iff ALL derivation steps verified AND the empty clause
      was derived. The empty clause has no literals to satisfy — deriving
      it proves the formula is contradictory, i.e. UNSAT. *)
  Fixpoint check_lrat_lines
    (num_vars : nat)
    (lines : list string)
    (db : list (nat * list Z))
    (derived_empty : bool)
    : bool :=
    match lines with
    | [] => derived_empty
    | line :: lines' =>
        match parse_lrat_line line with
        | None => check_lrat_lines num_vars lines' db derived_empty
        | Some st =>
            if st.(lrat_is_delete) then
              check_lrat_lines num_vars lines' (apply_deletions db st.(lrat_deletions)) derived_empty
            else
              if verify_rup_clause num_vars db st.(lrat_clause) then
                let db' := (st.(lrat_id), st.(lrat_clause)) :: apply_deletions db st.(lrat_deletions) in
                let derived_empty' := orb derived_empty (Nat.eqb (List.length st.(lrat_clause)) 0%nat) in
                check_lrat_lines num_vars lines' db' derived_empty'
              else false
        end
    end.

  (** check_lrat: top-level UNSAT certificate checker.
      Input: DIMACS CNF text + LRAT proof text.
      Output: true iff the proof derives the empty clause with all RUP
      steps valid.

      Steps: parse formula, build initial clause database (IDs 1, 2, 3...),
      then run check_lrat_lines. Returns false if any parse fails or any
      RUP step fails.

      UNSAT proofs can be enormous for hard instances — O(proof_size ×
      formula_size) to check. That's why it's a μ>0 operation: the μ-cost
      is proportional to proof length. I can't claim UNSAT for free.

      Same story as check_model: this Coq code is the canonical spec,
      extracted to OCaml (build/thiele_core.ml), same RUP checks, same
      outputs. *)
  Definition check_lrat (cnf_text : string) (proof_text : string) : bool :=
    match parse_dimacs cnf_text with
    | None => false
    | Some cnf =>
        let db := build_initial_db cnf.(cnf_clauses) 1%nat in
        check_lrat_lines cnf.(cnf_num_vars) (split_lines proof_text) db false
    end.

  (** Binary clause format — hardware path.

      The on-chip LASSERT FSM reads formula and assignment directly from VM
      data memory as 32-bit words. Parsing DIMACS text in RTL is infeasible
      (hundreds of FSM states); a binary word-per-literal layout reduces
      the checker to ~20 FSM states. This section gives the Coq model so
      the hardware FSM and the kernel share a semantic function and can be
      formally related.

      Binary format (agreed with hardware FSM):
        mem[fbase + 0] : flen (number of literal/terminator words)
        mem[fbase + 1] : num_vars
        mem[fbase + 2] : num_clauses
        mem[fbase + 3 .. 3+flen-1] : clause data — signed 32-bit literals,
          0 = end-of-clause terminator
        mem[cbase + 0] : num_vars guard
        mem[cbase + k] : assignment for variable k (0 = false, nonzero = true),
          variables 1-indexed

      Sign convention: w < 2^31 → positive literal; w ≥ 2^31 → negative
      (2's complement: Z_of_nat(w) - 2^32).

      check_model_binary reads the same semantic content as check_model but
      pre-formatted as memory words instead of DIMACS text. They should
      agree when the two representations are consistent. *)

  (** word32_to_signed: interpret a 32-bit nat as a signed Z (2's complement).
      Values [0, 2^31-1] are non-negative; values [2^31, 2^32-1] are negative. *)
  Definition word32_to_signed (w : nat) : Z :=
    let w' := Z.of_nat w in
    if (w' <? 2147483648)%Z   (* 2^31 *)
    then w'
    else (w' - 4294967296)%Z.  (* w' - 2^32 = 2's complement negative *)

  (** check_model_binary: SAT certificate checker on binary memory words.

      Takes the raw word list starting at fbase (formula) and the raw word
      list starting at cbase (assignment), both as lists of nat.

      formula_words layout:  [flen | num_vars | num_clauses | lit* | ...]
      cert_words layout:     [num_vars | val_1 | val_2 | ... | val_num_vars]

      Returns true iff all clauses are satisfied by the assignment. *)
  Definition check_model_binary (formula_words : list nat) (cert_words : list nat) : bool :=
    match formula_words with
    | _ :: _ :: nclauses_w :: lit_words =>
        (* Assignment lookup: cert_words[k] = value for variable k.
           Variables are 1-indexed so cert_words[0] is the guard word. *)
        let lookup_asgn (var : nat) : bool :=
          match nth_error cert_words var with
          | Some v => negb (Nat.eqb v 0)
          | None   => false
          end
        in
        (* Scan literal words, one clause at a time.
           ndone = number of clauses fully verified so far.
           clause_sat = has any literal in the current clause been satisfied? *)
        let fix scan (words : list nat) (ndone : nat) (clause_sat : bool) : bool :=
          if Nat.eqb ndone nclauses_w then true  (* all clauses verified *)
          else
            match words with
            | []      => false   (* formula truncated before all clauses finished *)
            | w :: ws =>
                if Nat.eqb w 0 then
                  (* end-of-clause terminator *)
                  if clause_sat then scan ws (S ndone) false
                  else false               (* this clause was never satisfied *)
                else
                  let lit := word32_to_signed w in
                  (* SAFE: Z.abs is always >= 0; Z.to_nat (Z.abs lit) is exact, no truncation *)
                  let var := Z.to_nat (Z.abs lit) in
                  let lsat :=
                    if (lit >? 0)%Z then lookup_asgn var
                    else negb (lookup_asgn var)
                  in
                  scan ws ndone (orb clause_sat lsat)
            end
        in
        scan lit_words 0%nat false
    | _ => false
    end.

  (** check_model_binary_fn: function-based variant of check_model_binary.

      Instead of taking a list of cert words, takes a function get_cert : nat -> nat
      that maps variable indices to assignment values.  This avoids materialising a
      65536-element list when the cert is implicitly stored in hardware data memory.

      Semantically equivalent to check_model_binary when
        get_cert k = nth k cert_words 0. *)
  Definition check_model_binary_fn (formula_words : list nat) (get_cert : nat -> nat) : bool :=
    match formula_words with
    | _ :: _ :: nclauses_w :: lit_words =>
        let lookup_asgn (var : nat) : bool :=
          negb (Nat.eqb (get_cert var) 0)
        in
        let fix scan (words : list nat) (ndone : nat) (clause_sat : bool) : bool :=
          if Nat.eqb ndone nclauses_w then true
          else
            match words with
            | []      => false
            | w :: ws =>
                if Nat.eqb w 0 then
                  if clause_sat then scan ws (S ndone) false
                  else false
                else
                  let lit := word32_to_signed w in
                  (* SAFE: Z.abs is always >= 0; Z.to_nat (Z.abs lit) is exact, no truncation *)
                  let var := Z.to_nat (Z.abs lit) in
                  let lsat :=
                    if (lit >? 0)%Z then lookup_asgn var
                    else negb (lookup_asgn var)
                  in
                  scan ws ndone (orb clause_sat lsat)
            end
        in
        scan lit_words 0%nat false
    | _ => false
    end.

  (** check_countermodel_binary: dual to check_model_binary.

      Returns true iff the provided assignment is a genuine countermodel for
      the formula, meaning the formula is well-formed enough to scan and the
      assignment does not satisfy all clauses. This is the cheap, checkable
      witness that the asserted constraint is non-trivial: at least one state
      is excluded.

      This does NOT compute exact feasible-set shrinkage. It enforces the
      minimum semantic guard the kernel can check cheaply: the formula has at
      least one satisfying assignment and at least one falsifying assignment.
      That blocks tautology inflation without asking the VM to solve model
      counting at runtime. *)
  Definition check_countermodel_binary (formula_words : list nat) (cert_words : list nat) : bool :=
    match formula_words with
    | _ :: _ :: _ :: _ => negb (check_model_binary formula_words cert_words)
    | _ => false
    end.

  (** check_countermodel_binary_fn: function-based countermodel checker.

      Semantically equivalent to [check_countermodel_binary] when
        get_cert k = nth k cert_words 0.
      Used by the kernel LASSERT path so the certificate can live directly in
      VM memory rather than being materialized as a list. *)
  Definition check_countermodel_binary_fn (formula_words : list nat) (get_cert : nat -> nat) : bool :=
    match formula_words with
    | _ :: _ :: _ :: _ => negb (check_model_binary_fn formula_words get_cert)
    | _ => false
    end.

  (** Prevent simpl from unfolding the recursive scanner: protects client proofs
      from stack overflow when kami_step bodies are reduced. *)
  Global Opaque check_model_binary_fn.
  Global Opaque check_countermodel_binary_fn.

End CertCheck.

Export CertCheck.
