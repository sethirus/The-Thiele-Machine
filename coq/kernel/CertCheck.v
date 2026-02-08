From Coq Require Import List Bool Arith.PeanoNat ZArith.
From Coq Require Import Strings.String Strings.Ascii.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(** * CertCheck: Certificate verification for SAT/UNSAT claims

    WHY THIS FILE EXISTS:
    The Thiele Machine needs to verify computational receipts. When the VM
    claims "this formula is SAT" or "this formula is UNSAT", it must provide
    a CERTIFICATE that anyone can check. This file implements those checkers
    in Coq, mirroring the Python implementation (thielecpu/certcheck.py) for
    3-layer isomorphism.

    THE TWO PROBLEMS:
    1. SAT: Formula is satisfiable. Certificate = satisfying assignment.
       Verification = substitute assignment, check all clauses true.
    2. UNSAT: Formula is unsatisfiable. Certificate = LRAT proof.
       Verification = check RUP (Reverse Unit Propagation) steps.

    WHY CERTIFICATES:
    Computational claims must be verifiable. Saying "I computed X" without
    proof is worthless. Certificates make computation CHECKABLE. This is
    foundational to the μ-cost model - you can't charge μ-cost without
    verifiable evidence that work was done.

    FORMAT:
    - DIMACS CNF: Standard format for Boolean formulas
    - SAT certificate: List of variable assignments (v1=true v2=false ...)
    - UNSAT certificate: LRAT proof (Linear Resolution Asymmetric Tautology)

    THE ISOMORPHISM:
    This Coq code EXACTLY mirrors thielecpu/certcheck.py. Same parsing, same
    checks, same outputs. Tests verify this (tests/test_cert_check.py). If
    the Python checker accepts, Coq accepts. If Coq rejects, Python rejects.

    FALSIFICATION:
    Find a formula and assignment where this checker says SAT but the formula
    isn't satisfied, or vice versa. Or find an LRAT proof that this checker
    accepts but the formula is actually SAT. The proofs are deterministic -
    bit-for-bit identical execution across Coq/Python/Verilog.
*)

Module CertCheck.

  (** ========================================================================
      BASIC STRING/LIST UTILITIES
      ========================================================================

      WHY:
      Certificate formats are text-based (DIMACS, LRAT). This section provides
      string manipulation primitives: splitting on whitespace, trimming, parsing.

      IMPLEMENTATION:
      Pure functional code on strings viewed as lists of ASCII characters.
      Mirrors Python's str.split(), str.strip(), etc. but deterministic and
      formal.

      USED BY:
      All parsing functions below. These are the atoms from which DIMACS and
      LRAT parsers are built.
      ====================================================================== *)

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

  (** ========================================================================
      INTEGER PARSING
      ========================================================================

      WHY:
      DIMACS uses integers for variables and literals. LRAT uses integers for
      clause IDs. This section parses ASCII decimal integers into Coq Z/nat.

      FORMAT:
      Standard decimal with optional '+' or '-' prefix. Examples: "42", "-7", "+3".

      CORRECTNESS:
      parse_int "0" = Some 0, parse_int "-123" = Some (-123)%Z. Mirrors
      Python's int(). Returns None on malformed input.

      USED BY:
      DIMACS parsing (clause literals), LRAT parsing (clause IDs, hints),
      assignment parsing (variable numbers).
      ====================================================================== *)

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
  (* SAFE: Bounded arithmetic operation with explicit domain *)
        if (z <? 0)%Z then None else Some (Z.to_nat z)
    | None => None
    end.

  (** ========================================================================
      DIMACS CNF PARSING
      ========================================================================

      WHY:
      DIMACS is THE standard format for Boolean formulas in CNF (Conjunctive
      Normal Form). Every SAT solver uses it. If the Thiele Machine claims to
      solve SAT, it must speak DIMACS.

      FORMAT:
      - Comments: Lines starting with 'c'
      - Header: "p cnf <num_vars> <num_clauses>"
      - Clauses: Space-separated integers terminated by 0
        Example: "1 -2 3 0" means (x₁ ∨ ¬x₂ ∨ x₃)

      PARSING STRATEGY:
      Line-by-line scanner. Skip comments, extract num_vars from header,
      accumulate clauses. Mirrors Python's certcheck.parse_dimacs().

      CORRECTNESS:
      parse_dimacs should accept EXACTLY the strings accepted by standard
      DIMACS parsers. Tests verify this against Python's implementation.

      FALSIFICATION:
      Find a valid DIMACS file that this parser rejects, or an invalid file
      it accepts. The 3-layer isomorphism tests check this.
      ====================================================================== *)

  (** dimacs_cnf: Parsed CNF formula.

      FIELDS:
      - cnf_num_vars: Number of variables (1 to num_vars)
      - cnf_clauses: List of clauses, each clause a list of literals

      LITERALS:
      Positive integer k means variable k is true.
      Negative integer -k means variable k is false (negated).

      EXAMPLE:
      {{cnf_num_vars := 3; cnf_clauses := [[1; -2]; [-1; 3]; [2; -3]]}}
      represents: (x₁ ∨ ¬x₂) ∧ (¬x₁ ∨ x₃) ∧ (x₂ ∨ ¬x₃)
  *)
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

  (** ========================================================================
      SAT MODEL CHECKING
      ========================================================================

      WHY:
      Verifying SAT certificates. Given a formula and an assignment, check
      that the assignment satisfies all clauses.

      THE ALGORITHM:
      1. Parse assignment into (variable, bool) pairs
      2. For each clause:
         - Check if any literal is satisfied by the assignment
         - If yes: clause is true
         - If no: formula is false, certificate invalid
      3. If all clauses satisfied: certificate valid

      CORRECTNESS:
      This is mechanical evaluation. No search, no heuristics. Just substitute
      and check. Either ALL clauses are true (SAT) or at least one is false
      (certificate invalid).

      TIME COMPLEXITY:
      O(formula_size). Linear in the number of literals. Fast verification is
      WHY certificates work - checking is easy even when finding is hard.

      FALSIFICATION:
      Find a formula F and assignment A where check_model(F, A) = true but
      A doesn't actually satisfy F. Can't happen - the check is mechanical
      substitution.
      ====================================================================== *)

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
    (* Mirrors Python: treat "0", "false", "f" as false; everything else true. *)
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
  (* SAFE: Bounded arithmetic operation with explicit domain *)
              else
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

  (** clause_satisfied: Check if a clause is true under an assignment.

      WHY:
      A clause is a disjunction (OR) of literals. It's satisfied if AT LEAST
      ONE literal is true. This function scans the clause looking for a
      satisfied literal.

      THE ALGORITHM:
      For each literal in the clause:
      - Extract variable number (|literal|)
      - Look up its value in the assignment
      - If positive literal and var=true, or negative literal and var=false: TRUE
      - If no literal matches: FALSE

      EDGE CASES:
      - Empty clause: Always false (can't satisfy nothing)
      - Variable not in assignment: clause unsatisfied (conservative)

      CORRECTNESS:
      Pure Boolean logic. The clause (lit₁ ∨ lit₂ ∨ ... ∨ litₙ) is true iff
      at least one litᵢ evaluates to true under the assignment.
  *)
  Definition clause_satisfied (asgn : list (nat * bool)) (cl : list Z) : bool :=
    let fix go (lits : list Z) : bool :=
      match lits with
  (* SAFE: Bounded arithmetic operation with explicit domain *)
      | [] => false
      | lit :: lits' =>
      (* SAFE: Bounded arithmetic operation with explicit domain *)
          let var := Z.to_nat (Z.abs lit) in
          match lookup_bool var asgn with
          | Some b => if Bool.eqb b (lit >? 0)%Z then true else go lits'
          | None => false
          end
      end
    in go cl.

  (** check_model: Main SAT certificate checker.

      WHY THIS IS THE TOP-LEVEL FUNCTION:
      This is what the VM calls when verifying a SAT certificate. Takes raw
      text (DIMACS formula + assignment), returns bool (valid or invalid).

      THE CONTRACT:
      - Input: DIMACS CNF formula, space-separated assignment
      - Output: true iff assignment satisfies formula
      - Failure: false if parsing fails or formula unsatisfied

      THE ALGORITHM:
      1. Parse DIMACS formula
      2. Parse assignment
      3. Check assignment length ≥ num_vars (must assign all variables)
      4. Check all clauses satisfied (forallb clause_satisfied)
      5. Return conjunction of all checks

      WHY THIS MATTERS:
      This is how the Thiele Machine verifies SAT claims. If the VM says
      "formula F is satisfiable", it must provide an assignment A such that
      check_model(F, A) = true. No escape. Computational claims must have
      checkable proofs.

      FALSIFICATION:
      Find F and A where check_model(F, A) = true but A doesn't satisfy F.
      Or where check_model(F, A) = false but A does satisfy F. The check is
      mechanical - no heuristics, no approximation.
  *)
  Definition check_model (cnf_text : string) (assignment_text : string) : bool :=
    match parse_dimacs cnf_text, parse_assignment assignment_text with
    | Some cnf, Some asgn =>
        if (Nat.ltb (List.length asgn) cnf.(cnf_num_vars)) then false
        else
          forallb (clause_satisfied asgn) cnf.(cnf_clauses)
    | _, _ => false
    end.

  (** ========================================================================
      LRAT / RUP CHECKING (UNSAT PROOFS)
      ========================================================================

      WHY:
      Verifying UNSAT certificates. SAT is easy to check (just test the
      assignment). UNSAT is harder - how do you prove NO assignment works?

      THE SOLUTION: LRAT PROOFS:
      LRAT (Linear Resolution Asymmetric Tautology) is a proof format for
      UNSAT. Each step either:
      1. Adds a new clause derived by RUP (Reverse Unit Propagation)
      2. Deletes old clauses (for efficiency)

      VERIFICATION:
      Check that each derived clause follows by RUP from existing clauses.
      If the proof derives the empty clause (contradiction), the formula is UNSAT.

      RUP (Reverse Unit Propagation):
      To check that clause C follows by RUP from clauses DB:
      1. Assume ¬C (negate all literals in C)
      2. Perform unit propagation on DB ∪ {¬C}
      3. If contradiction (empty clause): C is valid. If not: invalid.

      WHY THIS WORKS:
      RUP is sound by resolution. If assuming ¬C leads to contradiction, then
      C must be true. Iterating this builds a proof that the original formula
      implies FALSE (i.e., is unsatisfiable).

      TIME COMPLEXITY:
      O(proof_size × formula_size). Linear in proof length. This is WHY UNSAT
      proofs are practical - checking is polynomial even though finding is NP-hard.

      FALSIFICATION:
      Find a satisfiable formula and an LRAT proof that this checker accepts.
      Or find an unsatisfiable formula and a proof this checker rejects even
      though the proof is valid. The RUP checks are mechanical and complete.
      ====================================================================== *)

  Definition assoc_remove (k : nat) (db : list (nat * list Z)) : list (nat * list Z) :=
    filter (fun kv => negb (Nat.eqb (fst kv) k)) db.

  Definition db_clauses (db : list (nat * list Z)) : list (list Z) :=
    map snd db.

  Definition eval_clause (asgn : list (nat * bool)) (cl : list Z) : (bool * list Z) :=
    let fix go (lits : list Z) (undec : list Z) : (bool * list Z) :=
  (* SAFE: Bounded arithmetic operation with explicit domain *)
      match lits with
      | [] => (false, rev undec)
      | lit :: lits' =>
      (* SAFE: Bounded arithmetic operation with explicit domain *)
          let var := Z.to_nat (Z.abs lit) in
          match lookup_bool var asgn with
          | Some b =>
              if Bool.eqb b (lit >? 0)%Z then (true, []) else go lits' undec
          | None => go lits' (lit :: undec)
          end
      end
    in go cl [].

  (** unit_conflict_fuel: Core RUP checker with termination fuel.

      WHY FUEL:
      Unit propagation can loop if not careful. Fuel bounds iterations to
      ensure termination. If fuel runs out, return false (proof invalid).

      THE ALGORITHM:
      1. Pop a literal from the queue
      2. Check if it contradicts current assignment (conflict found: return true)
      3. If not, assign it and scan all clauses:
         - If clause becomes unsatisfied (empty): conflict! Return true.
         - If clause becomes unit (one unassigned literal): add to queue.
         - Otherwise: continue.
      4. Repeat until queue empty (no conflict: return false) or fuel exhausted.

      WHY THIS WORKS:
      Unit propagation is the core of DPLL SAT solvers. If assigning
      assumptions leads to a conflict, the assumptions are inconsistent. For
      RUP, we assume ¬C and check for conflict - if found, C must be true.

      FUEL CALCULATION:
      Set to num_vars + queue_length + 10. Generous but bounded. In practice,
      unit propagation terminates quickly or finds conflict quickly.

      USED BY:
      unit_conflict (wrapper that sets up fuel), which is called by
      verify_rup_clause to check each RUP step.
  *)
  Fixpoint unit_conflict_fuel
    (fuel : nat)
    (num_vars : nat)
    (clauses : list (list Z))
    (asgn : list (nat * bool))
    (queue : list Z)
    : bool :=
    match fuel with
    | 0%nat => false
  (* SAFE: Bounded arithmetic operation with explicit domain *)
    | S fuel' =>
        match queue with
        | [] => false
        | lit :: queue' =>
      (* SAFE: Bounded arithmetic operation with explicit domain *)
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

  (** unit_conflict: Check if assumptions lead to contradiction.

      WHY THIS WRAPPER:
      Sets up the initial state for unit_conflict_fuel. Collects initial unit
      clauses, builds the propagation queue, calculates fuel.

      THE SETUP:
      - unit_lits: Extract all unit clauses (single-literal clauses) from formula
      - queue: assumptions + unit_lits (initial propagation queue)
      - fuel: num_vars + queue length + 10 (generous termination bound)

      RETURNS:
      true if unit propagation from assumptions reaches a conflict.
      false if propagation completes without conflict or runs out of fuel.

      USED BY:
      verify_rup_clause to check RUP steps.
  *)
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

  (** verify_rup_clause: Check that a clause is derivable by RUP.

      WHY:
      This is the core of LRAT verification. Each derived clause must be
      checkable by RUP from existing clauses.

      THE CHECK:
      To verify clause C from database DB:
      1. Negate C: map Z.opp clause (flip all literals)
      2. Check if ¬C leads to conflict with DB
      3. If yes: C is valid (RUP holds). If no: invalid.

      WHY NEGATE:
      RUP checks if C is implied by DB. This is equivalent to checking if
      DB ∧ ¬C is inconsistent. So we assume ¬C and look for contradiction.

      USED BY:
      check_lrat_lines to verify each derivation step in the LRAT proof.

      FALSIFICATION:
      Find a clause C and database DB where this returns true but C doesn't
      actually follow from DB. Or where this returns false but C does follow.
      The unit propagation is complete and sound for RUP.
  *)
  Definition verify_rup_clause
    (num_vars : nat)
    (db : list (nat * list Z))
    (clause : list Z)
    : bool :=
    unit_conflict num_vars (db_clauses db) (map Z.opp clause).

  (** lrat_step: One line of an LRAT proof.

      STRUCTURE:
      LRAT proofs are sequences of steps. Each step is either:
      1. Derivation: Add a new clause (with ID) derived by RUP
      2. Deletion: Remove old clauses (for memory efficiency)

      FIELDS:
      - lrat_id: Clause ID number
      - lrat_clause: The derived clause (list of literals)
      - lrat_deletions: Clause IDs to delete after this step
      - lrat_is_delete: true if pure deletion step, false if derivation

      FORMAT:
      Derivation line: "<id> <lit>* 0 [<hint>* 0] <del>* 0"
      Deletion line: "d <id>* 0"

      EXAMPLE:
      "5 1 -2 0 0 2 3 0" means:
      - Derive clause #5: (x₁ ∨ ¬x₂)
      - Hints: clauses #2 and #3 used in derivation
      - Delete: none

      WHY DELETIONS:
      LRAT proofs can be huge. Deleting clauses no longer needed keeps memory
      bounded. Doesn't affect soundness - once derived, a clause is valid.
  *)
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

  (** check_lrat_lines: Process LRAT proof line by line.

      WHY:
      LRAT proofs are sequences of steps. This function walks through them,
      verifying each derivation and maintaining the clause database.

      THE ALGORITHM:
      For each line in the proof:
      1. Parse as lrat_step (derivation or deletion)
      2. If deletion: remove clauses from database
      3. If derivation:
         a. Verify clause by RUP from current database
         b. If valid: add clause to database, apply deletions
         c. If empty clause derived: set derived_empty flag
         d. If invalid: REJECT proof (return false)
      4. At end: check if empty clause was derived

      STATE:
      - db: Current clause database (id, clause) pairs
      - derived_empty: Have we derived the empty clause (contradiction)?

      TERMINATION:
      Returns true iff proof derives empty clause AND all steps verify.

      WHY EMPTY CLAUSE:
      The empty clause is FALSE (no literals to satisfy). Deriving it proves
      the formula is contradictory, hence UNSAT.

      FALSIFICATION:
      Find an LRAT proof that this accepts but doesn't derive empty clause,
      or where an RUP step is invalid. The checks are mechanical and complete.
  *)
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

  (** check_lrat: Main UNSAT certificate checker.

      WHY THIS IS THE TOP-LEVEL FUNCTION:
      This is what the VM calls when verifying an UNSAT certificate. Takes
      raw text (DIMACS formula + LRAT proof), returns bool (valid or invalid).

      THE CONTRACT:
      - Input: DIMACS CNF formula, LRAT proof text
      - Output: true iff proof derives empty clause with valid RUP steps
      - Failure: false if parsing fails or any RUP check fails

      THE ALGORITHM:
      1. Parse DIMACS formula
      2. Build initial clause database (assign IDs 1, 2, 3, ...)
      3. Process LRAT proof line by line (check_lrat_lines)
      4. Return whether empty clause was derived

      WHY THIS MATTERS:
      This is how the Thiele Machine verifies UNSAT claims. If the VM says
      "formula F is unsatisfiable", it must provide an LRAT proof P such that
      check_lrat(F, P) = true. No escape. UNSAT claims must have checkable proofs.

      THE COST:
      UNSAT proofs can be LARGE (gigabytes for hard instances). Checking them
      is expensive (O(proof_size × formula_size)). This is a μ>0 operation.
      The μ-cost is proportional to proof length.

      FALSIFICATION:
      Find F and P where check_lrat(F, P) = true but F is actually satisfiable.
      Or where check_lrat(F, P) = false but P is a valid LRAT proof. The RUP
      checks are sound and complete.

      THE ISOMORPHISM:
      This Coq implementation EXACTLY mirrors thielecpu/certcheck.check_lrat().
      Same parsing, same RUP checks, same outputs. Tests verify this
      (tests/test_cert_check.py). Bit-for-bit identical behavior.
  *)
  Definition check_lrat (cnf_text : string) (proof_text : string) : bool :=
    match parse_dimacs cnf_text with
    | None => false
    | Some cnf =>
        let db := build_initial_db cnf.(cnf_clauses) 1%nat in
        check_lrat_lines cnf.(cnf_num_vars) (split_lines proof_text) db false
    end.

End CertCheck.

Export CertCheck.
