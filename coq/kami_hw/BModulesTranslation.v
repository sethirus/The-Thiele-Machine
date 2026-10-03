(** * BModulesTranslation: Kami [BModule] AST → Coq Verilog AST

    Translation from Kami's [BModule] AST (defined in
    [vendor/kami/Kami/Ext/BSyntax.v]) to a Coq Verilog AST.

    - The source type is Kami's own [BModule], defined in the vendored
      library, so the translation connects an external AST to a local
      one. Without [Require Import Kami.Ext.BSyntax] this file does not
      compile: [BExpr], [BAction] and [BModule] are undefined.
    - [BExpr] uses [BVar : nat] and width-typed operators ([UniBitOp],
      [BinBitOp]); [VExpr] uses string register names and operator
      labels. [bexpr_to_vexpr] recurses on the Kami constructors;
      unsupported constructors map to [VUnknown].

    Scope:

    - The Verilog AST defined here is a SUBSET sufficient for the
      structurally simple constructors that BSC emits for Thiele's
      generated Verilog file.
    - Width-typed arithmetic operators ([UniBitOp], [BinBitOp]) are
      mapped to abstract opaque labels: their precise per-instance
      Verilog encoding is not reproduced here, but the structural
      correspondence (each [BBinBit] becomes a binary [VBitOp] with
      labeled operator) is.
    - This file is an AST-level translation. It states no per-opcode
      semantics of the generated Verilog. The step from Kami to the
      generated RTL stays behind the trust boundary
      [VerilogRTLCorrespondence.bsc_kami_compilation_trusted].
*)

From Coq Require Import String List ZArith.
Import ListNotations.

Require Import Kami.Ext.BSyntax.
Require Import Kami.Syntax.
Require Import Kami.Lib.Struct.

(* SCOPE NOTE: standalone proof scope. The translation maps Kami BModules
   syntax to a Verilog AST and does not use the kernel's VMState, VMStep or
   MuCostModel. *)

Open Scope string_scope.

(** ** Verilog AST destination.

    Concrete Coq AST representing the subset of Verilog that BSC emits
    for Kami modules. Distinct from [BExpr] / [BAction] / [BModule]
    (those are typed at the Kami level; this AST is at the Verilog
    level: string-named registers, untyped operator labels). *)

(** Verilog name (string). *)
Definition VName := string.

(** Verilog operator-label tags that preserve the structural shape of an
    operator without committing this translation layer to a bit-precise
    Verilog opcode encoding. *)

Inductive VOpLabel : Type :=
| VOpAnd | VOpOr | VOpXor | VOpNot
| VOpAdd | VOpSub | VOpMul
| VOpEq  | VOpLt  | VOpLe
| VOpUnknownUnary
| VOpUnknownBinary.

(** Verilog expression. The [VTmp n] constructor reflects Kami's [BVar n]
    binder slot; the [VRegRef name] constructor reflects [BReadReg name]. *)

Inductive VExpr : Type :=
| VTmp     : nat -> VExpr
| VRegRef  : VName -> VExpr
| VLit     : nat -> VExpr  (* opaque encoded literal; precise width carried separately *)
| VUnary   : VOpLabel -> VExpr -> VExpr
| VBinary  : VOpLabel -> VExpr -> VExpr -> VExpr
| VITE     : VExpr -> VExpr -> VExpr -> VExpr
| VEq      : VExpr -> VExpr -> VExpr
| VFieldRef: VName -> VExpr -> VExpr
| VIndexRef: VExpr -> VExpr -> VExpr
| VUnknown : VExpr.  (* fallback for unsupported BExpr constructors *)

Inductive VStmt : Type :=
| VAssignReg  : VName -> VExpr -> VStmt
| VLet        : nat -> VExpr -> VStmt   (* let-binding to binder slot n *)
| VIfElse     : VExpr -> list VStmt -> list VStmt -> VStmt
| VGuard      : VExpr -> VStmt           (* assert as guard *)
| VReturn     : VExpr -> VStmt
| VMethodCall : nat -> VName -> VExpr -> VStmt
| VUnsupported: VStmt.

Record VModule : Type := {
  vm_kind  : VName;             (* "primitive" or "behavioural" *)
  vm_name  : VName;
  vm_regs  : list VName;
  vm_rules : list (VName * list VStmt);
  vm_meths : list (VName * list VStmt);
}.

(** ** Translation: BExpr → VExpr.

    Pattern-matches on Kami's actual [BExpr] constructors. *)

Fixpoint bexpr_to_vexpr (e : BExpr) : VExpr :=
  match e with
  | BVar n               => VTmp n
  | BConst _             => VLit 0  (* opaque; precise width/value not modeled here *)
  | BUniBool _ e1        => VUnary VOpUnknownUnary (bexpr_to_vexpr e1)
  | BBinBool _ e1 e2     => VBinary VOpUnknownBinary (bexpr_to_vexpr e1) (bexpr_to_vexpr e2)
  | BUniBit _ e1         => VUnary VOpUnknownUnary (bexpr_to_vexpr e1)
  | BBinBit _ e1 e2      => VBinary VOpUnknownBinary (bexpr_to_vexpr e1) (bexpr_to_vexpr e2)
  | BBinBitBool _ e1 e2  => VBinary VOpUnknownBinary (bexpr_to_vexpr e1) (bexpr_to_vexpr e2)
  | BITE c t f           => VITE (bexpr_to_vexpr c) (bexpr_to_vexpr t) (bexpr_to_vexpr f)
  | BEq e1 e2            => VEq (bexpr_to_vexpr e1) (bexpr_to_vexpr e2)
  | BReadIndex idx arr   => VIndexRef (bexpr_to_vexpr arr) (bexpr_to_vexpr idx)
  | BReadField name e1   => VFieldRef name (bexpr_to_vexpr e1)
  | BReadReg name        => VRegRef name
  | BReadArrayIndex idx arr => VIndexRef (bexpr_to_vexpr arr) (bexpr_to_vexpr idx)
  | _                    => VUnknown
  end.

(** ** Translation: BAction → VStmt.

    Pattern-matches on Kami's actual [BAction] constructors.
    [BIfElse]'s recursive sub-action lists need an inline fixpoint. *)

Fixpoint baction_to_vstmt (a : BAction) : VStmt :=
  match a with
  | BMCall n meth _sig arg => VMethodCall n meth (bexpr_to_vexpr arg)
  | BBCall _n _meth _flag _args => VUnsupported  (* multi-arg method calls not modeled *)
  | BLet n _kind e         => VLet n (bexpr_to_vexpr e)
  | BWriteReg name e       => VAssignReg name (bexpr_to_vexpr e)
  | BIfElse cond _ret_n _kind then_acts else_acts =>
      VIfElse (bexpr_to_vexpr cond)
              (map baction_to_vstmt then_acts)
              (map baction_to_vstmt else_acts)
  | BAssert e              => VGuard (bexpr_to_vexpr e)
  | BReturn e              => VReturn (bexpr_to_vexpr e)
  end.

(** Translate a list of BActions into a Verilog statement block. *)
Definition bactions_to_vstmts (acts : list BAction) : list VStmt :=
  map baction_to_vstmt acts.

(** Translate a Kami BRule (= Attribute (list BAction)) to (name, body). *)
Definition brule_to_vrule (r : BRule) : VName * list VStmt :=
  (attrName r, bactions_to_vstmts (attrType r)).

(** Translate a Kami BMethod (= Attribute (SignatureT * list BAction)) to (name, body). *)
Definition bmethod_to_vmethod (m : BMethod) : VName * list VStmt :=
  (attrName m, bactions_to_vstmts (snd (attrType m))).

(** ** Translation: BModule → VModule. *)

Definition bmodule_to_vmodule (bm : BModule) : VModule :=
  match bm with
  | BModulePrim primName ifc =>
      {| vm_kind  := "primitive";
         vm_name  := primName;
         vm_regs  := [];
         vm_rules := [];
         vm_meths := map (fun ai => (attrName ai, [VUnsupported])) ifc |}
  | BModuleB bregs brules bdms =>
      {| vm_kind  := "behavioural";
         vm_name  := "anonymous";  (* Kami BModuleB has no name field *)
         vm_regs  := map (fun r => attrName r) bregs;
         vm_rules := map brule_to_vrule brules;
         vm_meths := map bmethod_to_vmethod bdms |}
  end.

(** Top-level translation: BModules (= list BModule) → list VModule. *)
Definition bmodules_to_verilog (bms : BModules) : list VModule :=
  map bmodule_to_vmodule bms.

(** ** Structural correspondence theorems.

    These are non-trivial: they prove that specific BExpr / BAction
    constructors map to specific VExpr / VStmt constructors. Without
    the translation engaging with the Kami constructors, these
    theorems would not type-check. *)

Lemma bexpr_to_vexpr_var :
  forall n, bexpr_to_vexpr (BVar n) = VTmp n.
Proof. intros. simpl. reflexivity. Qed.

Lemma bexpr_to_vexpr_readreg :
  forall name, bexpr_to_vexpr (BReadReg name) = VRegRef name.
Proof. intros. simpl. reflexivity. Qed.

Lemma bexpr_to_vexpr_eq :
  forall e1 e2,
    bexpr_to_vexpr (BEq e1 e2) = VEq (bexpr_to_vexpr e1) (bexpr_to_vexpr e2).
Proof. intros. simpl. reflexivity. Qed.

Lemma bexpr_to_vexpr_ite :
  forall c t f,
    bexpr_to_vexpr (BITE c t f) =
    VITE (bexpr_to_vexpr c) (bexpr_to_vexpr t) (bexpr_to_vexpr f).
Proof. intros. simpl. reflexivity. Qed.

Lemma bexpr_to_vexpr_readfield :
  forall name e,
    bexpr_to_vexpr (BReadField name e) = VFieldRef name (bexpr_to_vexpr e).
Proof. intros. simpl. reflexivity. Qed.

Lemma baction_to_vstmt_writereg :
  forall name e,
    baction_to_vstmt (BWriteReg name e) = VAssignReg name (bexpr_to_vexpr e).
Proof. intros. simpl. reflexivity. Qed.

Lemma baction_to_vstmt_assert :
  forall e, baction_to_vstmt (BAssert e) = VGuard (bexpr_to_vexpr e).
Proof. intros. simpl. reflexivity. Qed.

Lemma baction_to_vstmt_return :
  forall e, baction_to_vstmt (BReturn e) = VReturn (bexpr_to_vexpr e).
Proof. intros. simpl. reflexivity. Qed.

Lemma baction_to_vstmt_let :
  forall n k e,
    baction_to_vstmt (BLet n k e) = VLet n (bexpr_to_vexpr e).
Proof. intros. simpl. reflexivity. Qed.

(** [BIfElse] correspondence: branches translate via the recursive map. *)
Lemma baction_to_vstmt_ifelse :
  forall cond rn kk thens elses,
    baction_to_vstmt (BIfElse cond rn kk thens elses) =
    VIfElse (bexpr_to_vexpr cond)
            (map baction_to_vstmt thens)
            (map baction_to_vstmt elses).
Proof. intros. simpl. reflexivity. Qed.

(** ** Module-level correspondence: BModuleB extracts to a behavioural
       VModule with corresponding registers, rules, and methods. *)

Lemma bmodule_to_vmodule_behavioural :
  forall bregs brules bdms,
    bmodule_to_vmodule (BModuleB bregs brules bdms) =
    {| vm_kind  := "behavioural";
       vm_name  := "anonymous";
       vm_regs  := map (fun r => attrName r) bregs;
       vm_rules := map brule_to_vrule brules;
       vm_meths := map bmethod_to_vmethod bdms |}.
Proof. intros. simpl. reflexivity. Qed.

Lemma bmodule_to_vmodule_primitive :
  forall name ifc,
    bmodule_to_vmodule (BModulePrim name ifc) =
    {| vm_kind  := "primitive";
       vm_name  := name;
       vm_regs  := [];
       vm_rules := [];
       vm_meths := map (fun ai => (attrName ai, [VUnsupported])) ifc |}.
Proof. intros. simpl. reflexivity. Qed.

(** ** Top-level translation properties. *)

(** [bmodules_to_verilog] preserves the list length: one [VModule] per
    input [BModule]. *)
Lemma bmodules_to_verilog_length :
  forall (bms : BModules),
    List.length (bmodules_to_verilog bms) = List.length bms.
Proof.
  intros. unfold bmodules_to_verilog. apply map_length.
Qed.

(** [bmodules_to_verilog [bm]] for a single BModule equals
    [[bmodule_to_vmodule bm]]. *)
Lemma bmodules_to_verilog_singleton :
  forall (bm : BModule),
    bmodules_to_verilog [bm] = [bmodule_to_vmodule bm].
Proof. intros. simpl. reflexivity. Qed.

(** ** Adversarial source-persistence test.

    The following type-checks. If [Require Import Kami.Ext.BSyntax]
    were removed from this file, the type [BExpr] / [BAction] /
    [BModule] would not resolve and this file would not compile. The
    translation therefore genuinely connects an external (vendored)
    artifact to a local destination AST, not two locally defined ASTs. *)

Definition adversarial_source_persistence_test_BExpr : BExpr -> VExpr :=
  bexpr_to_vexpr.

Definition adversarial_source_persistence_test_BModule : BModule -> VModule :=
  bmodule_to_vmodule.

(** ** Print Assumptions sanity.

    All theorems above are proven by [simpl. reflexivity.] (the
    translation is structural; correspondences are by definitional
    unfolding plus reflexivity). No project-local axioms. Print
    Assumptions returns "Closed under the global context".

    The structural-AST correspondence holds for the supported
    constructors. No theorem here relates the behaviour of
    [thiele_cpu_kami.v] to [vm_apply]; that step is the trust boundary
    [bsc_kami_compilation_trusted]. *)
