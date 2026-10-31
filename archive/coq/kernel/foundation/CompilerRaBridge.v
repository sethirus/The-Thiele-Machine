(** CompilerRaBridge.v: every unary recursive algorithm gives a reading
    routine in the sense of CompilerChecker.v.

    The vendored compiler from recursive algorithms to counter programs
    (MuRec/Util/ra_mm_env.v, ra_compiler) produces, for f : recalg 1 and
    any choice of input register xS, answer register xB and spare bound m
    with xB < m, xB <> xS and xS < m, a counter program R satisfying the
    vendored ra_compiled specification. That specification, with one
    input, is exactly cg_routine for the relation of f [cg_routine_of_ra],
    so such an R exists for every f [cg_routine_exists], and the fixed
    checker's acceptance of the routine's code means f reads 1 on the
    input [cg_checker_sound_ra].

    Dependencies: Coq standard library, the vendored coq-undecidability
    library (recursive algorithms and their counter-machine compiler,
    compiled from copies in vend/) and the Compiler*.v files. No axioms,
    no Admitted. *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this
   file is one step of the presented universal machine of
   PresentedUniversal.v and imports only the Coq standard library, the
   vendored coq-undecidability library and the standard-library files under
   minimal/. Its link to the abstract record (the priced host as a
   CertificationSystem, the cost floor of its runs, and the undecidability
   of U_P's halting problem) lives in PricedHostLinks.v. *)

From Coq Require Import List Arith Lia.
From Undecidability.Shared.Libs.DLW Require Import utils pos vec subcode sss.
From Undecidability.MinskyMachines Require Import MM.
From Undecidability.MinskyMachines.MMenv Require Import env mme_defs.
From Undecidability.MuRec.Util Require Import recalg ra_mm_env.
Require Import Kernel.CompilerCodes Kernel.CompilerChecker.

(* The relation computed by a unary recursive algorithm. *)
Definition cg_ra_reading (f : recalg 1) : nat -> nat -> Prop :=
  fun c x => ra_rel f (c ## vec_nil) x.

Theorem cg_routine_of_ra : forall (f : recalg 1) ig xS xB m R,
  ra_compiled f ig xS xB m R -> cg_routine (cg_ra_reading f) ig R xS xB m.
Proof.
  intros f ig xS xB m R H e He.
  assert (Hv : forall q : pos 1, get_env e (pos2nat q + xS)
                                 = vec_pos (get_env e xS ## vec_nil) q).
  { intros q. invert pos q; [rewrite pos2nat_fst; reflexivity | invert pos q]. }
  destruct (H (get_env e xS ## vec_nil) e He Hv) as [H1 H2].
  split.
  - intros x Hx. destruct (H1 x Hx) as (e' & He' & Hc). exists e'. split; assumption.
  - intros Ht. exact (H2 Ht).
Qed.

Theorem cg_routine_exists : forall (f : recalg 1) ig xS xB m,
  xB < m -> xB <> xS -> xS < m ->
  { R | cg_routine (cg_ra_reading f) ig R xS xB m }.
Proof.
  intros f ig xS xB m H1 H2 H3.
  assert (Hc := @ra_compiler 1 f). unfold ra_compiler_stm in Hc.
  destruct (Hc ig xS xB m) as (R & HR); [lia | lia | lia |].
  exists R. apply cg_routine_of_ra. exact HR.
Qed.

(* The fixed checker on the code of a compiled routine. *)
Theorem cg_checker_sound_ra : forall (f : recalg 1) ig R xS xB xT m v,
  ra_compiled f ig xS xB m R ->
  cg_ueval (URun (cg_renc ig R xS xB xT m)) v = true ->
  ra_rel f (get_env (cg_env_chk m v) xS ## vec_nil) 1.
Proof.
  intros f ig R xS xB xT m v HR Hev.
  exact (cg_checker_sound (cg_ra_reading f) _ ig R xS xB xT m v
           (cg_rdec_renc ig R xS xB xT m) (cg_routine_of_ra f ig xS xB m R HR) Hev).
Qed.

Print Assumptions cg_routine_of_ra.
Print Assumptions cg_routine_exists.
Print Assumptions cg_checker_sound_ra.
