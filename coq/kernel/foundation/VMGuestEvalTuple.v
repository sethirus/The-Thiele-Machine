(** The guest evaluator over nested pairs.

    [GRegs] and [GConf] are records. The extraction to L encodes inductive
    types such as pairs, but not records, so this file restates the
    evaluator of [VMGuestEvalNat] with registers as [nat * (nat * (nat * nat))]
    and configurations as [nat * (nat * registers)], and proves every piece
    equal to the record form. *)

From Coq Require Import Arith Lia List.
Import ListNotations.
From Kernel Require Import VMUnboundedStep VMEncoding VMSelfGuest VMSelfRun VMSelfRice.
From Kernel Require Import VMGuestEvalNat VMGuestExactEpilogue.

Definition R4 : Type := nat * (nat * (nat * nat)).

Definition toR (g : GRegs) : R4 := (gr0 g, (gr1 g, (gr2 g, gr3 g))).

Definition tget (t : R4) (r : nat) : nat :=
  if r =? 0 then fst t
  else if r =? 1 then fst (snd t)
  else if r =? 2 then fst (snd (snd t))
  else snd (snd (snd t)).

Definition tset (t : R4) (r v : nat) : R4 :=
  if r =? 0 then (v, snd t)
  else if r =? 1 then (fst t, (v, snd (snd t)))
  else if r =? 2 then (fst t, (fst (snd t), (v, snd (snd (snd t)))))
  else (fst t, (fst (snd t), (fst (snd (snd t)), v))).

Lemma tget_spec : forall g r, tget (toR g) r = g_get g r.
Proof. intros [a b c d] [| [| [| r]]]; reflexivity. Qed.

Lemma tset_spec : forall g r v, tset (toR g) r v = toR (g_set g r v).
Proof. intros [a b c d] [| [| [| r]]] v; reflexivity. Qed.

Definition TC : Type := nat * (nat * R4).

Definition toC (c : GConf) : TC := (gc_pc c, (gc_mu c, toR (gc_g c))).

Definition tnext (i : GInstr) (pc mu : nat) (t : R4) : TC :=
  let mu' := mu + g_cost i in
  match i with
  | GHalt _          => (S pc, (mu', t))
  | GLoadImm d imm _ => (S pc, (mu', tset t d imm))
  | GXfer d s _      => (S pc, (mu', tset t d (tget t s)))
  | GAdd d a b _     => (S pc, (mu', tset t d (tget t a + tget t b)))
  | GSub d a b _     => (S pc, (mu', tset t d (tget t a - tget t b)))
  | GMul d a b _     => (S pc, (mu', tset t d (tget t a * tget t b)))
  | GAnd d a b _     => (S pc, (mu', tset t d (nand (tget t a) (tget t b))))
  | GOr d a b _      => (S pc, (mu', tset t d (nor (tget t a) (tget t b))))
  | GShl d a b _     => (S pc, (mu', tset t d (nshl (tget t a) (tget t b))))
  | GShr d a b _     => (S pc, (mu', tset t d (nshr (tget t a) (tget t b))))
  | GJump t' _       => (t', (mu', t))
  | GJnez r t' _     => (if Nat.eqb (tget t r) 0 then S pc else t', (mu', t))
  end.

Lemma tnext_spec : forall i pc mu g,
  tnext i pc mu (toR g) =
  let '(pc', mu', g') := nnext i pc mu g in (pc', (mu', toR g')).
Proof.
  intros i pc mu g. destruct i; unfold tnext, nnext;
    rewrite ?tget_spec, ?tset_spec; reflexivity.
Qed.

Definition tstep (p : list GInstr) (c : TC) : TC :=
  match nth_error p (fst c) with
  | Some i => tnext i (fst c) (fst (snd c)) (snd (snd c))
  | None => c
  end.

Fixpoint trun (n : nat) (p : list GInstr) (c : TC) : TC :=
  match n with
  | 0 => c
  | S n' => trun n' p (tstep p c)
  end.

Lemma tstep_spec : forall p c, tstep p (toC c) = toC (nstep p c).
Proof.
  intros p [pc mu g]. unfold tstep, nstep, toC. cbn [gc_pc gc_mu gc_g fst snd].
  destruct (nth_error p pc) as [i |]; [| reflexivity].
  rewrite tnext_spec. destruct (nnext i pc mu g) as [[pc' mu'] g']. reflexivity.
Qed.

Theorem trun_spec : forall n p c, trun n p (toC c) = toC (nrun n p c).
Proof.
  induction n as [| n IH]; intros p c; [reflexivity |].
  cbn [trun nrun]. rewrite tstep_spec. apply IH.
Qed.

Definition tinput (x : nat) : TC := (0, (0, (x, (0, (0, 0))))).

Lemma tinput_spec : forall x, tinput x = toC (g_input x).
Proof. reflexivity. Qed.

(** [g_out_pack] on pairs. *)
Definition tsum (t : R4) : nat :=
  fst t + fst (snd t) + fst (snd (snd t)) + snd (snd (snd t)).

Definition tbody (t : R4) : nat :=
  fst (snd t) + pow2 (tsum t) * (snd (snd (snd t)) + pow2 (tsum t) * fst (snd (snd t))).

Definition tpack (t : R4) (m : nat) : nat :=
  (2 * ((2 * tbody t + 1) * pow2 (tsum t)) + 1) * pow2 m.

Lemma tpack_spec : forall g m, tpack (toR g) m = g_out_pack g m.
Proof. intros [a b c d] m. reflexivity. Qed.

(** [genc] with the payload written as a direct recursion. *)
Fixpoint gpay (p : list GInstr) : list bool :=
  match p with
  | [] => []
  | i :: r => gibits i ++ gpay r
  end.

Lemma gpay_spec : forall p, gpay p = flat_map gibits p.
Proof. induction p as [| i r IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Definition gencT (p : list GInstr) : nat := bnat (VMEncoding.encode_nat (length p) ++ gpay p).

Lemma gencT_spec : forall p, gencT p = genc p.
Proof. intro p. unfold gencT, genc, gbits. rewrite gpay_spec. reflexivity. Qed.

Definition thfun (D : list GInstr) (fuel z : nat) : option nat :=
  let (c, y) := unpair z in
  match dec c with
  | None => None
  | Some p0 =>
      let cd := trun fuel D (tinput (gencT (sp p0 c))) in
      if length D <=? fst cd then
        match dec (tget (snd (snd cd)) 0) with
        | None => None
        | Some q =>
            let cq := trun fuel q (tinput y) in
            if length q <=? fst cq then Some (tpack (snd (snd cq)) (fst (snd cq))) else None
        end
      else None
  end.

Theorem thfun_spec : forall D fuel z, thfun D fuel z = hfun g_out_pack D fuel z.
Proof.
  intros D fuel z. unfold thfun, hfun.
  destruct (unpair z) as [c y]. destruct (dec c) as [p0 |]; [| reflexivity].
  rewrite gencT_spec, tinput_spec, trun_spec.
  destruct (nrun fuel D (g_input (genc (sp p0 c)))) as [pcd mud gd]. unfold toC.
  cbn [gc_pc gc_mu gc_g fst snd].
  destruct (length D <=? pcd); [| reflexivity].
  rewrite tget_spec. cbn [g_get].
  destruct (dec (gr0 gd)) as [q |]; [| reflexivity].
  rewrite tinput_spec, trun_spec.
  destruct (nrun fuel q (g_input y)) as [pcq muq gq]. unfold toC.
  cbn [gc_pc gc_mu gc_g fst snd].
  destruct (length q <=? pcq); [| reflexivity].
  rewrite tpack_spec. reflexivity.
Qed.

Print Assumptions trun_spec.
Print Assumptions thfun_spec.
