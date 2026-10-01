(** A guest evaluator over natural numbers only.

    Program codes ([guest_program_code]) are bit strings read lowest bit
    first, with every number in unary. This file reads and writes those codes
    with halving, parity, addition, and multiplication, runs guest programs
    with the same operations, and proves each piece equal to the existing
    definitions. Every function here is a plain structural recursion over
    [nat], [bool], lists, and options, so it can be extracted to the lambda
    calculus L. *)

From Coq Require Import Arith Lia List Bool PArith NArith.
Import ListNotations.
From Kernel Require Import VMState VMStep VMUnboundedStep VMEncoding VMInstructionEncoding.
From Kernel Require Import VMSelfGuest VMSelfRun VMSelfRice VMRecursionTarget.

(** * Halving and parity *)

Fixpoint hb (n : nat) : nat * bool :=
  match n with
  | 0 => (0, false)
  | S k => let (h, b) := hb k in if b then (S h, false) else (h, true)
  end.

Definition bit (b : bool) : nat := if b then 1 else 0.

Lemma hb_correct : forall n, n = 2 * fst (hb n) + bit (snd (hb n)).
Proof.
  induction n as [| k IH]; [reflexivity |].
  simpl. destruct (hb k) as [h b]. simpl in *.
  destruct b; simpl in *; lia.
Qed.

Lemma hb_unique : forall h b, hb (bit b + 2 * h) = (h, b).
Proof.
  intros h b. pose proof (hb_correct (bit b + 2 * h)) as E.
  destruct (hb (bit b + 2 * h)) as [h' b'] eqn:Ehb. simpl in E.
  destruct b, b'; unfold bit in E; simpl in E; f_equal; lia.
Qed.

Lemma hb_spec : forall n, hb n = (Nat.div2 n, Nat.odd n).
Proof.
  intro n. pose proof (Nat.div2_odd n) as E.
  rewrite E at 1. replace (Nat.b2n (Nat.odd n)) with (bit (Nat.odd n))
    by (destruct (Nat.odd n); reflexivity).
  rewrite Nat.add_comm. apply hb_unique.
Qed.

Fixpoint pow2 (k : nat) : nat :=
  match k with
  | 0 => 1
  | S k' => pow2 k' + pow2 k'
  end.

Lemma pow2_spec : forall k, pow2 k = 2 ^ k.
Proof. induction k as [| k IH]; simpl; [reflexivity | rewrite IH; lia]. Qed.

(** * Bit strings as numbers *)

(** [bnat] is [bools_to_nat]: lowest bit first, with a top terminator bit. *)
Fixpoint bnat (bs : list bool) : nat :=
  match bs with
  | [] => 1
  | b :: r => bit b + 2 * bnat r
  end.

Lemma bnat_spec : forall bs, bnat bs = bools_to_nat bs.
Proof.
  unfold bools_to_nat.
  induction bs as [| b r IH]; [reflexivity |].
  simpl. rewrite IH. destruct b; simpl.
  - rewrite Pos2Nat.inj_xI. reflexivity.
  - rewrite Pos2Nat.inj_xO. reflexivity.
Qed.

Lemma bnat_gt_length : forall bs, length bs < bnat bs.
Proof. induction bs as [| b r IH]; simpl; [lia | destruct b; simpl; lia]. Qed.

Lemma bnat_ge_two : forall b r, 2 <= bnat (b :: r).
Proof. intros b r. simpl. pose proof (bnat_gt_length r). destruct b; simpl; lia. Qed.

Fixpoint nbits (fuel c : nat) : list bool :=
  match fuel with
  | 0 => []
  | S f =>
      if c <=? 1 then []
      else let (h, b) := hb c in b :: nbits f h
  end.

Lemma nbits_bnat : forall bs fuel, length bs <= fuel -> nbits fuel (bnat bs) = bs.
Proof.
  induction bs as [| b r IH]; intros fuel Hf.
  - destruct fuel; reflexivity.
  - destruct fuel as [| f]; [simpl in Hf; lia |].
    pose proof (bnat_ge_two b r) as H2.
    cbn [nbits]. destruct (Nat.leb_spec (bnat (b :: r)) 1) as [Hle | _]; [lia |].
    change (bnat (b :: r)) with (bit b + 2 * bnat r).
    rewrite hb_unique. f_equal. apply IH. simpl in Hf. lia.
Qed.

(** * Unary fields *)

Fixpoint pun (bs : list bool) (acc : nat) : option (nat * list bool) :=
  match bs with
  | [] => None
  | true :: r => pun r (S acc)
  | false :: r => Some (acc, r)
  end.

Lemma encode_nat_shape : forall n, encode_nat n = repeat true n ++ [false].
Proof. induction n as [| n IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma pun_encode : forall n acc r, pun (encode_nat n ++ r) acc = Some (n + acc, r).
Proof.
  induction n as [| n IH]; intros acc r; [reflexivity |].
  simpl. rewrite IH. f_equal. f_equal. lia.
Qed.

Lemma pun_encode0 : forall n r, pun (encode_nat n ++ r) 0 = Some (n, r).
Proof. intros n r. rewrite pun_encode. rewrite Nat.add_0_r. reflexivity. Qed.

(** * Instruction bits *)

Definition gibits (i : GInstr) : list bool :=
  match i with
  | GHalt c => encode_nat 24 ++ encode_nat c
  | GLoadImm d imm c => encode_nat 8 ++ encode_nat d ++ encode_nat imm ++ encode_nat c
  | GXfer d s c => encode_nat 7 ++ encode_nat d ++ encode_nat s ++ encode_nat c
  | GAdd d a b c => encode_nat 11 ++ encode_nat d ++ encode_nat a ++ encode_nat b ++ encode_nat c
  | GSub d a b c => encode_nat 12 ++ encode_nat d ++ encode_nat a ++ encode_nat b ++ encode_nat c
  | GMul d a b c => encode_nat 35 ++ encode_nat d ++ encode_nat a ++ encode_nat b ++ encode_nat c
  | GAnd d a b c => encode_nat 31 ++ encode_nat d ++ encode_nat a ++ encode_nat b ++ encode_nat c
  | GOr d a b c => encode_nat 32 ++ encode_nat d ++ encode_nat a ++ encode_nat b ++ encode_nat c
  | GShl d a b c => encode_nat 33 ++ encode_nat d ++ encode_nat a ++ encode_nat b ++ encode_nat c
  | GShr d a b c => encode_nat 34 ++ encode_nat d ++ encode_nat a ++ encode_nat b ++ encode_nat c
  | GJump t c => encode_nat 13 ++ encode_nat t ++ encode_nat c
  | GJnez r t c => encode_nat 14 ++ encode_nat r ++ encode_nat t ++ encode_nat c
  end.

Lemma gibits_denote : forall i, gibits i = encode_vm_instruction (g_denote i).
Proof. intro i. destruct i; reflexivity. Qed.

Definition gbits (p : list GInstr) : list bool :=
  encode_nat (length p) ++ flat_map gibits p.

Lemma encode_list_payload_flat : forall p,
  encode_list_payload encode_vm_instruction (g_program p) = flat_map gibits p.
Proof.
  induction p as [| i p IH]; [reflexivity |].
  simpl. rewrite IH, gibits_denote. reflexivity.
Qed.

Lemma gbits_encode_program : forall p, gbits p = encode_program (g_program p).
Proof.
  intro p. unfold gbits, encode_program, encode_list, g_program.
  rewrite map_length. f_equal. symmetry. apply encode_list_payload_flat.
Qed.

Definition genc (p : list GInstr) : nat := bnat (gbits p).

Theorem genc_code : forall p, genc p = guest_program_code p.
Proof.
  intro p. unfold genc, guest_program_code, program_to_nat.
  rewrite bnat_spec, gbits_encode_program. reflexivity.
Qed.

(** * Decoding *)

Definition p1 (bs : list bool) : option (nat * list bool) := pun bs 0.

Definition pinstr (bs : list bool) : option (GInstr * list bool) :=
  match p1 bs with
  | None => None
  | Some (op, r0) =>
      if op =? 24 then
        match p1 r0 with Some (c, r1) => Some (GHalt c, r1) | None => None end
      else if (op =? 8) || (op =? 7) || (op =? 14) then
        match p1 r0 with
        | Some (x, r1) =>
            match p1 r1 with
            | Some (y, r2) =>
                match p1 r2 with
                | Some (c, r3) =>
                    Some ((if op =? 8 then GLoadImm x y c
                           else if op =? 7 then GXfer x y c
                           else GJnez x y c), r3)
                | None => None
                end
            | None => None
            end
        | None => None
        end
      else if op =? 13 then
        match p1 r0 with
        | Some (t, r1) =>
            match p1 r1 with Some (c, r2) => Some (GJump t c, r2) | None => None end
        | None => None
        end
      else if (op =? 11) || (op =? 12) || (op =? 35) || (op =? 31) || (op =? 32)
              || (op =? 33) || (op =? 34) then
        match p1 r0 with
        | Some (d, r1) =>
            match p1 r1 with
            | Some (a, r2) =>
                match p1 r2 with
                | Some (b, r3) =>
                    match p1 r3 with
                    | Some (c, r4) =>
                        Some ((if op =? 11 then GAdd d a b c
                               else if op =? 12 then GSub d a b c
                               else if op =? 35 then GMul d a b c
                               else if op =? 31 then GAnd d a b c
                               else if op =? 32 then GOr d a b c
                               else if op =? 33 then GShl d a b c
                               else GShr d a b c), r4)
                    | None => None
                    end
                | None => None
                end
            | None => None
            end
        | None => None
        end
      else None
  end.

Lemma pinstr_gibits : forall i r, pinstr (gibits i ++ r) = Some (i, r).
Proof.
  intros i r. destruct i; unfold pinstr, p1, gibits; rewrite <- ?app_assoc;
    repeat (rewrite pun_encode0; cbn [Nat.eqb orb]); reflexivity.
Qed.

Fixpoint pinstrs (n : nat) (bs : list bool) : option (list GInstr * list bool) :=
  match n with
  | 0 => Some ([], bs)
  | S k =>
      match pinstr bs with
      | Some (i, r) =>
          match pinstrs k r with
          | Some (is, r') => Some (i :: is, r')
          | None => None
          end
      | None => None
      end
  end.

Lemma pinstrs_flat : forall p r, pinstrs (length p) (flat_map gibits p ++ r) = Some (p, r).
Proof.
  induction p as [| i p IH]; intro r; [reflexivity |].
  simpl. rewrite <- app_assoc, pinstr_gibits, IH. reflexivity.
Qed.

Definition dec_bits (bs : list bool) : option (list GInstr) :=
  match p1 bs with
  | Some (len, r) =>
      match pinstrs len r with Some (p, _) => Some p | None => None end
  | None => None
  end.

Definition dec (c : nat) : option (list GInstr) := dec_bits (nbits c c).

Theorem dec_genc : forall p, dec (genc p) = Some p.
Proof.
  intro p. unfold dec, genc.
  rewrite nbits_bnat by (pose proof (bnat_gt_length (gbits p)); lia).
  unfold dec_bits, gbits, p1. rewrite pun_encode0.
  rewrite <- (app_nil_r (flat_map gibits p)), pinstrs_flat. reflexivity.
Qed.

Corollary dec_code : forall p, dec (guest_program_code p) = Some p.
Proof. intro p. rewrite <- genc_code. apply dec_genc. Qed.


(** * Arithmetic over [nat] *)

Fixpoint nbitw (op : bool -> bool -> bool) (fuel a b : nat) : nat :=
  match fuel with
  | 0 => 0
  | S f =>
      let (ha, ba) := hb a in
      let (hb', bb) := hb b in
      bit (op ba bb) + 2 * nbitw op f ha hb'
  end.

Lemma N_split : forall x : N, x = (2 * N.div2 x + (if N.odd x then 1 else 0))%N.
Proof.
  intro x. pose proof (N.div2_odd x) as E. rewrite E at 1.
  destruct (N.odd x); simpl; lia.
Qed.

Lemma N_of_nat_div2 : forall a, N.of_nat (Nat.div2 a) = N.div2 (N.of_nat a).
Proof. intro a. apply Nat2N.inj_div2. Qed.

Lemma N_odd_of_nat : forall a, N.odd (N.of_nat a) = Nat.odd a.
Proof.
  intro a. pose proof (Nat.div2_odd a) as Ea.
  pose proof (N_split (N.of_nat a)) as En.
  rewrite <- N_of_nat_div2 in En.
  destruct (Nat.odd a) eqn:Ho, (N.odd (N.of_nat a)) eqn:Hn; try reflexivity;
    exfalso; simpl in Ea; lia.
Qed.

Lemma N_land_step : forall x y : N,
  N.land x y = (2 * N.land (N.div2 x) (N.div2 y)
                + (if N.odd x && N.odd y then 1 else 0))%N.
Proof.
  intros x y. rewrite (N_split (N.land x y)).
  rewrite !N.div2_spec, N.shiftr_land, <- !N.div2_spec.
  f_equal. rewrite <- !N.bit0_odd, N.land_spec. reflexivity.
Qed.

Lemma N_lor_step : forall x y : N,
  N.lor x y = (2 * N.lor (N.div2 x) (N.div2 y)
               + (if N.odd x || N.odd y then 1 else 0))%N.
Proof.
  intros x y. rewrite (N_split (N.lor x y)).
  rewrite !N.div2_spec, N.shiftr_lor, <- !N.div2_spec.
  f_equal. rewrite <- !N.bit0_odd, N.lor_spec. reflexivity.
Qed.

Lemma nbitw_land : forall fuel a b, a <= fuel ->
  nbitw andb fuel a b = N.to_nat (N.land (N.of_nat a) (N.of_nat b)).
Proof.
  induction fuel as [| f IH]; intros a b Ha.
  - assert (a = 0) as -> by lia. reflexivity.
  - simpl. rewrite !hb_spec.
    rewrite IH by (apply Nat.div2_decr; lia).
    rewrite !N_of_nat_div2.
    rewrite (N_land_step (N.of_nat a) (N.of_nat b)), !N_odd_of_nat.
    rewrite N2Nat.inj_add, N2Nat.inj_mul.
    destruct (Nat.odd a && Nat.odd b); unfold bit; simpl; lia.
Qed.

Lemma nbitw_lor : forall fuel a b, a + b <= fuel ->
  nbitw orb fuel a b = N.to_nat (N.lor (N.of_nat a) (N.of_nat b)).
Proof.
  induction fuel as [| f IH]; intros a b Hab.
  - assert (a = 0) as -> by lia. assert (b = 0) as -> by lia. reflexivity.
  - simpl. rewrite !hb_spec.
    rewrite IH.
    + rewrite !N_of_nat_div2.
      rewrite (N_lor_step (N.of_nat a) (N.of_nat b)), !N_odd_of_nat.
      rewrite N2Nat.inj_add, N2Nat.inj_mul.
      destruct (Nat.odd a || Nat.odd b); unfold bit; simpl; lia.
    + pose proof (Nat.div2_odd a) as Ea. pose proof (Nat.div2_odd b) as Eb.
      destruct (Nat.odd a), (Nat.odd b); simpl in Ea, Eb; lia.
Qed.

Definition nand (a b : nat) : nat := nbitw andb a a b.
Definition nor (a b : nat) : nat := nbitw orb (a + b) a b.
Definition nshl (a k : nat) : nat := a * pow2 k.
Fixpoint nshr (a k : nat) : nat :=
  match k with
  | 0 => a
  | S k' => nshr (fst (hb a)) k'
  end.

Lemma nand_spec : forall a b, nand a b = u_and a b.
Proof. intros a b. unfold nand, u_and. apply nbitw_land. lia. Qed.

Lemma nor_spec : forall a b, nor a b = u_or a b.
Proof. intros a b. unfold nor, u_or. apply nbitw_lor. lia. Qed.

Lemma nshl_spec : forall a k, nshl a k = u_shl a k.
Proof.
  intros a k. unfold nshl, u_shl. rewrite N.shiftl_mul_pow2.
  rewrite N2Nat.inj_mul, N2Nat.inj_pow, !Nat2N.id, pow2_spec. reflexivity.
Qed.

Lemma nshr_div : forall k a, nshr a k = a / 2 ^ k.
Proof.
  induction k as [| k IH]; intro a.
  - cbn [nshr]. rewrite Nat.pow_0_r, Nat.div_1_r. reflexivity.
  - cbn [nshr]. rewrite IH, hb_spec. cbn [fst].
    rewrite Nat.div2_div, Nat.div_div by (try apply Nat.pow_nonzero; lia).
    rewrite Nat.pow_succ_r'. reflexivity.
Qed.

Lemma nshr_spec : forall a k, nshr a k = u_shr a k.
Proof.
  intros a k. unfold u_shr. rewrite N.shiftr_div_pow2.
  rewrite N2Nat.inj_div, N2Nat.inj_pow, !Nat2N.id, nshr_div. reflexivity.
Qed.

(** * Guest steps and runs *)

Definition nnext (i : GInstr) (pc mu : nat) (g : GRegs) : nat * nat * GRegs :=
  let mu' := mu + g_cost i in
  match i with
  | GHalt _          => (S pc, mu', g)
  | GLoadImm d imm _ => (S pc, mu', g_set g d imm)
  | GXfer d s _      => (S pc, mu', g_set g d (g_get g s))
  | GAdd d a b _     => (S pc, mu', g_set g d (g_get g a + g_get g b))
  | GSub d a b _     => (S pc, mu', g_set g d (g_get g a - g_get g b))
  | GMul d a b _     => (S pc, mu', g_set g d (g_get g a * g_get g b))
  | GAnd d a b _     => (S pc, mu', g_set g d (nand (g_get g a) (g_get g b)))
  | GOr d a b _      => (S pc, mu', g_set g d (nor (g_get g a) (g_get g b)))
  | GShl d a b _     => (S pc, mu', g_set g d (nshl (g_get g a) (g_get g b)))
  | GShr d a b _     => (S pc, mu', g_set g d (nshr (g_get g a) (g_get g b)))
  | GJump t _        => (t, mu', g)
  | GJnez r t _      => (if Nat.eqb (g_get g r) 0 then S pc else t, mu', g)
  end.

Lemma nnext_spec : forall i pc mu g, nnext i pc mu g = g_next i pc mu g.
Proof.
  intros i pc mu g. destruct i; unfold nnext, g_next;
    rewrite ?nand_spec, ?nor_spec, ?nshl_spec, ?nshr_spec; reflexivity.
Qed.

Definition nstep (p : list GInstr) (c : GConf) : GConf :=
  match nth_error p c.(gc_pc) with
  | Some i =>
      let '(pc', mu', g') := nnext i c.(gc_pc) c.(gc_mu) c.(gc_g) in
      {| gc_pc := pc'; gc_mu := mu'; gc_g := g' |}
  | None => c
  end.

Fixpoint nrun (n : nat) (p : list GInstr) (c : GConf) : GConf :=
  match n with
  | 0 => c
  | S n' => nrun n' p (nstep p c)
  end.

Lemma nstep_spec : forall p c, nstep p c = g_step p c.
Proof.
  intros p c. unfold nstep, g_step. destruct (nth_error p (gc_pc c)); [| reflexivity].
  rewrite nnext_spec. reflexivity.
Qed.

Theorem nrun_spec : forall n p c, nrun n p c = g_run n p c.
Proof.
  induction n as [| n IH]; intros p c; [reflexivity |].
  simpl. rewrite nstep_spec. apply IH.
Qed.


(** * Pairing and the specializer *)

(** [npair] is [g_pair] from [VMGuestRecursion] with [pow2] for [2 ^ x]. *)
Definition npair (x y : nat) : nat := (2 * y + 1) * pow2 x.

Fixpoint tz (fuel z acc : nat) : nat * nat :=
  match fuel with
  | 0 => (acc, 0)
  | S f => let (h, b) := hb z in if b then (acc, h) else tz f h (S acc)
  end.

Definition unpair (z : nat) : nat * nat := tz z z 0.

Lemma pow2_gt : forall x, x < pow2 x.
Proof. induction x as [| x IH]; simpl; lia. Qed.

Lemma tz_npair : forall x y fuel acc, x < fuel -> tz fuel (npair x y) acc = (x + acc, y).
Proof.
  induction x as [| x IH]; intros y fuel acc Hf; destruct fuel as [| f]; try lia.
  - cbn [tz]. unfold npair. simpl pow2. rewrite Nat.mul_1_r.
    replace (2 * y + 1) with (bit true + 2 * y) by (simpl; lia).
    rewrite hb_unique. reflexivity.
  - cbn [tz]. replace (npair (S x) y) with (bit false + 2 * npair x y)
      by (unfold npair; simpl; lia).
    rewrite hb_unique. rewrite IH by lia. f_equal. lia.
Qed.

Theorem unpair_npair : forall x y, unpair (npair x y) = (x, y).
Proof.
  intros x y. unfold unpair. rewrite tz_npair; [f_equal; lia |].
  unfold npair. pose proof (pow2_gt x). nia.
Qed.

Definition sp_prefix (x tail : nat) : list GInstr :=
  [ GLoadImm 2 1 0;
    GAdd 0 0 0 0;
    GAdd 0 0 2 0;
    GLoadImm 1 x 0;
    GJnez 1 7 0;
    GLoadImm 2 0 0;
    GJump tail 0;
    GAdd 0 0 0 0;
    GSub 1 1 2 0;
    GJump 4 0 ].

Definition sp (p : list GInstr) (x : nat) : list GInstr := sp_prefix x 10 ++ reloc 10 p.

Lemma sp_wf : forall p x, g_wf_program p -> g_wf_program (sp p x).
Proof.
  intros p x Hp. unfold sp, g_wf_program. apply Forall_app. split.
  - repeat constructor; unfold g_wf; simpl; lia.
  - apply reloc_wf. exact Hp.
Qed.

(** * The evaluator as a fuel function *)

Definition hfun (pack : GRegs -> nat -> nat) (D : list GInstr) (fuel z : nat) : option nat :=
  let (c, y) := unpair z in
  match dec c with
  | None => None
  | Some p0 =>
      let cd := nrun fuel D (g_input (genc (sp p0 c))) in
      if length D <=? gc_pc cd then
        match dec (gr0 (gc_g cd)) with
        | None => None
        | Some q =>
            let cq := nrun fuel q (g_input y) in
            if length q <=? gc_pc cq then Some (pack (gc_g cq) (gc_mu cq)) else None
        end
      else None
  end.

Lemma run_stable : forall p c n m,
  length p <= gc_pc (g_run n p c) -> n <= m -> g_run m p c = g_run n p c.
Proof. intros p c n m Ht Hle. eapply g_run_terminal_after; eassumption. Qed.

Theorem hfun_mono : forall pack D fuel fuel' z m,
  hfun pack D fuel z = Some m -> fuel <= fuel' -> hfun pack D fuel' z = Some m.
Proof.
  intros pack D fuel fuel' z m H Hle. unfold hfun in *.
  destruct (unpair z) as [c y]. destruct (dec c) as [p0 |]; [| discriminate].
  rewrite nrun_spec in *.
  destruct (Nat.leb_spec (length D) (gc_pc (g_run fuel D (g_input (genc (sp p0 c))))))
    as [HD | HD]; [| discriminate].
  rewrite (@run_stable _ _ _ _ HD Hle).
  destruct (Nat.leb_spec (length D) (gc_pc (g_run fuel D (g_input (genc (sp p0 c))))));
    [| lia].
  destruct (dec (gr0 (gc_g (g_run fuel D (g_input (genc (sp p0 c))))))) as [q |];
    [| discriminate].
  rewrite nrun_spec in *.
  destruct (Nat.leb_spec (length q) (gc_pc (g_run fuel q (g_input y)))) as [Hq | Hq];
    [| discriminate].
  rewrite (@run_stable _ _ _ _ Hq Hle).
  destruct (Nat.leb_spec (length q) (gc_pc (g_run fuel q (g_input y)))); [exact H | lia].
Qed.

(** Two halting runs of the same program from the same start agree. *)
Lemma run_det : forall p c n1 n2,
  length p <= gc_pc (g_run n1 p c) -> length p <= gc_pc (g_run n2 p c) ->
  g_run n1 p c = g_run n2 p c.
Proof.
  intros p c n1 n2 H1 H2. destruct (Nat.le_ge_cases n1 n2) as [Hle | Hle].
  - symmetry. apply run_stable; assumption.
  - apply run_stable; assumption.
Qed.

(** The meaning of the fuel function: on the pair of a program's code and an
    input, it eventually returns [m] exactly when the transformed specialized
    program halts on that input with registers [g] and ledger [mu] packed as
    [m]. *)
Theorem hfun_sem : forall pack D F e y m,
  g_represents_transformer D F ->
  g_wf_program e ->
  (exists fuel, hfun pack D fuel (npair (genc e) y) = Some m) <->
  (exists g mu, m = pack g mu /\ g_beh (F (sp e (genc e))) y g mu).
Proof.
  intros pack D F e y m [HwfD HD] He.
  set (c := genc e). set (p := sp e c).
  assert (Hp : g_wf_program p) by (apply sp_wf; exact He).
  destruct (HD p Hp) as (gD & muD & (nD & HtD & HgD & _) & Hcode).
  unfold g_terminal in HtD.
  assert (Hdec : dec c = Some e) by apply dec_genc.
  assert (Hgenc : genc p = guest_program_code p) by apply genc_code.
  split.
  - intros [fuel Hf]. unfold hfun in Hf. rewrite unpair_npair, Hdec in Hf.
    fold p in Hf. rewrite Hgenc, !nrun_spec in Hf.
    destruct (Nat.leb_spec (length D) (gc_pc (g_run fuel D (g_input (guest_program_code p)))))
      as [HtF | _]; [| discriminate].
    rewrite (@run_det D _ fuel nD HtF HtD), HgD, Hcode, dec_code in Hf.
    rewrite nrun_spec in Hf.
    destruct (Nat.leb_spec (length (F p)) (gc_pc (g_run fuel (F p) (g_input y))))
      as [Hq | _]; [| discriminate].
    injection Hf as <-.
    exists (gc_g (g_run fuel (F p) (g_input y))), (gc_mu (g_run fuel (F p) (g_input y))).
    split; [reflexivity |]. exists fuel. repeat split. exact Hq.
  - intros (g & mu & -> & nq & Htq & Hg & Hmu).
    unfold g_terminal in Htq.
    exists (nD + nq). unfold hfun. rewrite unpair_npair, Hdec.
    fold p. rewrite Hgenc, !nrun_spec.
    rewrite (@run_stable D _ nD (nD + nq) HtD) by lia.
    destruct (Nat.leb_spec (length D) (gc_pc (g_run nD D (g_input (guest_program_code p)))));
      [| lia].
    rewrite HgD, Hcode, dec_code, nrun_spec.
    rewrite (@run_stable (F p) _ nq (nD + nq) Htq) by lia.
    destruct (Nat.leb_spec (length (F p)) (gc_pc (g_run nq (F p) (g_input y)))); [| lia].
    rewrite Hg, Hmu. reflexivity.
Qed.

Print Assumptions dec_code.
Print Assumptions genc_code.
Print Assumptions nrun_spec.
Print Assumptions unpair_npair.
Print Assumptions hfun_mono.
Print Assumptions hfun_sem.
