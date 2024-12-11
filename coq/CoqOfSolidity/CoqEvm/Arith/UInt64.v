From Coq Require Import ZArith Lia.
From Coq Require Import Uint63.
From Coq Require Bool.

From CoqOfSolidity Require Import Arith2 UInt63 Nibble.

Definition uint64 := (bool * int)%type.
Definition t := uint64.

Local Open Scope Z_scope.

Definition Z_of_uint64 (a: uint64)
:= match a with
   | (false, n) => Uint63.to_Z n
   | (true , n) => Uint63.to_Z n + Uint63.wB
   end.

Definition Z_of_uint64_lor (a: uint64)
:= match a with
   | (false, n) => Uint63.to_Z n
   | (true , n) => Z.lor (Uint63.to_Z n) Uint63.wB
   end.

Lemma Z_of_uint64_lor_ok (a: uint64):
  Z_of_uint64_lor a = Z_of_uint64 a.
Proof.
unfold Z_of_uint64_lor.
destruct a as (b, n).
rewrite<- Arith2.Z_add_nocarry_lor. { trivial. }
apply Arith2.Z_land_pow2_small. { apply to_Z_bounded. }
apply Nat2Z.is_nonneg.
Qed.

Definition Z_of_uint64_lxor (a: uint64)
:= match a with
   | (false, n) => Uint63.to_Z n
   | (true , n) => Z.lxor (Uint63.to_Z n) Uint63.wB
   end.

Lemma Z_of_uint64_lxor_ok (a: uint64):
  Z_of_uint64_lxor a = Z_of_uint64 a.
Proof.
unfold Z_of_uint64_lxor.
destruct a as (b, n).
rewrite<- Z.add_nocarry_lxor. { trivial. }
apply Arith2.Z_land_pow2_small. { apply to_Z_bounded. }
apply Nat2Z.is_nonneg.
Qed.

Lemma Z_of_uint64_lower (a: uint64):
  0 <= Z_of_uint64 a.
Proof.
destruct a as (hi, lo).
assert(B := Uint63.to_Z_bounded lo).
destruct B as (L, H).
destruct hi; unfold Z_of_uint64; lia.
Qed.

Lemma Z_of_uint64_upper (a: uint64):
  Z_of_uint64 a < 2^64.
Proof.
destruct a as (hi, lo).
assert(B := Uint63.to_Z_bounded lo).
destruct B as (_, H).
assert (E: Uint63.wB = 2^63). { unfold Uint63.wB. f_equal. }
destruct hi; unfold Z_of_uint64; lia.
Qed.

Definition Z_of_uint64' (a: uint64)
:= let (b, n) := a in
   Uint63.to_Z n + (if b then 1 else 0) * Uint63.wB.

Lemma Z_of_uint64_alt (a: uint64):
  Z_of_uint64' a = Z_of_uint64 a.
Proof.
unfold Z_of_uint64'. unfold Z_of_uint64.
destruct a as (b, n). destruct b; lia.
Qed.

Definition Z_of_uint64_lor' (a: uint64)
:= let (b, n) := a in
   Z.lor (Uint63.to_Z n) ((if b then 1 else 0) * Uint63.wB).

Lemma Z_of_uint64_lor'_ok (a: uint64):
  Z_of_uint64_lor' a = Z_of_uint64' a.
Proof.
unfold Z_of_uint64_lor'.
destruct a as (b, n).
rewrite<- Arith2.Z_add_nocarry_lor. { trivial. }
destruct b.
{
  rewrite Z.mul_1_l. apply Arith2.Z_land_pow2_small. 
  { apply to_Z_bounded. } apply Nat2Z.is_nonneg.
}
rewrite Z.mul_0_l. rewrite Z.land_0_r. trivial.
Qed.

Definition uint64_of_Z (z: Z)
                        (lower: 0 <= z)
                        (upper: z < 2^64)
: uint64
:= (2^63 <=? z, Uint63.of_Z z).

Lemma uint64_of_Z_of_uint64 (a: uint64):
  uint64_of_Z (Z_of_uint64 a) (Z_of_uint64_lower a) (Z_of_uint64_upper a) = a.
Proof.
assert (E: Uint63.wB = 2^63). { unfold Uint63.wB. f_equal. }
destruct a as (hi, lo).
assert(B := Uint63.to_Z_bounded lo).
destruct hi; unfold Z_of_uint64; unfold uint64_of_Z.
{
  rewrite E. f_equal.
  { rewrite Z.leb_le. lia. }
  rewrite<- E. clear E.
  apply Uint63.to_Z_inj. rewrite Uint63.of_Z_spec.
  rewrite Z.add_comm.
  rewrite<- Zplus_mod_idemp_l.
  rewrite Z_mod_same_full.
  rewrite Z.add_0_l.
  remember (Uint63.to_Z lo) as n. clear Heqn.
  exact (Z.mod_small _ _ B).
}
rewrite<- E.
f_equal. { rewrite Z.leb_gt. tauto. }
apply Uint63.of_to_Z.
Qed.

Lemma Z_of_uint64_of_Z (z: Z)
                        (lower: 0 <= z)
                        (upper: z < 2^64):
  Z_of_uint64 (uint64_of_Z z lower upper) = z.
Proof.
assert (E: Uint63.wB = 2^63). { unfold Uint63.wB. f_equal. }
unfold Z_of_uint64. unfold uint64_of_Z.
remember (2 ^ 63 <=? z) as is_high.
rewrite Uint63.of_Z_spec.
symmetry in Heqis_high.
destruct is_high.
{
  rewrite Z.leb_le in Heqis_high.
  rewrite E. clear E.
  remember (z - 2^63) as y.
  assert (YL: 0 <= y) by lia.
  assert (YU: y < 2^63) by lia.
  assert (R: z mod 2^63 = y mod 2^63).
  {
    subst.
    rewrite<- Zminus_mod_idemp_r.
    rewrite Z_mod_same_full.
    rewrite Z.sub_0_r.
    trivial.
  }
  rewrite R.
  rewrite (Z.mod_small _ _ (conj YL YU)).
  lia.
}
rewrite Z.leb_gt in Heqis_high.
apply Z.mod_small. tauto.
Qed.

Definition uint64_of_Z_mod (z: Z)
: uint64
:= (Z.testbit z 63, Uint63.of_Z z).

Lemma uint64_mod_pos_bound (a: Z):
  0 <= a mod 2^64 < 2^64.
Proof.
apply Z.mod_pos_bound.
rewrite<- Z.ltb_lt.
trivial.
Qed.
 
Lemma uint64_of_Z_mod_ok (z: Z):
  uint64_of_Z_mod z = uint64_of_Z (z mod 2^64)
                                  (proj1 (uint64_mod_pos_bound z))
                                  (proj2 (uint64_mod_pos_bound z)).
Proof.
unfold uint64_of_Z. unfold uint64_of_Z_mod.
f_equal.
{
  rewrite<- (Z.mod_pow2_bits_low z 64 63) by now rewrite<- Z.ltb_lt.
  assert (B := uint64_mod_pos_bound z).
  remember (z mod 2 ^ 64) as x. clear Heqx.
  rewrite (Z.testbit_odd x 63).
  rewrite Z.shiftr_div_pow2 by now rewrite<- Z.leb_le.
  remember (2 ^ 63 <=? x) as f. symmetry in Heqf.
  destruct f.
  {
    rewrite Z.leb_le in Heqf.
    assert(L: 1 <= x / 2 ^ 63).
    {
      rewrite<- (Z.div_same (2^63)) by discriminate.
      apply Z.div_le_mono. { rewrite<- Z.ltb_lt. trivial. }
      assumption.
    }
    assert (U: x / 2^63 <= (2 ^ 64 - 1) / 2 ^ 63).
    {
      apply Z.div_le_mono. { rewrite<- Z.ltb_lt. trivial. }
      lia.
    }
    replace ((2 ^ 64 - 1) / 2 ^ 63) with 1 in U by trivial.
    assert (E: x / 2 ^ 63 = 1) by lia.
    now rewrite E.
  }
  rewrite (Logic2.b_false (Z.leb_le _ _)) in Heqf.
  apply Z.nle_gt in Heqf.
  replace (x / 2 ^ 63) with 0. 2:{ symmetry. apply Z.div_small. tauto. }
  trivial.
}
apply to_Z_inj.
repeat rewrite of_Z_spec. 
apply Znumtheory.Zmod_div_mod; try rewrite<- Z.ltb_lt; trivial.
replace (2^64) with (2 * wB) by trivial.
apply Z.divide_factor_r.
Qed.

Lemma Z_of_uint64_of_Z_mod (z: Z):
  Z_of_uint64 (uint64_of_Z_mod z) = z mod 2^64.
Proof.
rewrite uint64_of_Z_mod_ok.
rewrite Z_of_uint64_of_Z.
trivial.
Qed.

Definition uint64_0: uint64 := (false, 0%uint63).
Lemma uint64_0_ok:
  Z_of_uint64 uint64_0 = 0.
Proof. trivial. Qed.
Definition uint64_1: uint64 := (false, 1%uint63).
Lemma uint64_1_ok:
  Z_of_uint64 uint64_1 = 1.
Proof. trivial. Qed.
Definition uint64_max_value: uint64 := (true, max_int).
Lemma uint64_max_value_ok:
  Z_of_uint64 uint64_max_value = 2^64 - 1.
Proof. trivial. Qed.

(*******************************************************************************)

Definition add (a b: uint64)
: uint64
:= let (ha, la) := a in
   let (hb, lb) := b in
   let x := xorb ha hb in
   match Uint63.addc la lb with
   | DoubleType.C0 c => (x, c)
   | DoubleType.C1 c => (negb x, c)
   end.

Ltac wB_up
:= repeat (rewrite (Z.add_comm _ Uint63.wB)
        || rewrite (Z.add_comm _ (_ * Uint63.wB)));
   repeat rewrite Z.add_assoc;
   repeat rewrite<- Z.mul_add_distr_r.

Lemma mod_wB (x: Z):
  (x * Uint63.wB) mod 2 ^ 64 = if Z.odd x then Uint63.wB else 0.
Proof.
remember (Z.odd x) as last_bit.
rewrite (Zdiv2_odd_eqn x). subst.
rewrite Z.mul_add_distr_r.
replace (2 * Z.div2 x) with (Z.div2 x * 2) by apply Z.mul_comm.
rewrite<- Z.mul_assoc.
replace (2 * Uint63.wB) with (2 ^ 64)%Z by trivial.
rewrite Z.add_comm. rewrite Z.mod_add by discriminate.
now destruct (Z.odd x).
Qed.

Lemma add_ok (a b: uint64):
  Z_of_uint64 (add a b) = ((Z_of_uint64 a + Z_of_uint64 b) mod 2^64).
Proof.
assert (L := Z_of_uint64_lower (add a b)).
assert (U := Z_of_uint64_upper (add a b)).
repeat rewrite<- Z_of_uint64_alt in *.
rewrite<- (Z.mod_small (Z_of_uint64' (add a b)) (2 ^ 64)) by tauto.
unfold add. destruct a as (ha, la). destruct b as (hb, lb).
assert (R := Uint63.addc_spec la lb).
cbn in L. cbn in U.
unfold DoubleType.interp_carry in R.
remember (Uint63.addc la lb) as x. clear Heqx.
unfold Z_of_uint64'.
destruct x; 
  [rewrite R | try rewrite Z.mul_1_l in R;
               replace (Uint63.to_Z i) with (Uint63.to_Z la + Uint63.to_Z lb + (-1) * Uint63.wB) by lia];
  wB_up; wB_up; repeat rewrite<- Z.add_assoc;
  apply Z_mod_add_r;
  destruct ha, hb; rewrite mod_wB; trivial.
Qed.

(*******************************************************************************)

Definition shr_uint63 (a: uint64) (sh: uint63)
: uint64
:= if (sh =? 0)%uint63
     then a
     else let (hi, lo) := a in
       (false, if hi
                 then (((1 << 62) >> (sh - 1)) lor (lo >> sh))%uint63
                 else lsr lo sh).

Lemma shr_uint63_ok (a: uint64) (sh: uint63):
  Z_of_uint64 (shr_uint63 a sh) = Z.shiftr (Z_of_uint64 a) (Uint63.to_Z sh).
Proof.
unfold shr_uint63.
remember ((sh =? 0)%uint63) as sh0 eqn:Sh0. symmetry in Sh0. destruct sh0.
{ rewrite Uint63.eqb_spec in Sh0. now subst. }
assert(BS := to_Z_bounded sh). remember (to_Z sh) as s.
assert(SPos: 0 < s).
{
  enough (s <> 0) by lia.
  intro H. subst.
  replace 0 with (to_Z 0) in H by trivial.
  apply to_Z_inj in H.
  apply eqb_spec in H.
  rewrite H in Sh0.
  discriminate.
}
destruct a as (hi, lo).
destruct hi; unfold Z_of_uint64.
2:{
  (* low case *)
  rewrite Uint63.lsr_spec.
  rewrite Z.shiftr_div_pow2 by tauto.
  now subst.
}
(* high case *)
rewrite Uint63.lor_spec'.
rewrite Uint63.lsr_spec.
rewrite Uint63.lsr_spec.
rewrite Uint63.lsl_spec.
rewrite Uint63.sub_spec.
replace (to_Z 1) with 1 by trivial.
replace (to_Z 62) with 62 by trivial.
rewrite<- Heqs.
clear Sh0 Heqs.
assert(BN := to_Z_bounded lo). remember (to_Z lo) as n. clear Heqn.
rewrite Z.mul_1_l. rewrite Z.shiftr_div_pow2 by tauto.
replace (2 ^ 62 mod wB) with (2 ^ 62) by trivial.
replace ((s - 1) mod wB) with (s - 1). 2:{ symmetry. apply Z.mod_small. lia. }
assert (CS: 64 <= s \/ s <= 63) by lia.
case CS; clear CS; intro CS.
{
  (* large shift, everything is 0 *)
  replace (n / 2 ^ s) with 0.
  2:{
    symmetry. apply Z.div_small.
    split. { tauto. }
    replace Uint63.wB with (2 ^ 63) in * by trivial.
    apply (Z.lt_trans n (2^63) (2^s)). { tauto. }
    apply Z.pow_lt_mono_r; lia.
  }
  rewrite Z.lor_0_r. 
  rewrite Z.div_small.
  2:{
    split. { lia. }
    apply Z.pow_lt_mono_r; lia.
  }
  rewrite Z.div_small. { trivial. }
  split. { lia. }
  apply (Z.lt_le_trans _ (2^64) (2^s)).
  { replace (2 ^ 64) with (wB + wB) by trivial. lia. }
  apply Z.pow_le_mono_r; lia.
}
replace (2 ^ 62 / 2 ^ (s - 1)) with (2 ^ 63 / 2 ^ s). 
2:{
  replace (2 ^ 63) with (2 * (2 ^ 62)) by trivial.
  replace (2 ^ s) with ((2 ^ (1 + (s - 1)))) by now replace (1 + (s - 1)) with s by lia.
  rewrite Z.pow_add_r; try lia.
  rewrite Z.div_mul_cancel_l; lia.
}
repeat rewrite<- Z.shiftr_div_pow2 by tauto.
rewrite<- Z.shiftr_lor.
f_equal.
rewrite<- Arith2.Z_add_nocarry_lor. { apply Z.add_comm. }
rewrite Z.land_comm.
apply Arith2.Z_land_pow2_small. { tauto. }
now rewrite<- Z.leb_le.
Qed.

(*******************************************************************************)

Definition shl_uint63 (a: uint64) (sh: uint63)
: uint64
:= if (sh =? 0)%uint63
     then a
     else let (hi, lo) := a in
       (get_digit lo (63 - sh), lsl lo sh).

Lemma shl_uint63_ok (a: uint64) (sh: uint63):
  Z_of_uint64 (shl_uint63 a sh) = (Z.shiftl (Z_of_uint64 a) (Uint63.to_Z sh) mod 2^64)%Z.
Proof.
repeat rewrite<- Z_of_uint64_alt. repeat rewrite<- Z_of_uint64_lor'_ok.
unfold shl_uint63.
remember ((sh =? 0)%uint63) as sh0 eqn:Sh0. symmetry in Sh0. destruct sh0.
{ 
  rewrite Uint63.eqb_spec in Sh0. subst. rewrite Z.shiftl_0_r.
  symmetry. apply Z.mod_small.
  rewrite Z_of_uint64_lor'_ok.
  rewrite Z_of_uint64_alt.
  split. { apply Z_of_uint64_lower. } apply Z_of_uint64_upper.
}
assert(BS := to_Z_bounded sh). remember (to_Z sh) as s.
assert(SPos: 0 < s).
{
  enough (s <> 0) by lia.
  intro H. subst.
  replace 0 with (to_Z 0) in H by trivial.
  apply to_Z_inj in H.
  apply eqb_spec in H.
  rewrite H in Sh0.
  discriminate.
}
destruct a as (hi, lo).
rewrite uint63_testbit_Z.
unfold Z_of_uint64_lor'.
rewrite Uint63.lsl_spec.
apply Z.bits_inj'. intros k Knonneg.
rewrite Z.lor_spec.
rewrite<- Z.shiftl_mul_pow2 by now subst.
rewrite<- Heqs.
assert (BN := to_Z_bounded lo). remember (to_Z lo) as n.
rewrite Z.shiftl_lor.
replace wB with (2^63) by trivial.
repeat rewrite<- Z.land_ones.
rewrite Z.land_lor_distr_l.
replace (Z.land (Z.shiftl ((if hi then 1 else 0) * 2 ^ 63) s) (Z.ones 64)) with 0.
3-4: now rewrite<- Z.leb_le.
2:{
  destruct hi. 2:{ rewrite Z.mul_0_l. rewrite Z.shiftl_0_l. rewrite Z.land_0_l. trivial. }
  symmetry.
  rewrite Z.mul_1_l.
  rewrite Z.shiftl_mul_pow2 by tauto.
  rewrite Z.land_ones by now rewrite<- Z.leb_le.
  rewrite<- Z.pow_add_r; try lia.
  replace (2 ^ (63 + s)) with (2^(s - 1) * 2^64).
  2:{ rewrite<- Z.pow_add_r; try f_equal; lia. }
  apply Z_mod_mult.
}
rewrite Z.lor_0_r.
repeat rewrite Z.land_spec.
repeat rewrite Z.testbit_ones_nonneg; try lia.
remember (Z.testbit (Z.shiftl n s) k) as x.
assert (CK: k <> 63 \/ k = 63) by lia.
case CK; clear CK; intro CK.
{
  replace (Z.testbit ((if Z.testbit n (to_Z (63 - sh)%uint63) then 1 else 0) * 2 ^ 63) k) with false.
  2:{
    symmetry.
    destruct (Z.testbit n (to_Z (63 - sh)%uint63)); [ rewrite Z.mul_1_l | rewrite Z.mul_0_l ].
    { apply Z.pow2_bits_false. lia. }
    apply Z.bits_0.
  }
  rewrite Bool.orb_false_r.
  f_equal.
  rewrite Arith2.Z_ltb_lt_quad. split; lia.
}
subst k x.
replace (63 <? 63) with false by trivial.
replace (63 <? 64) with true by trivial.
rewrite Bool.andb_false_r. rewrite Bool.orb_false_l. rewrite Bool.andb_true_r.
rewrite Arith2.Z_testbit_flag_mul_pow2 by lia.
rewrite Z.shiftl_spec by lia.
rewrite sub_spec. replace (to_Z 63) with 63 by trivial.
rewrite<- Heqs.
assert (WB63: 63 < wB) by now rewrite<- Z.ltb_lt.
assert (Q: (63 - s) mod wB = 63 - s \/ 63 < (63 - s) mod wB).
{
  assert(B: -wB < 63 - s) by lia.
  assert(WBNZ: wB <> 0) by discriminate.
  assert(D := Z.div_mod (63 - s) wB WBNZ).
  assert(WBPos: 0 < wB) by lia.
  assert(BQ := Z.mod_pos_bound (63 - s) wB WBPos).
  remember ((63 - s) mod wB) as q.
  clear Heqq.
  assert (L: -1 <= (63 - s) / wB) by nia.
  assert (U: (63 - s) / wB <= 0) by nia.
  assert (T: (63 - s) / wB = 0 \/ (63 - s) / wB = -1) by lia.
  case T; clear T; intro T; lia.
}
case Q; clear Q; intro Q. { now rewrite Q. }
assert (S63: 63 < s).
{
  apply Z.nle_gt. intro H.
  replace ((63 - s) mod wB) with (63 - s) in *. 
  2:{ 
    rewrite Z.mod_small. { trivial. } 
    lia.
  }
  lia.
}
rewrite (Z.testbit_neg_r n (63 - s)) by lia.
apply Arith2.Z_testbit_small. { tauto. }
refine (Z.lt_trans n wB _ _ _). { tauto. }
replace wB with (2^63) by trivial.
apply Z.pow_lt_mono_r; try lia.
apply Z.mod_pos_bound.
trivial. apply Q.
Qed.

(*******************************************************************************)

Definition bitwise_or (a b: uint64)
: uint64
:= ((fst a || fst b)%bool,  Uint63.lor (snd a) (snd b)).

Lemma bitwise_or_ok (a b: uint64):
  Z_of_uint64 (bitwise_or a b) = (Z.lor (Z_of_uint64 a) (Z_of_uint64 b)).
Proof.
repeat rewrite<- Z_of_uint64_lor_ok.
destruct a as (a_hi, a_lo).
destruct b as (b_hi, b_lo).
unfold Z_of_uint64_lor. unfold bitwise_or.
destruct a_hi, b_hi;
  match goal with
  |- (if ?cond then _ else _) = ?rhs  => remember cond as c; cbn in Heqc; subst
  end;
  repeat rewrite lor_spec';
  replace (snd (_, a_lo)) with a_lo by trivial;
  replace (snd (_, b_lo)) with b_lo by trivial;
  remember (to_Z a_lo) as x;
  remember (to_Z b_lo) as y;
  repeat rewrite Z.lor_assoc; trivial.
{
  (* goal: Z.lor (Z.lor x y) wB = Z.lor (Z.lor (Z.lor x wB) y) wB *)
  repeat rewrite<- Z.lor_assoc. f_equal.
  rewrite Z.lor_comm.
  rewrite Z.lor_assoc.
  now replace (Z.lor wB wB) with wB by trivial.
}
(* goal: Z.lor (Z.lor x y) wB = Z.lor (Z.lor x wB) y *)
repeat rewrite<- Z.lor_assoc. f_equal.
apply Z.lor_comm.
Qed.

(*******************************************************************************)

Definition bitwise_xor (a b: uint64)
: uint64
:= (xorb (fst a) (fst b),  Uint63.lxor (snd a) (snd b)).

Lemma bitwise_xor_ok (a b: uint64):
  Z_of_uint64 (bitwise_xor a b) = (Z.lxor (Z_of_uint64 a) (Z_of_uint64 b)).
Proof.
repeat rewrite<- Z_of_uint64_lxor_ok.
destruct a as (a_hi, a_lo).
destruct b as (b_hi, b_lo).
unfold Z_of_uint64_lxor. unfold bitwise_xor.
destruct a_hi, b_hi;
  match goal with
  |- (if ?cond then _ else _) = ?rhs  => remember cond as c; cbn in Heqc; subst
  end;
  repeat rewrite lxor_spec';
  replace (snd (_, a_lo)) with a_lo by trivial;
  replace (snd (_, b_lo)) with b_lo by trivial;
  remember (to_Z a_lo) as x;
  remember (to_Z b_lo) as y; 
  repeat rewrite Z.lxor_assoc; trivial.
{
  (* goal: Z.lxor x y = Z.lxor x (Z.lxor wB (Z.lxor y wB)) *)
  rewrite (Z.lxor_comm y wB). f_equal.
  rewrite<- Z.lxor_assoc.
  now replace (Z.lor wB wB) with wB by trivial.
}
f_equal. apply Z.lxor_comm.
Qed.

(*******************************************************************************)

Definition bitwise_and (a b: uint64)
: uint64
:= ((fst a && fst b)%bool,  Uint63.land (snd a) (snd b)).

Lemma bitwise_and_ok (a b: uint64):
  Z_of_uint64 (bitwise_and a b) = (Z.land (Z_of_uint64 a) (Z_of_uint64 b)).
Proof.
repeat rewrite<- Z_of_uint64_lor_ok.
destruct a as (a_hi, a_lo).
destruct b as (b_hi, b_lo).
unfold Z_of_uint64_lor. unfold bitwise_and.
destruct a_hi, b_hi;
  match goal with
  |- (if ?cond then _ else _) = ?rhs  => remember cond as c; cbn in Heqc; subst
  end;
  repeat rewrite land_spec';
  replace (snd (_, a_lo)) with a_lo by trivial;
  replace (snd (_, b_lo)) with b_lo by trivial;
  remember (to_Z a_lo) as x;
  remember (to_Z b_lo) as y;
  repeat rewrite Z.land_assoc; trivial.
{ apply Z.lor_land_distr_l. }
{ 
  rewrite Z.land_lor_distr_l.
  replace (Z.land wB y) with 0. { now rewrite Z.lor_0_r. }
  symmetry. rewrite Z.land_comm. apply Arith2.Z_land_pow2_small.
  { subst. apply to_Z_bounded. }
  rewrite<- Z.leb_le. trivial.
}
rewrite Z.land_lor_distr_r.
replace (Z.land x wB) with 0. { now rewrite Z.lor_0_r. }
symmetry. apply Arith2.Z_land_pow2_small.
{ subst. apply to_Z_bounded. }
rewrite<- Z.leb_le. trivial.
Qed.

(*******************************************************************************)

Definition bitwise_not (a: uint64)
: uint64
:= (negb (fst a),  Uint63.lxor (snd a) (of_Z (-1))).

Lemma bitwise_not_via_xor (a: uint64):
  bitwise_not a = bitwise_xor a uint64_max_value.
Proof.
trivial.
Qed.

Lemma bitwise_not_ok (a: uint64):
  Z_of_uint64 (bitwise_not a) = (Z.lnot (Z_of_uint64 a)) mod 2^64.
Proof.
rewrite bitwise_not_via_xor. rewrite bitwise_xor_ok.
rewrite<- Z.lxor_m1_r. rewrite<- Z.land_ones. 2: { now rewrite<- Z.leb_le. }
assert (L := Z_of_uint64_lower a).
assert (U := Z_of_uint64_upper a).
remember (Z_of_uint64 a) as x. clear Heqx.
rewrite uint64_max_value_ok.
replace (2 ^ 64 - 1) with (Z.ones 64) by trivial.
rewrite Z_land_lxor_distr_l.
f_equal.
symmetry. apply Z.land_ones_low. { assumption. }
apply Arith2.Z_log2_lt_pow2; try assumption.
now rewrite<- Z.ltb_lt.
Qed.

(*******************************************************************************)

Definition uint64_of_be_bytes (b: byte * byte * byte * byte * byte * byte * byte * byte)
: uint64
:= match b with
   | (b7, b6, b5, b4, b3, b2, b1, b0) =>
       bitwise_or (shl_uint63 (false, int_of_byte b7) 56%uint63)
                  (false, ((int_of_byte b6 << 48) lor (int_of_byte b5 << 40) lor (int_of_byte b4 << 32)
                       lor (int_of_byte b3 << 24) lor (int_of_byte b2 << 16) lor (int_of_byte b1 << 8)
                       lor int_of_byte b0)%uint63)
   end.

Definition uint64_to_be_bytes (a: uint64)
: byte * byte * byte * byte * byte * byte * byte * byte
:= let (f, i) := a in
    (byte_of_int (snd (shr_uint63 a 56)),
     byte_of_int (i >> 48),
     byte_of_int (i >> 40),
     byte_of_int (i >> 32),
     byte_of_int (i >> 24),
     byte_of_int (i >> 16),
     byte_of_int (i >> 8),
     byte_of_int i)%uint63.

Definition uint64_to_le_bytes (a: uint64)
: byte * byte * byte * byte * byte * byte * byte * byte
:= let (f, i) := a in
    (byte_of_int i,
     byte_of_int (i >> 8),
     byte_of_int (i >> 16),
     byte_of_int (i >> 24),
     byte_of_int (i >> 32),
     byte_of_int (i >> 40),
     byte_of_int (i >> 48),
     byte_of_int (snd (shr_uint63 a 56)))%uint63.
