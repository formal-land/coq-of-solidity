(** 
  This file continues theories/Numbers/Cyclic/Int63/Int63.v from the standard library of Coq.
 *)

From Coq Require Import Uint63 NArith ZArith Lia.

From CoqOfSolidity Require Import Logic2 Arith2.

Definition uint63 := int.
Definition Z_of_uint63 := to_Z.
Definition uint63_of_Z := of_Z.

Ltac rewrite_Z_of_uint63 
:= repeat (rewrite lsl_spec
        || rewrite lsr_spec
        || rewrite land_spec'
        || rewrite lor_spec'
        || rewrite lxor_spec'
        || rewrite add_spec
        || rewrite sub_spec
        || rewrite mul_spec
        || rewrite div_spec
        || rewrite mod_spec
        || rewrite ltb_spec
        || rewrite leb_spec).

Definition N_of_uint63 (i: uint63): N
:= Z.to_N (to_Z i).
Definition uint63_of_N (n: N): uint63
:= of_Z (Z.of_N n).

Definition nat_of_uint63 (i: uint63): nat
:= N.to_nat (N_of_uint63 i).

Definition uint63_of_nat (n: nat): uint63
:= uint63_of_N (N.of_nat n).


Lemma Z_of_uint63_nonneg (i: uint63):
  (0 <= to_Z i)%Z.
Proof.
assert(B := to_Z_bounded i).
tauto.
Qed.

Lemma uint63_ltb_Z (x y: uint63):
  (x <? y)%uint63 = (to_Z x <? to_Z y)%Z.
Proof.
apply (relation_quad (fun x y => iff_refl _) Z.ltb_lt).
apply ltb_spec.
Qed.

Lemma uint63_leb_Z (x y: uint63):
  (x <=? y)%uint63 = (to_Z x <=? to_Z y)%Z.
Proof.
apply (relation_quad (fun x y => iff_refl _) Z.leb_le).
apply leb_spec.
Qed.

Lemma uint63_ltb_N (x y: uint63):
  (x <? y)%uint63 = (N_of_uint63 x <? N_of_uint63 y)%N.
Proof.
rewrite uint63_ltb_Z.
unfold N_of_uint63.
assert (Bx := to_Z_bounded x).
assert (By := to_Z_bounded y).
destruct Bx as (Bx, _).
destruct By as (By, _).
assert (L := Z2N.inj_lt (to_Z x) (to_Z y) Bx By).
clear Bx By.
apply (relation_quad Z.ltb_lt N.ltb_lt).
apply L.
Qed.

Lemma uint63_leb_N (x y: uint63):
  (x <=? y)%uint63 = (N_of_uint63 x <=? N_of_uint63 y)%N.
Proof.
rewrite uint63_leb_Z.
unfold N_of_uint63.
assert (Bx := to_Z_bounded x).
assert (By := to_Z_bounded y).
destruct Bx as (Bx, _).
destruct By as (By, _).
assert (L := Z2N.inj_le (to_Z x) (to_Z y) Bx By).
clear Bx By.
apply (relation_quad Z.leb_le N.leb_le).
apply L.
Qed.

Lemma uint63_get_high_digit (i k: uint63)
                            (B: (63 <=? k)%uint63 = true):
  get_digit i k = false.
Proof.
unfold get_digit.
enough (U: (1 << k = 0)%uint63).
{ 
  rewrite U.
  rewrite uint63_ltb_Z.
  rewrite land_spec'.
  rewrite to_Z_0.
  rewrite Z.land_0_r.
  trivial.
}
match goal with
|- ?lhs = ?rhs => rewrite<- (of_to_Z lhs); rewrite<- (of_to_Z rhs)
end.
f_equal.
rewrite lsl_spec.
rewrite to_Z_1. rewrite to_Z_0.
rewrite Z.mul_1_l.
rewrite uint63_leb_Z in B.
replace (to_Z 63%uint63) with 63%Z in B. 2:{ trivial. }
remember (to_Z k) as n. clear i k Heqn.
remember (n - 63)%Z as m.
assert (Q: n = (m + 63)%Z). { subst. lia. }
subst n.
rewrite Z.pow_add_r; rewrite Z.leb_le in B; [ | lia | lia ].
apply Z_mod_mult.
Qed.

Lemma uint63_testbit_Z (i k: uint63):
  get_digit i k = Z.testbit (to_Z i) (to_Z k).
Proof.
remember (k <? 63)%uint63 as Low. symmetry in HeqLow.
destruct Low.
{ 
  unfold get_digit.
  rewrite uint63_ltb_Z.
  rewrite land_spec'.
  rewrite lsl_spec.
  remember (to_Z i) as n.
  remember (to_Z k) as m.
  replace (to_Z 0%uint63) with 0%Z. 2:{ trivial. }
  replace (to_Z 1%uint63) with 1%Z. 2:{ trivial. }
  rewrite Z.mul_1_l.
  rewrite Z.mod_small.
  2:{
    split. { apply Z.pow_nonneg. rewrite<- Z.leb_le. trivial. }
    unfold wB.
    apply Z.pow_lt_mono_r.
    { rewrite<- Z.ltb_lt. trivial. }
    { rewrite<- Z.leb_le. trivial. }
    subst.
    rewrite ltb_spec in HeqLow.
    assumption.
}
symmetry.
apply Z_testbit_alt.
assert (BN := to_Z_bounded i).
subst. tauto.
assert (BM := to_Z_bounded k).
subst. tauto.
}
assert(Bk: (63 <= to_Z k)%Z).
{
  rewrite uint63_ltb_Z in HeqLow.
  replace (to_Z 63%uint63) with 63%Z in HeqLow. 2:{ trivial. }
  rewrite Z.ltb_ge in HeqLow.
  assumption.
}
rewrite uint63_get_high_digit.
{
  symmetry.
  assert(Bi := to_Z_bounded i).
  apply Z_testbit_high.
  { assert(BK := to_Z_bounded k). tauto. }
  split. { tauto. }
  apply (Z.lt_le_trans _ wB _). { tauto. }
  apply Z.pow_le_mono_r. { rewrite<- Z.ltb_lt. trivial. }
  apply Bk.
}
rewrite leb_spec.
apply Bk.
Qed.

Lemma uint63_testbit_N_low_digit (n k: N)
                                  (B: (k < 63)%N):
  N.testbit n k = get_digit (uint63_of_N n) (uint63_of_N k).
Proof.
rewrite<- N2Z.inj_testbit.
rewrite uint63_testbit_Z.
unfold uint63_of_N.
repeat rewrite of_Z_spec.
rewrite (Z.mod_small (Z.of_N k)). 2:{ unfold wB. cbn. lia. }
symmetry.
apply Z.mod_pow2_bits_low.
unfold size.
lia.
Qed.

Lemma uint63_bit_get_digit (i k: uint63):
  bit i k = get_digit i k.
Proof.
rewrite bitE. rewrite uint63_testbit_Z. trivial.
Qed.

(**************************************************************************)

Lemma uint63_land_N (x y: uint63):
  N_of_uint63 (x land y)%uint63 = N.land (N_of_uint63 x) (N_of_uint63 y).
Proof.
unfold N_of_uint63.
rewrite land_spec'.
apply Z_to_N_land; apply Z_of_uint63_nonneg.
Qed.

Lemma uint63_lor_N (x y: uint63):
  N_of_uint63 (x lor y)%uint63 = N.lor (N_of_uint63 x) (N_of_uint63 y).
Proof.
unfold N_of_uint63.
rewrite lor_spec'.
apply Z_to_N_lor; apply Z_of_uint63_nonneg.
Qed.

Lemma uint63_lxor_N (x y: uint63):
  N_of_uint63 (x lxor y)%uint63 = N.lxor (N_of_uint63 x) (N_of_uint63 y).
Proof.
unfold N_of_uint63.
rewrite lxor_spec'.
apply Z_to_N_lxor; apply Z_of_uint63_nonneg.
Qed.

(**************************************************************************)
