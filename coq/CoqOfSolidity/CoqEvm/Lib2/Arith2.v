From Coq Require Import NArith ZArith Lia.

From CoqOfSolidity Require Import Logic2.

(**************************************************************************)

Lemma N_ltb_lt_quad (a b c d: N):
  ((a <? b)%N = (c <? d)%N) <-> ((a < b)%N <-> (c < d)%N).
Proof.
apply relation_quad; apply N.ltb_lt.
Qed.

Lemma Z_ltb_lt_quad (a b c d: Z):
  ((a <? b)%Z = (c <? d)%Z) <-> ((a < b)%Z <-> (c < d)%Z).
Proof.
apply relation_quad; apply Z.ltb_lt.
Qed.

Lemma N_leb_le_quad (a b c d: N):
  ((a <=? b)%N = (c <=? d)%N) <-> ((a <= b)%N <-> (c <= d)%N).
Proof.
apply relation_quad; apply N.leb_le.
Qed.

Lemma Z_leb_le_quad (a b c d: Z):
  ((a <=? b)%Z = (c <=? d)%Z) <-> ((a <= b)%Z <-> (c <= d)%Z).
Proof.
apply relation_quad; apply Z.leb_le.
Qed.

Lemma N2Z_ltb (n m: N):
  (n <? m)%N = (Z.of_N n <? Z.of_N m)%Z.
Proof.
apply (relation_quad N.ltb_lt Z.ltb_lt).
apply N2Z.inj_lt.
Qed.

Lemma N2Z_leb (n m: N):
  (n <=? m)%N = (Z.of_N n <=? Z.of_N m)%Z.
Proof.
apply (relation_quad N.leb_le Z.leb_le).
apply N2Z.inj_le.
Qed.

(**************************************************************************)

Lemma Z_shiftr_pow2 (n: Z) (B: (0 <= n)%Z):
  Z.shiftr (2 ^ n) n = 1%Z.
Proof.
rewrite (Z.shiftr_div_pow2 _ _ B).
apply Z.div_same.
now apply Z.pow_nonzero.
Qed.

Lemma Z_ltb_irrefl (n: Z):
  (n <? n)%Z = false.
Proof.
remember (n <? n)%Z as L.
destruct L; trivial.
symmetry in HeqL.
rewrite Z.ltb_lt in HeqL.
apply Z.lt_irrefl in HeqL.
contradiction.
Qed.

Lemma N_ltb_irrefl (n: N):
  (n <? n)%N = false.
Proof.
remember (n <? n)%N as L.
destruct L; trivial.
symmetry in HeqL.
rewrite N.ltb_lt in HeqL.
apply N.lt_irrefl in HeqL.
contradiction.
Qed.

(**************************************************************************)

Lemma Z_land_pow2_shift (n m: Z) (BM: (0 <= m)%Z):
  Z.land n (2 ^ m) = Z.shiftl (Z.land (Z.shiftr n m) 1) m.
Proof.
rewrite<- (Z_shiftr_pow2 m BM).
rewrite<- Z.shiftr_land.
rewrite<- (Z.ldiff_ones_r _ _ BM).
rewrite Z.ldiff_land.
rewrite<- Z.land_assoc.
f_equal.
apply Z.bits_inj'. intros k Bk.
rewrite Z.land_spec.
rewrite (Z.lnot_spec _ _ Bk).
rewrite (Z.testbit_ones _ _ BM).
rewrite (Z.pow2_bits_eqb _ _ BM).
rewrite<- Z.leb_le in Bk.
rewrite Bk.
rewrite Bool.andb_true_l.
remember (m =? k)%Z as MK. symmetry in HeqMK.
destruct MK. 
{
  rewrite Z.eqb_eq in HeqMK. subst.
  now rewrite Z_ltb_irrefl.
}
trivial.
Qed.

Lemma Z_mul_pos_iff_l (n m: Z) (BM: (0 < m)%Z):
  (0 < n)%Z <-> (0 < n * m)%Z.
Proof.
split. { intro. apply Z.mul_pos_pos; assumption. }
apply (Z.mul_pos_cancel_r _ _ BM).
Qed.

Lemma Z_mul_pos_iff_r (n m: Z) (BN: (0 < n)%Z):
  (0 < m)%Z <-> (0 < n * m)%Z.
Proof.
split. { apply (Z.mul_pos_pos _ _ BN). }
apply (Z.mul_pos_cancel_l _ _ BN).
Qed.

Lemma Z_shiftl_pos_iff (n m: Z) (BM: (0 <= m)%Z):
 (0 < n)%Z <-> (0 < Z.shiftl n m)%Z.
Proof.
rewrite (Z.shiftl_mul_pow2 _ _ BM).
apply Z_mul_pos_iff_l.
apply Z.pow_pos_nonneg.
{ rewrite<- Z.ltb_lt. trivial. }
assumption.
Qed.

Lemma Z_odd_land_1 (n: Z) (B: (0 <= n)%Z):
  Z.odd n = (0 <? Z.land n 1)%Z.
Proof.
destruct n; now try destruct p.
Qed.

Lemma Z_testbit_alt (n m: Z) (BN: (0 <= n)%Z) (BM: (0 <= m)%Z):
  Z.testbit n m = (0 <? Z.land n (2 ^ m))%Z.
Proof.
rewrite (Z_land_pow2_shift _ _ BM).
assert (Q: forall x, ((0 <? Z.shiftl x m) = (0 <? x))%Z).
{
  intro x.
  rewrite Z_ltb_lt_quad.
  symmetry.
  apply Z_shiftl_pos_iff.
  assumption.
}
rewrite Q. clear Q.
rewrite Z.testbit_odd.
apply Z_odd_land_1.
apply Z.shiftr_nonneg.
assumption.
Qed.

Lemma Z_testbit_high (a n: Z)
                      (B: (0 <= n)%Z)
                      (A: (0 <= a < 2 ^ n)%Z):
  Z.testbit a n = false.
Proof.
rewrite<- (Z.mod_small a (2 ^ n)%Z A).
apply Z.mod_pow2_bits_high.
split. { assumption. }
apply Z.le_refl.
Qed.

(**************************************************************************)

Lemma Z_to_N_land (x y: Z) (BX: (0 <= x)%Z) (BY: (0 <= y)%Z):
  Z.to_N (Z.land x y) = N.land (Z.to_N x) (Z.to_N y).
Proof.
apply N.bits_inj. intro n.
rewrite N.land_spec.
remember (Z.of_N n) as m.
assert (NM: n = Z.to_N m).
{ subst m. symmetry. apply N2Z.id. }
repeat rewrite NM.
assert (BM: (0 <= m)%Z).
{ subst. apply N2Z.is_nonneg. }
repeat rewrite<- Z2N.inj_testbit; try assumption.
repeat rewrite Z2N.id; try assumption.
{ apply Z.land_spec. }
rewrite Z.land_nonneg. tauto.
Qed.


Lemma N_to_Z_land (x y: N):
  Z.of_N (N.land x y) = Z.land (Z.of_N x) (Z.of_N y).
Proof.
rewrite<- (Z2N.id (Z.land (Z.of_N x) (Z.of_N y))).
{
  f_equal.
  rewrite Z_to_N_land; try apply N2Z.is_nonneg.
  repeat rewrite N2Z.id.
  trivial.
}
apply Z.land_nonneg. left. apply N2Z.is_nonneg.
Qed.

Lemma Z_to_N_lor (x y: Z) (BX: (0 <= x)%Z) (BY: (0 <= y)%Z):
  Z.to_N (Z.lor x y) = N.lor (Z.to_N x) (Z.to_N y).
Proof.
apply N.bits_inj. intro n.
rewrite N.lor_spec.
remember (Z.of_N n) as m.
assert (NM: n = Z.to_N m).
{ subst m. symmetry. apply N2Z.id. }
repeat rewrite NM.
assert (BM: (0 <= m)%Z).
{ subst. apply N2Z.is_nonneg. }
repeat rewrite<- Z2N.inj_testbit; try assumption.
repeat rewrite Z2N.id; try assumption.
{ apply Z.lor_spec. }
rewrite Z.lor_nonneg. tauto.
Qed.

Lemma N_to_Z_lor (x y: N):
  Z.of_N (N.lor x y) = Z.lor (Z.of_N x) (Z.of_N y).
Proof.
rewrite<- (Z2N.id (Z.lor (Z.of_N x) (Z.of_N y))).
{
  f_equal.
  rewrite Z_to_N_lor; try apply N2Z.is_nonneg.
  repeat rewrite N2Z.id.
  trivial.
}
apply Z.lor_nonneg. split; apply N2Z.is_nonneg.
Qed.

Lemma Z_to_N_lxor (x y: Z) (BX: (0 <= x)%Z) (BY: (0 <= y)%Z):
  Z.to_N (Z.lxor x y) = N.lxor (Z.to_N x) (Z.to_N y).
Proof.
apply N.bits_inj. intro n.
rewrite N.lxor_spec.
remember (Z.of_N n) as m.
assert (NM: n = Z.to_N m).
{ subst m. symmetry. apply N2Z.id. }
repeat rewrite NM.
assert (BM: (0 <= m)%Z).
{ subst. apply N2Z.is_nonneg. }
repeat rewrite<- Z2N.inj_testbit; try assumption.
repeat rewrite Z2N.id; try assumption.
{ apply Z.lxor_spec. }
rewrite Z.lxor_nonneg. tauto.
Qed.

Lemma N_to_Z_lxor (x y: N):
  Z.of_N (N.lxor x y) = Z.lxor (Z.of_N x) (Z.of_N y).
Proof.
rewrite<- (Z2N.id (Z.lxor (Z.of_N x) (Z.of_N y))).
{
  f_equal.
  rewrite Z_to_N_lxor; try apply N2Z.is_nonneg.
  repeat rewrite N2Z.id.
  trivial.
}
apply Z.lxor_nonneg. split; intro; apply N2Z.is_nonneg.
Qed.

(**************************************************************************)

Lemma N_testbit_alt (n m: N):
  N.testbit n m = (0 <? N.land n (2 ^ m))%N.
Proof.
rewrite<- Z.testbit_of_N.
replace (0 <? N.land n (2 ^ m))%N with (0 <? Z.land (Z.of_N n) (2 ^ (Z.of_N m)))%Z.
2:{
  rewrite N2Z_ltb.
  rewrite N_to_Z_land.
  cbn.
  repeat f_equal.
  rewrite N2Z.inj_pow.
  trivial.
}
apply Z_testbit_alt; apply N2Z.is_nonneg.
Qed.

(**************************************************************************)

Definition N_0_lt_pow2 (n: N):
  (0 < 2 ^ n)%N.
Proof.
case (N.eq_0_gt_0_cases (2 ^ n)); intro; try assumption.
apply N.pow_nonzero in H. { contradiction. }
discriminate.
Qed.

Definition Z_0_lt_pow2 (n: Z) (B: (0 <= n)%Z):
  (0 < 2 ^ n)%Z.
Proof.
assert (A := N_0_lt_pow2 (Z.to_N n)).
apply N2Z.inj_lt in A.
rewrite N2Z.inj_pow in A.
cbn in A.
now rewrite Z2N.id in A.
Qed.

Lemma N_ne_0_gt_0 (n: N):
  n <> 0%N <-> (0 < n)%N.
Proof.
split; intro H.
{ assert (CN := N.eq_0_gt_0_cases n). tauto. }
destruct n. { now apply N.lt_irrefl in H. }
discriminate.
Qed.

Lemma N_div_0_r (n: N):
  (n / 0 = 0)%N.
Proof.
now destruct n.
Qed.

Lemma Z_div_0_r (n: Z):
  (n / 0 = 0)%Z.
Proof.
now destruct n.
Qed.

Lemma N_div_le (n: N) (d: N):
  (n / d <= n)%N.
Proof.
assert (CN := N.eq_0_gt_0_cases n).
assert (CD := N.eq_0_gt_0_cases d).
case CN; intro. { subst. cbn. apply N.le_refl. }
case CD; intro. { subst. rewrite N_div_0_r. now apply N.lt_le_incl. }
assert (D: N.succ (N.pred d) = d).
{ apply N.succ_pred_pos. assumption. }
remember (N.pred d) as k. clear Heqk. subst.
assert (CK := N.eq_0_gt_0_cases k).
case CK; intro. { subst. cbn. now rewrite N.div_1_r. }
apply N.lt_le_incl.
apply N.div_lt. { assumption. }
now apply N.lt_pred_lt_succ.
Qed.

Lemma Z_div_nonneg (a b: Z)
                    (A: (0 <= a)%Z)
                    (B: (0 <= b)%Z):
  (0 <= a / b)%Z.
Proof.
destruct b. { rewrite Zdiv_0_r. apply Z.le_refl. }
{ apply Z.div_pos; easy. }
easy.
Qed.

Lemma Z_abs_div_le (a b: Z):
  (Z.abs a / Z.abs b <= Z.abs a)%Z.
Proof.
assert(A := Z.abs_nonneg a).
assert(B := Z.abs_nonneg b).
apply Z2N.inj_le. { now apply Z_div_nonneg. }
{ assumption. }
rewrite Z2N.inj_div; try assumption.
apply N_div_le.
Qed.

Lemma Z_abs_sgn (a b: Z):
  Z.abs (Z.sgn a * b)%Z = match a with
                          | 0%Z => 0%Z
                          | _ => Z.abs b
                          end.
Proof.
now destruct a, b.
Qed.

Lemma Z_sgn_abs (a: Z):
  (Z.sgn a * Z.abs a)%Z = a.
Proof.
now destruct a.
Qed.

Lemma Z_add_nocarry_lor (a b: Z) (H: Z.land a b = 0%Z):
  (a + b = Z.lor a b)%Z.
Proof.
rewrite Z.add_nocarry_lxor by assumption.
apply Z.lxor_lor. assumption.
Qed.

Lemma Z_land_pow2_small (a b: Z) (A: (0 <= a < 2 ^ b)%Z) (B: (0 <= b)%Z):
  Z.land a (2 ^ b) = 0%Z.
Proof.
rewrite Arith2.Z_land_pow2_shift by tauto.
replace (Z.shiftr a b) with 0%Z. { cbn. apply Z.shiftl_0_l. }
rewrite Z.shiftr_div_pow2 by tauto.
symmetry. apply Z.div_small. exact A.
Qed.

Lemma Z_testbit_flag_mul_pow2 (f: bool) (k: Z) (K: (0 <= k)%Z):
  Z.testbit ((if f then 1 else 0) * 2 ^ k) k = f.
Proof.
destruct f.
{ rewrite Z.mul_1_l. apply Z.pow2_bits_true. assumption. }
rewrite Z.mul_0_l. apply Z.bits_0.
Qed.

(* A version of Z.bits_above_log2 with a different bound. *)
Lemma Z_testbit_small (a n: Z) (A: (0 <= a)%Z)
                               (B: (a < 2 ^ n)%Z):
  Z.testbit a n = false.
Proof.
destruct a. { apply Z.testbit_0_l. }
{ apply Z.bits_above_log2. trivial. now apply Z.log2_lt_pow2. }
exfalso. rewrite<- Z.leb_le in A. cbn in A. discriminate.
Qed.

(**************************************************************************)

Lemma Z_pos_ne_0 (a: positive):
  Z.pos a <> 0%Z.
Proof.
discriminate.
Qed.

Lemma Z_0_lt_pos (a: positive):
  (0 < Z.pos a)%Z.
Proof.
rewrite<- Z.ltb_lt.
trivial.
Qed.

Lemma Z_ceiling_via_floor (a b: Z) (B: (0 <= b)%Z):
  (- ((- a) / b) = (a + b - 1) / b)%Z.
Proof.
destruct b as [|b|b]. { now repeat rewrite Z_div_0_r. }
{
  assert (D := Z.div_mod (-a) (Z.pos b) (Z_pos_ne_0 b)).
  assert (E := Z.div_mod (a + Z.pos b - 1) (Z.pos b) (Z_pos_ne_0 b)).
  assert (P := Z.mod_pos_bound (-a) (Z.pos b) (Z_0_lt_pos b)).
  assert (Q := Z.mod_pos_bound (a + Z.pos b - 1) (Z.pos b) (Z_0_lt_pos b)).
  nia.
}
rewrite<- Z.leb_le in B. discriminate.
Qed.

(**************************************************************************)

Lemma Z_land_lxor_distr_l (a b c: Z):
  Z.land (Z.lxor a b) c = Z.lxor (Z.land a c) (Z.land b c).
Proof.
apply Z.bits_inj. intro.
repeat (rewrite Z.land_spec || rewrite Z.lxor_spec).
destruct (Z.testbit a n); destruct (Z.testbit b n); destruct (Z.testbit c n); easy.
Qed.

Lemma Z_land_lxor_distr_r (a b c: Z):
  Z.land a (Z.lxor b c) = Z.lxor (Z.land a b) (Z.land a c).
Proof.
apply Z.bits_inj. intro.
repeat (rewrite Z.land_spec || rewrite Z.lxor_spec).
destruct (Z.testbit a n); destruct (Z.testbit b n); destruct (Z.testbit c n); easy.
Qed.

(**************************************************************************)

(* This is a version of Z.log2_lt_pow2 but a can be 0 and b cannot. *)
Lemma Z_log2_lt_pow2 (a b: Z) (BA: (0 <= a)%Z) (BB: (0 < b)%Z):
    (a < 2 ^ b <-> Z.log2 a < b)%Z.
Proof.
destruct a.
{
  cbn. assert (P: (0 < 2 ^ b)%Z). apply Z_0_lt_pow2. { apply Z.lt_le_incl. assumption. }
  tauto.
}
{ apply Z.log2_lt_pow2. rewrite<- Z.ltb_lt. trivial. }
rewrite<- Z.leb_le in BA. discriminate.
Qed.

(**************************************************************************)

Lemma Z_mod_add_l (a b c m: Z)
                  (H: (b mod m = c mod m)%Z):
  ((a + b) mod m = (a + c) mod m)%Z.
Proof.
rewrite<- (Zplus_mod_idemp_r b a).
rewrite<- (Zplus_mod_idemp_r c a).
rewrite H.
trivial.
Qed.

Lemma Z_mod_add_r (a b c m: Z)
                  (H: (a mod m = b mod m)%Z):
  ((a + c) mod m = (b + c) mod m)%Z.
Proof.
rewrite<- (Zplus_mod_idemp_l a c).
rewrite<- (Zplus_mod_idemp_l b c).
rewrite H.
trivial.
Qed.

(**************************************************************************)

Lemma Nat2N_inj_div (a b: nat):
  N.of_nat (a / b) = (N.of_nat a / N.of_nat b)%N.
Proof.
destruct b. { cbn. now rewrite N_div_0_r. }
assert (BNZ: S b <> 0) by discriminate.
assert (D := Nat.div_mod a (S b) BNZ).
remember (a / S b) as q.
remember (a mod S b) as r.
apply N.div_unique with (r := N.of_nat r).
{
  unfold N.lt.
  rewrite<- Nat2N.inj_compare.
  apply Nat.compare_lt_iff.
  subst. apply (Nat.mod_upper_bound _ _ BNZ).
}
rewrite<- Nat2N.inj_mul.
rewrite<- Nat2N.inj_add.
now rewrite D.
Qed.

Lemma Nat2N_inj_mod (a b: nat) (ok: b <> 0):
  N.of_nat (a mod b) = (N.of_nat a mod N.of_nat b)%N.
Proof.
destruct b. { contradiction. }
rewrite Nat.Div0.mod_eq by discriminate.
rewrite Nat2N.inj_sub.
rewrite Nat2N.inj_mul.
rewrite Nat2N_inj_div.
symmetry. apply N.Div0.mod_eq.
Qed.

(**************************************************************************)
(** This is a strenghtening of Pos.size_nat_monotone from [p < q] to [p <= q]. *)
Lemma Pos_size_nat_monotone (p q: positive) (LE: (p <= q)%positive):
  (Pos.size_nat p <= Pos.size_nat q)%nat.
Proof.
remember (Pos.compare p q) as cmp. symmetry in Heqcmp. destruct cmp.
{ apply Pos.compare_eq in Heqcmp. subst. apply Nat.le_refl. }
{ apply Pos.size_nat_monotone. exact Heqcmp. }
contradiction.
Qed.