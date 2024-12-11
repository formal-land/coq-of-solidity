(** This is an implementation of finite integers using Z with constraints.
  Warning: proof terms may blow up during computation.
 *)

From Coq Require Import NArith ZArith.
From Coq Require Import Bool Eqdep_dec.
From Coq Require Import Lia.

From CoqOfSolidity Require Import Logic2 Arith2.

Local Open Scope Z_scope.

Definition bound_int (lower upper: Z) := { a: Z | ((lower <=? a) && (a <? upper)) = true}.

Definition Z_of_bound_int {lower upper: Z} (n: bound_int lower upper): Z := proj1_sig n.

Lemma bound_int_irrel {lower upper: Z} {n m: bound_int lower upper}
                      (E: Z_of_bound_int n = Z_of_bound_int m):
  n = m.
Proof.
destruct n as (n, okN). destruct m as (m, okM).
cbn in E. subst m. f_equal.
apply eq_proofs_unicity. decide equality.
Qed.

Lemma bound_int_lower {lower upper: Z} (b: bound_int lower upper):
  lower <= Z_of_bound_int b.
Proof.
unfold Z_of_bound_int.
rewrite<- Z.leb_le.
exact (proj1 (andb_prop _ _ (proj2_sig b))).
Qed.

Lemma bound_int_upper {lower upper: Z} (b: bound_int lower upper):
  Z_of_bound_int b < upper.
Proof.
unfold Z_of_bound_int.
rewrite<- Z.ltb_lt.
exact (proj2 (andb_prop _ _ (proj2_sig b))).
Qed.

Definition bound_int_both {lower upper: Z} (b: bound_int lower upper):
  lower <= Z_of_bound_int b < upper
:= conj (bound_int_lower b) (bound_int_upper b).

Definition bound_int_of_Z {lower upper: Z} (n: Z) (LB: lower <= n) (UB: n < upper)
: bound_int lower upper
:= exist _ n (andb_true_intro (conj (proj2 (Z.leb_le _ _) LB)
                                    (proj2 (Z.ltb_lt _ _) UB))).

Definition bound_int_of_Z_conj {lower upper: Z} (n: Z) (B: lower <= n < upper)
: bound_int lower upper
:= bound_int_of_Z n (proj1 B) (proj2 B).

Definition bound_int_of_N_bound_by_Z {upper: Z} (n: N) (UB: (Z.of_N n < upper)%Z)
: bound_int 0%Z upper
:= bound_int_of_Z (Z.of_N n) (N2Z.is_nonneg n) UB.

Definition bound_int_of_N_bound_by_N {upper: N} (n: N) (UB: (n < upper)%N)
: bound_int 0%Z (Z.of_N upper)
:= bound_int_of_Z (Z.of_N n) (N2Z.is_nonneg n) (proj1 (N2Z.inj_lt _ _) UB).

(****************************************************************************)

Definition bound_N upper := { a: N | (a <? upper)%N = true}.
Definition uint' (width: N) := bound_N (2 ^ width).
Definition N_of_uint' {width: N} (n: uint' width) := proj1_sig n.
Definition Z_of_uint' {width: N} (n: uint' width) := Z.of_N (N_of_uint' n).

Lemma uint'_bound {width: N} (n: uint' width):
  (N_of_uint' n < 2 ^ width)%N.
Proof.
assert (B := proj2_sig n).
unfold N_of_uint'.
apply N.ltb_lt.
apply B.
Qed.

Lemma N_of_Z_of_uint' {width: N} (n: uint' width):
  Z.to_N (Z_of_uint' n) = N_of_uint' n.
Proof.
unfold Z_of_uint'.
now rewrite N2Z.id.
Qed.

Definition uint (width: N) := bound_int 0 (2 ^ (Z.of_N width)).
Definition Z_of_uint {width: N} (n: uint width): Z := Z_of_bound_int n.
Definition N_of_uint {width: N} (n: uint width): N := Z.to_N (Z_of_uint n).

Lemma Z_of_N_of_uint {width: N} (n: uint width):
  Z.of_N (N_of_uint n) = Z_of_uint n.
Proof.
unfold N_of_uint.
rewrite Z2N.id. { trivial. }
apply (bound_int_lower n).
Qed.

(* This is an N bound. For a Z bound, use bound_int_upper. *)
Lemma uint_bound {width: N} (n: uint width):
  (N_of_uint n < 2 ^ width)%N.
Proof.
assert (B := bound_int_upper n).
apply N2Z.inj_lt.
rewrite Z_of_N_of_uint.
now rewrite N2Z.inj_pow.
Qed.

Lemma uint_mod_bound_N (width: N) (n: N):
  (n mod 2^width < 2^width)%N.
Proof.
apply N.mod_upper_bound.
apply N.pow_nonzero.
discriminate.
Qed.

Lemma uint_mod_bound_Z (width: N) (n: N):
  (Z.of_N (n mod 2^width) < 2 ^ Z.of_N width)%Z.
Proof.
replace 2%Z with (Z.of_N 2%N). 2:{ trivial. }
rewrite<- N2Z.inj_pow.
apply N2Z.inj_lt.
apply uint_mod_bound_N.
Qed.

Lemma uint_land_ones_bound_Z (width: N) (n: N):
  (Z.of_N (N.land n (N.ones width)) < 2 ^ Z.of_N width)%Z.
Proof.
rewrite N.land_ones.
apply uint_mod_bound_Z.
Qed.

Local Lemma uint_of_N_pow_spec {width: N} {n: N} (B: (n < 2 ^ width)%N):
  Z.of_N n < 2 ^ Z.of_N width.
Proof.
replace 2%Z with (Z.of_N 2%N). 2:{ trivial. }
rewrite<- N2Z.inj_pow.
apply N2Z.inj_lt.
exact B.
Qed.

Definition uint_of_N {width: N} (n: N) (B: (n < 2 ^ width)%N)
: uint width
:= bound_int_of_N_bound_by_Z n (uint_of_N_pow_spec B). 

Definition uint_of_N_mod {width: N} (n: N)
: uint width
:= bound_int_of_N_bound_by_Z (N.land n (N.ones width)) (uint_land_ones_bound_Z width n).

Definition uint_0 (width: N)
: uint width
:= uint_of_N 0%N (N_0_lt_pow2 width).

Lemma uint_1_bound (width: positive):
  (1 < 2 ^ N.pos width)%N.
Proof.
replace 1%N with (2 ^ 0)%N by trivial.
apply N.pow_lt_mono_r; lia.
Qed.

Definition uint_1 (width: positive)
: uint (N.pos width)
:= uint_of_N 1%N (uint_1_bound width).

Lemma uint_highest_bound (width: N):
  (N.ones width < 2 ^ width)%N.
Proof.
rewrite N.ones_equiv.
assert (V := N_0_lt_pow2 width).
lia.
Qed.

Definition uint_highest (width: N)
: uint width
:= uint_of_N (N.ones width) (uint_highest_bound width).

Local Lemma uint_of_Z_mod_bound (width: N) (n: Z):
  0 <= n mod 2 ^ Z.of_N width < 2 ^ Z.of_N width.
Proof.
replace 2%Z with (Z.of_N 2%N). 2:{ trivial. }
rewrite<- N2Z.inj_pow.
apply (Z.mod_pos_bound _ _ (proj1 (N2Z.inj_lt _ _) (N_0_lt_pow2 width))).
Qed.

Local Lemma uint_of_Z_land_ones_bound (width: N) (n: Z):
  0 <= Z.land n (Z.ones (Z.of_N width)) < 2 ^ Z.of_N width.
Proof.
rewrite Z.land_ones.
apply uint_of_Z_mod_bound.
apply N2Z.is_nonneg.
Qed.

Definition uint_of_Z_mod (width: N) (n: Z)
: uint width
:= bound_int_of_Z_conj (Z.land n (Z.ones (Z.of_N width)))
                       (uint_of_Z_land_ones_bound width n).

Lemma Z_of_uint_of_Z_mod (width: N) (n: Z):
  Z_of_uint (uint_of_Z_mod width n) = n mod 2 ^ Z.of_N width.
Proof.
cbn. rewrite Z.land_ones. { trivial. } apply N2Z.is_nonneg.
Qed.

(*********************************************************************************)

Lemma N_land_bound {width: N} {n m: N} 
                   (BN: (n < 2 ^ width)%N)
                   (BM: (m < 2 ^ width)%N):
  (N.land n m < 2 ^ width)%N.
Proof.
assert (CN := N.eq_0_gt_0_cases n).
assert (CM := N.eq_0_gt_0_cases m).
assert (CA := N.eq_0_gt_0_cases (N.land n m)).
case CN; intro ZN. { now subst. }
case CM; intro ZM. { subst. now rewrite N.land_comm. }
case CA; intro ZA. { rewrite ZA. apply N_0_lt_pow2. }
rewrite N.log2_lt_pow2 in *; try assumption.
apply (N.le_lt_trans _ _ _ (N.log2_land _ _)).
apply N.min_lt_iff.
right. assumption.
Qed.

Definition uint_and {width: N} (a b: uint width)
: uint width
:= uint_of_N (N.land (N_of_uint a) (N_of_uint b)) 
             (N_land_bound (uint_bound a) (uint_bound b)).

Lemma N_lor_bound {width: N} {n m: N} 
                  (BN: (n < 2 ^ width)%N)
                  (BM: (m < 2 ^ width)%N):
  (N.lor n m < 2 ^ width)%N.
Proof.
assert (CN := N.eq_0_gt_0_cases n).
assert (CM := N.eq_0_gt_0_cases m).
assert (CA := N.eq_0_gt_0_cases (N.lor n m)).
case CN; intro ZN. { now subst. }
case CM; intro ZM. { subst. now rewrite N.lor_comm. }
case CA; intro ZA. { rewrite ZA. apply N_0_lt_pow2. }
rewrite N.log2_lt_pow2 in *; try assumption.
rewrite N.log2_lor.
apply N.max_lub_lt; assumption.
Qed.

Definition uint_or {width: N} (a b: uint width)
: uint width
:= uint_of_N (N.lor (N_of_uint a) (N_of_uint b)) 
             (N_lor_bound (uint_bound a) (uint_bound b)).

Lemma N_lxor_bound {width: N} {n m: N} 
                   (BN: (n < 2 ^ width)%N)
                   (BM: (m < 2 ^ width)%N):
  (N.lxor n m < 2 ^ width)%N.
Proof.
assert (CN := N.eq_0_gt_0_cases n).
assert (CM := N.eq_0_gt_0_cases m).
assert (CA := N.eq_0_gt_0_cases (N.lxor n m)).
case CN; intro ZN. { now subst. }
case CM; intro ZM. { subst. now rewrite N.lxor_comm. }
case CA; intro ZA. { rewrite ZA. apply N_0_lt_pow2. }
rewrite N.log2_lt_pow2 in *; try assumption.
apply (N.le_lt_trans _ _ _ (N.log2_lxor _ _)).
apply N.max_lub_lt; assumption.
Qed.

Definition uint_xor {width: N} (a b: uint width)
: uint width
:= uint_of_N (N.lxor (N_of_uint a) (N_of_uint b)) 
             (N_lxor_bound (uint_bound a) (uint_bound b)).

Lemma N_lnot_bound {width: N} {n: N}
                   (BN: (n < 2 ^ width)%N):
  (N.lnot n width < 2 ^ width)%N.
Proof.
unfold N.lnot. apply N_lxor_bound. { assumption. }
rewrite N.ones_equiv.
apply N.lt_pred_l.
apply N.pow_nonzero.
discriminate.
Qed.

Definition uint_not {width: N} (a: uint width)
: uint width
:= uint_of_N (N.lnot (N_of_uint a) width)
             (N_lnot_bound (uint_bound a)).

Example uint_not_example: 
  N_of_uint (uint_not (uint_0 8)) = 255%N.
Proof. trivial. Qed.

Lemma N_shiftr_bound {width: N} {n: N}
                     (BN: (n < 2 ^ width)%N)
                     (shift: N):
  (N.shiftr n shift < 2 ^ width)%N.
Proof.
rewrite N.shiftr_div_pow2.
assert (CN := N.eq_0_gt_0_cases n).
assert (CS := N.eq_0_gt_0_cases shift).
case CN; intro. { subst. cbn. apply N_0_lt_pow2. }
case CS; intro. { subst. cbn. now rewrite N.div_1_r. }
enough (n / 2 ^ shift < n)%N. { now refine (N.lt_trans _ _ _ _ BN). }
apply N.div_lt. { assumption. }
apply N.pow_gt_1. { now rewrite<- N.ltb_lt. }
now apply N_ne_0_gt_0.
Qed.

Definition uint_shr_N {width: N} (a: uint width) (shift: N)
: uint width
:= uint_of_N (N.shiftr (N_of_uint a) shift)
             (N_shiftr_bound (uint_bound a) shift).

(*********************************************************************************)

Lemma N_div_bound {width: N} {n: N}
                  (BN: (n < 2 ^ width)%N)
                  (d: N):
  (n / d < 2 ^ width)%N.
Proof.
apply (N.le_lt_trans _ _ _ (N_div_le n d) BN).
Qed.

Definition uint_div_N {width: N} (a: uint width) (d: N)
: uint width
:= uint_of_N ((N_of_uint a) / d)%N
             (N_div_bound (uint_bound a) d).

(*********************************************************************************)

Definition uint_add {width: N} (a b: uint width)
: uint width
:= uint_of_Z_mod width (Z_of_uint a + Z_of_uint b)%Z.

Definition uint_sub {width: N} (a b: uint width)
: uint width
:= uint_of_Z_mod width (Z_of_uint a - Z_of_uint b)%Z. (* may not be via N since N.sub truncates *) 

Definition uint_mul {width: N} (a b: uint width)
: uint width
:= uint_of_Z_mod width (Z_of_uint a * Z_of_uint b)%Z.

Definition uint_shl_N {width: N} (a: uint width) (shift: N)
: uint width
:= uint_of_N_mod (N.shiftl (N_of_uint a) shift).

(* This version is mathematically correct but too slow to compute;
   see uint_pow below.
 *)
Definition uint_pow_ideal {width: N} (a b: uint width)
: uint width
:= uint_of_Z_mod width (Z_of_uint a ^ Z_of_uint b)%Z.

(*********************************************************************************)

Lemma uint_0_pow_0_is_1 {width: positive}:
  uint_pow_ideal (uint_0 (Npos width)) (uint_0 (Npos width)) = uint_1 width.
Proof.
unfold uint_pow_ideal. apply bound_int_irrel. cbn.
assert(T: 1 < 2 ^ (Z.pos width)).
{
  replace 1 with (2 ^ 0)%Z by trivial.
  apply Z.pow_lt_mono_r; lia.
}
assert(P: 0 < Z.ones (Z.pos width)).
{ rewrite Z.ones_equiv. lia. } 
remember (Z.ones (Z.pos width)) as ones.
destruct ones; try lia.
assert (Odd: Z.odd (Z.pos p) = true).
{
  rewrite Heqones.
  rewrite Z.ones_equiv.
  rewrite Z.odd_pred.
  rewrite Z.even_pow.
  apply Z.even_2.
  trivial.
}
now destruct p.
Qed.

Fixpoint uint_pow_pos {width: N} (a: uint width) (b: positive)
: uint width
:= match b with
   | 1%positive => a
   | p~0%positive => let x := uint_pow_pos a p in uint_mul x x
   | p~1%positive => let x := uint_pow_pos a p in uint_mul a (uint_mul x x)
   end.

Lemma uint_pow_pos_ok {width: N} (a: uint width) (b: positive):
  uint_pow_pos a b = uint_of_Z_mod width (Z_of_uint a ^ Z.pos b)%Z.
Proof.
induction b.
{
  replace (Z.pos b~1) with (2 * Z.pos b + 1) by trivial.
  rewrite Z.pow_add_r; try lia.
  rewrite Z.pow_1_r.
  rewrite Z.pow_twice_r.
  cbn. unfold uint_mul.
  apply bound_int_irrel.
  cbn. repeat rewrite Z.land_ones; try apply N2Z.is_nonneg.
  rewrite IHb.
  repeat rewrite Z_of_uint_of_Z_mod.
  clear IHb. rewrite Z.pow_pos_fold.
  remember (Z_of_uint a) as n. remember (Z.pos b) as p. remember (2 ^ Z.of_N width) as m.
  rewrite<- Zmult_mod.
  rewrite<- Z.mul_assoc.
  rewrite<- Z.mul_comm.
  rewrite Zmult_mod_idemp_l.
  now rewrite<- Z.mul_assoc.
}
{
  replace (Z.pos b~0) with (2 * Z.pos b) by trivial.
  rewrite Z.pow_twice_r.
  cbn. unfold uint_mul.
  apply bound_int_irrel.
  cbn. repeat rewrite Z.land_ones; try apply N2Z.is_nonneg.
  rewrite IHb.
  repeat rewrite Z_of_uint_of_Z_mod.
  clear IHb. rewrite Z.pow_pos_fold.
  remember (Z_of_uint a) as n. remember (Z.pos b) as p. remember (2 ^ Z.of_N width) as m.
  now rewrite<- Zmult_mod.
}
cbn. apply bound_int_irrel.
cbn. rewrite Z.land_ones; try apply N2Z.is_nonneg.
rewrite Z.mul_1_r.
rewrite Z.mod_small. { trivial. }
exact (bound_int_both a).
Qed.

Definition uint_pow_N {width: positive} (a: uint (Npos width)) (b: N)
: uint (Npos width)
:= match b with
   | 0%N => uint_1 width
   | Npos p => uint_pow_pos a p
   end.

Lemma uint_pow_N_ok {width: positive} (a: uint (Npos width)) (b: N):
  uint_pow_N a b = uint_of_Z_mod (Npos width) (Z_of_uint a ^ Z.of_N b)%Z.
Proof.
destruct b. 2:{ apply uint_pow_pos_ok. }
cbn. apply bound_int_irrel.
replace Z_of_bound_int with (@Z_of_uint (N.pos width)) by trivial.
rewrite Z_of_uint_of_Z_mod.
cbn.
rewrite Z.pow_pos_fold.
symmetry. apply Z.mod_small.
split. { now rewrite<- Z.leb_le. }
replace 1 with (2 ^ 0) by trivial.
apply Z.pow_lt_mono_r; lia.
Qed.

Definition uint_pow {width: positive} (a b: uint (Npos width))
: uint (Npos width)
:= uint_pow_N a (N_of_uint b).

Lemma uint_pow_ok {width: positive} (a b: uint (Npos width)):
  uint_pow a b = uint_pow_ideal a b.
Proof.
unfold uint_pow. rewrite uint_pow_N_ok.
unfold uint_pow_ideal.
now rewrite Z_of_N_of_uint.
Qed.
