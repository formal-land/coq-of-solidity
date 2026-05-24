(* Ethereum instructions that deal with signed ints: SDIV SMOD SIGNEXTEND SLT SGT SAR *)

From Coq Require Import NArith ZArith Lia.

Require Import UInt.
Require Import Arith2.

Local Open Scope Z_scope.

Definition sint (width: N) := bound_int (- 2 ^ (Z.of_N width - 1))
                                         (  2 ^ (Z.of_N width - 1)).

Definition Z_of_sint {width: N} (z: sint width): Z := Z_of_bound_int z.

Local Lemma uint_of_sint_pos_spec {width : N}
                             (a: sint width)
                             (p: positive)
                             (E: Z_of_sint a = Z.pos p):
  (N.pos p < 2 ^ width)%N.
Proof.
assert (B := bound_int_upper a).
unfold Z_of_sint in E. rewrite E in B.
clear E a.
apply N2Z.inj_lt.
rewrite N2Z.inj_pow.
cbn.
apply (Z.lt_trans _ _ _ B).
apply Z.pow_lt_mono_r. { now rewrite<- Z.ltb_lt. }
{ apply N2Z.is_nonneg. }
apply Z.lt_pred_l.
Qed.

Local Lemma uint_of_sint_neg_spec {width : N}
                            (a: sint width)
                            (p: positive)
                            (E: Z_of_sint a = Z.neg p):
  (2 ^ width - N.pos p < 2 ^ width)%N.
Proof.
assert (B := bound_int_lower a). unfold Z_of_sint in E.
rewrite E in B. clear E a.
apply N.sub_lt. 2:{ now apply N_ne_0_gt_0. }
apply N2Z.inj_le.
rewrite N2Z.inj_pow.
cbn.
rewrite Z.opp_le_mono in B.
cbn in B. rewrite Z.opp_involutive in B.
apply (Z.le_trans _ _ _ B).
apply Z.pow_le_mono_r. { now rewrite<- Z.ltb_lt. }
apply Z.lt_le_incl.
apply Z.lt_pred_l.
Qed.

(** Convert an uint to a sint in a usual way:
    split the range of uints in half and 
    map the higher half into the negatives.
 *)

Definition uint_of_sint {width: N} (a: sint width)
: uint width
:= let z := Z_of_sint a in 
   match z as z' return z = z' -> _ with
   | Z0 => fun _ => uint_0 width
   | Zpos p => fun E => uint_of_N (Npos p) (uint_of_sint_pos_spec a p E)
   | Zneg p => fun E => uint_of_N (2^width - Npos p)%N (uint_of_sint_neg_spec a p E)
   end eq_refl.       (* I don't like this ^ subtraction in N but it's too late *)

 
Lemma Z_of_uint_of_sint {width: N} (a: sint width):
  Z_of_uint (uint_of_sint a) =
    let z := Z_of_sint a in
    match z with
    | Z0 | Zpos _ => z
    | Zneg p => (z + 2^(Z.of_N width))%Z
    end.
Proof.
unfold Z_of_uint.
unfold uint_of_sint.
remember (fun p (E : Z_of_sint a = Z.pos p) => uint_of_N (N.pos p) (uint_of_sint_pos_spec a p E))
  as branch_pos.
remember (fun p (E : Z_of_sint a = Z.neg p) =>
   uint_of_N (2 ^ width - N.pos p) (uint_of_sint_neg_spec a p E))
  as branch_neg.
assert(PosOk: forall p E, Z_of_bound_int (branch_pos p E) = Zpos p).
{ intros. subst. trivial. }
assert(NegOk: forall p E, Z_of_bound_int (branch_neg p E) = Zneg p + 2^(Z.of_N width)).
{ 
  intros. subst. cbn. clear PosOk.
  assert (P: 0 < 2 ^ Z.of_N width). { apply Z_0_lt_pow2. apply N2Z.is_nonneg. }
  remember (2 ^ Z.of_N width) as m.
  destruct m. { now apply Z.lt_irrefl in P. }
  2:{ exfalso. rewrite<- Z.ltb_lt in P. cbn in P. discriminate. }
  clear P.
  unfold Z_of_sint in E.
  rewrite<- Pos2Z.add_pos_neg.
  rewrite Heqm. clear Heqm.
  assert (U := bound_int_lower a).
  assert (Q: (N.pos p <= 2 ^ width)%N).
  {
    rewrite E in U.
    rewrite<- (Pos2Z.opp_pos p) in U.
    rewrite<- Z.opp_le_mono in U.
    rewrite N2Z.inj_le.
    rewrite N2Z.inj_pow. cbn.
    apply (Z.le_trans _ _ _ U).
    apply Z.pow_le_mono_r. { now rewrite<- Z.ltb_lt. }
    apply Z.le_pred_l.
  }
  rewrite N2Z.inj_sub; try assumption.
  rewrite N2Z.inj_pow. cbn.
  rewrite<- (Pos2Z.opp_pos p). rewrite Z.add_opp_r. trivial.
}
clear Heqbranch_pos Heqbranch_neg.
destruct (Z_of_sint a); easy.
Qed.

Local Lemma sint_of_uint_high {width: positive}
                               (z: Z)
                               (H : (Z.ones (Zpos width - 1) <? z) = true)
                               (U: z < 2 ^ Zpos width):
  - 2 ^ (Zpos width - 1) <= z - 2 ^ Zpos width < 2 ^ (Zpos width - 1).
Proof.
rewrite Z.ones_equiv in H.
rewrite Z.ltb_lt in H.
rewrite Z.lt_pred_le in H.
replace (2 ^ Zpos width) with (2 ^ (Z.succ (Z.pred (Zpos width)))) in *.
2:{ f_equal. now rewrite Z.succ_pred. }
replace (Z.pred (Zpos width)) with (Zpos width - 1)%Z in *. 2:{ trivial. }
rewrite Z.pow_succ_r in *; lia.
Qed.

Local Lemma sint_of_uint_low {width: positive}
                              (z: Z)
                              (L: (Z.ones (Z.pos width - 1) <? z) = false)
                              (NN: 0 <= z):
  - 2 ^ (Z.pos width - 1) <= z < 2 ^ (Z.pos width - 1).
Proof.
rewrite Z.ones_equiv in L.
rewrite Z.ltb_ge in L.
rewrite<- Z.lt_le_pred in L.
split; try assumption.
refine (Z.le_trans _ _ _ _ NN).
rewrite Z.opp_nonpos_nonneg.
apply Z.pow_nonneg.
rewrite<- Z.leb_le. trivial.
Qed.

Definition sint_of_uint {width: positive} (a: uint (Npos width))
: sint (Npos width)
:= let z := Z_of_uint a in
   (if (Z.ones (Zpos width - 1) <? z)%Z as b return _ = b -> _
     then fun H => bound_int_of_Z_conj (z - 2^(Zpos width))
                                        (sint_of_uint_high z H (bound_int_upper a))
     else fun L => bound_int_of_Z_conj z 
                                        (sint_of_uint_low z L (bound_int_lower a))) 
       eq_refl.

(* Same but without proofs: *)
Lemma Z_of_sint_of_uint {width: positive} (a: uint (Npos width)):
  Z_of_sint (sint_of_uint a) =
   let z := Z_of_uint a in
   if (Z.ones (Zpos width - 1) <? z)%Z
     then z - 2 ^ (Zpos width)
     else z.
Proof.
unfold sint_of_uint.
(* TODO: write a tactic for this: *)
remember (fun H : (Z.ones (Z.pos width - 1) <? Z_of_uint a) = true =>
     bound_int_of_Z_conj (Z_of_uint a - 2 ^ Z.pos width)
       (sint_of_uint_high (Z_of_uint a) H (bound_int_upper a))) 
  as high_branch.
remember (fun L : (Z.ones (Z.pos width - 1) <? Z_of_uint a) = false =>
     bound_int_of_Z_conj (Z_of_uint a) (sint_of_uint_low (Z_of_uint a) L (bound_int_lower a)))
  as low_branch.
assert(HighOk: forall H, Z_of_bound_int (high_branch H) = Z_of_uint a - 2 ^ Z.pos width).
{ intro. subst. trivial. }
assert(LowOk: forall L, Z_of_bound_int (low_branch L) = Z_of_uint a).
{ intro. subst. trivial. }
clear Heqhigh_branch Heqlow_branch.
destruct (Z.ones (Z.pos width - 1) <? Z_of_uint a).
{ apply (HighOk eq_refl). }
{ apply (LowOk eq_refl). }
Qed.

Example sint_of_uint_example:
  Z_of_sint (sint_of_uint (uint_not (uint_0 8))) = -1%Z.
Proof. trivial. Qed.

Lemma Z_pow2_pos_pred (p: positive):
  2 ^ Z.pos p = 2 * 2 ^ (Z.pos p - 1).
Proof.
replace (2 ^ Z.pos p) with (2 ^ Z.succ (Z.pos p - 1)).
{ apply Z.pow_succ_r. lia. }
f_equal. lia.
Qed.

Lemma sint_of_uint_of_sint {width: positive} (s: sint (Npos width)):
  sint_of_uint (uint_of_sint s) = s.
Proof.
apply bound_int_irrel.
replace (Z_of_bound_int (sint_of_uint (uint_of_sint s)))
  with (Z_of_sint (sint_of_uint (uint_of_sint s))) by trivial.
rewrite Z_of_sint_of_uint.
rewrite Z_of_uint_of_sint.
rewrite Z.ones_equiv.
assert(LB := bound_int_lower s).
assert(UB := bound_int_upper s).
replace (Z.of_N (N.pos width)) with (Z.pos width) in * by trivial.
unfold Z_of_sint.
remember (Z_of_bound_int s) as z. clear Heqz s. subst.
assert (K: 0 <= Z.pred (2 ^ (Z.pos width - 1))).
{
  apply Zlt_0_le_0_pred.
  apply Z_0_lt_pow2.
  lia.
}
destruct z. { rewrite<- Z.ltb_ge in K. now rewrite K. }
{
  assert (M: Z.pos p <= Z.pred (2 ^ (Z.pos width - 1))).
  {
    replace (Z.of_N (N.pos width)) with (Z.pos width) in UB by trivial.
    lia.
  }
  rewrite<- Z.ltb_ge in M. rewrite M. trivial.
}
assert (M: Z.pred (2 ^ (Z.pos width - 1)) < Z.neg p + 2 ^ Z.of_N (N.pos width)).
{
  replace (Z.of_N (N.pos width)) with (Z.pos width) in * by trivial.
  rewrite (Z_pow2_pos_pred width). lia.
}
rewrite<- Z.ltb_lt in M. rewrite M.
replace (Z.of_N (N.pos width)) with (Z.pos width) in * by trivial.
lia.
Qed.

Lemma uint_of_sint_of_uint {width: positive} (u: uint (Npos width)):
  uint_of_sint (sint_of_uint u) = u.
Proof.
apply bound_int_irrel.
replace (Z_of_bound_int (uint_of_sint (sint_of_uint u))) 
   with (Z_of_uint (uint_of_sint (sint_of_uint u))) by trivial.
rewrite Z_of_uint_of_sint. rewrite Z_of_sint_of_uint.
assert(LB := bound_int_lower u).
assert(UB := bound_int_upper u).
replace (Z_of_uint u) with (Z_of_bound_int u) by trivial.
remember (Z_of_bound_int u) as z. clear Heqz u.
replace (Z.of_N (N.pos width)) with (Z.pos width) in * by trivial.
rewrite Z.ones_equiv. rewrite (Z_pow2_pos_pred width) in *.
remember (2 ^ (Z.pos width - 1)) as m.
assert(M: 0 < m). { subst. apply Z_0_lt_pow2. lia. }
cbn. clear Heqm.
remember (Z.pred m <? z) as f. symmetry in Heqf.
destruct m; try lia.
destruct f; remember (z - Z.pos p~0) as y; destruct y; try lia.
destruct z; lia.
Qed.

(*************************************************************************)

Lemma sint_minus_1_lower (width: positive):
  (- 2 ^ (Z.of_N (N.pos width) - 1)) <= -1.
Proof.
apply Zlt_succ_le.
apply Z.opp_neg_pos.
apply Z_0_lt_pow2.
lia.
Qed.

Lemma sint_0_lower (width: positive):
  (- 2 ^ (Z.of_N (N.pos width) - 1)) <= 0.
Proof.
apply (Z.le_trans _ _ _ (sint_minus_1_lower _)).
rewrite<- Z.leb_le. trivial.
Qed.

Lemma sint_0_upper (width: positive):
  0 < 2 ^ (Z.of_N (N.pos width) - 1).
Proof.
apply Z_0_lt_pow2.
lia.
Qed.

Lemma sint_minus_1_upper (width: positive):
  -1 < 2 ^ (Z.of_N (N.pos width) - 1).
Proof.
refine (Z.lt_trans _ _ _ _ (sint_0_upper _)).
rewrite<- Z.ltb_lt. trivial.
Qed.

Definition sint_0 (width: positive)
: sint (Npos width)
:= bound_int_of_Z 0%Z (sint_0_lower width) (sint_0_upper width).

Definition sint_minus_1 (width: positive)
: sint (Npos width)
:= bound_int_of_Z (-1)%Z (sint_minus_1_lower width) (sint_minus_1_upper width).

Definition sint_lowest (width: positive)
: sint (Npos width)
:= bound_int_of_Z (- 2 ^ (Z.of_N (Npos width) - 1))
                  (Z.le_refl _) 
                  (Z.le_lt_trans _ _ _ (sint_0_lower width) (sint_0_upper width)).

(*************************************************************************)

Definition sdiv (a b: Z) := Z.sgn a * Z.sgn b * (Z.abs a / Z.abs b).

Lemma sdiv_0_r (a: Z):
  sdiv a 0 = 0.
Proof.
unfold sdiv. cbn. rewrite Z.mul_0_r. rewrite Z.mul_0_l. trivial.
Qed.

Lemma sdiv_1_r (a: Z):
  sdiv a 1 = a.
Proof.
unfold sdiv. cbn. rewrite Z.mul_1_r. rewrite Z.div_1_r.
now destruct a.
Qed.

Lemma abs_sdiv (a b: Z):
  Z.abs (sdiv a b) = Z.abs a / Z.abs b.
Proof.
unfold sdiv.
rewrite<- Z.mul_assoc.
rewrite Z_abs_sgn.
rewrite Z_abs_sgn.
remember (Z.abs a / Z.abs b) as q.
assert(Q: 0 <= q). { subst. apply Z_div_nonneg; apply Z.abs_nonneg. }
destruct a, b; try easy; now apply Z.abs_eq.
Qed.

Lemma abs_sdiv_le (a b: Z):
  Z.abs (sdiv a b) <= Z.abs a.
Proof.
rewrite abs_sdiv.
apply Z2N.inj_le; try apply Z_div_nonneg; try rewrite Z2N.inj_div; try apply Z.abs_nonneg. 
apply N_div_le.
Qed.

Lemma abs_sdiv_lt (a b: Z)
                  (A: 0 < Z.abs a)
                  (B: 1 < Z.abs b):
  Z.abs (sdiv a b) < Z.abs a.
Proof.
rewrite abs_sdiv. now apply Z.div_lt.
Qed.

Lemma sint_sdiv_bound {width: positive} (a b: sint (Npos width))
      (E: ((Z_of_sint a =? Z_of_sint (sint_lowest width)) && (Z_of_sint b =? -1))%bool = false):
  - 2 ^ (Z.of_N (N.pos width) - 1) <= sdiv (Z_of_sint a) (Z_of_sint b) < 2 ^ (Z.of_N (N.pos width) - 1).
Proof.
assert(AL := bound_int_lower a).
assert(AU := bound_int_upper a).
assert(BL := bound_int_lower b).
assert(BU := bound_int_upper b).
unfold Z_of_sint in *.
remember (Z_of_bound_int a) as n. clear Heqn.
remember (Z_of_bound_int b) as m. clear Heqm.
apply Bool.andb_false_elim in E.
destruct E as [NotLowest | NotMinusOne].
{
  rewrite Z.eqb_neq in NotLowest.
  replace (Z_of_bound_int (sint_lowest width)) 
    with (- 2 ^ (Z.of_N (N.pos width) - 1))
    in NotLowest by trivial.
  assert(NL: - 2 ^ (Z.of_N (N.pos width) - 1) < n) by lia. clear AL.
  enough (- 2 ^ (Z.of_N (N.pos width) - 1) < sdiv n m < 2 ^ (Z.of_N (N.pos width) - 1)) by lia.
  rewrite<- Z.abs_lt. rewrite abs_sdiv.
  apply (Z.le_lt_trans _ _ _ (Z_abs_div_le _ _)).
  lia.
}
rewrite Z.eqb_neq in NotMinusOne.
assert(MZ: m = 0 \/ 0 < Z.abs m). { lia. }
case MZ; intro; subst. { rewrite sdiv_0_r. apply (bound_int_both (sint_0 width)). }
assert(NZ: n = 0 \/ 0 < Z.abs n). { lia. }
case NZ; intro; subst. { apply (bound_int_both (sint_0 width)). }
assert(M1: m = 1 \/ 1 < Z.abs m). { lia. }
case M1; intro; subst. { rewrite sdiv_1_r. tauto. }
enough (- 2 ^ (Z.of_N (N.pos width) - 1) < sdiv n m < 2 ^ (Z.of_N (N.pos width) - 1)) by lia.
rewrite<- Z.abs_lt. rewrite abs_sdiv.
refine (Z.lt_le_trans _ _ _ (Z.div_lt _ _ _ _) _); try lia.
Qed.

Definition sint_sdiv {width: positive} (a b: sint (Npos width))
: sint (Npos width)
:= (if ((Z_of_sint a =? Z_of_sint (sint_lowest width)) && (Z_of_sint b =? -1))%bool 
      as over return _ = over -> _ 
      then fun _ => a
      else fun E => bound_int_of_Z_conj (sdiv (Z_of_sint a) (Z_of_sint b)) 
                                         (sint_sdiv_bound a b E))
      eq_refl.

(*************************************************************************)

(* This is Ethereum's smod: the sign of b is ignored. *)
Definition smod (a b: Z) := Z.sgn a * (Z.abs a mod Z.abs b).
Lemma smod_0_r (a: Z):
  smod a 0 = 0.
Proof.
unfold smod. cbn. rewrite Zmod_0_r. now rewrite Z.mul_0_r.
Qed. 

Lemma sint_smod_bound {width: positive} (a b: sint (Npos width)):
  - 2 ^ (Z.of_N (N.pos width) - 1) <= smod (Z_of_sint a) (Z_of_sint b) < 2 ^ (Z.of_N (N.pos width) - 1).
Proof.
assert(AL := bound_int_lower a).
assert(AU := bound_int_upper a).
assert(BL := bound_int_lower b).
assert(BU := bound_int_upper b).
unfold Z_of_sint in *.
remember (Z_of_bound_int a) as n. clear Heqn.
remember (Z_of_bound_int b) as m. clear Heqm.
assert(M: m = 0 \/ 0 < Z.abs m) by lia.
case M; intro MZ. { subst. rewrite smod_0_r. apply (bound_int_both (sint_0 width)). }
clear M.
unfold smod.
assert (B := Z.mod_pos_bound (Z.abs n) (Z.abs m) MZ).
enough(- 2 ^ (Z.of_N (N.pos width) - 1) < Z.sgn n * (Z.abs n mod Z.abs m) < 2 ^ (Z.of_N (N.pos width) - 1)) by lia.
apply Z.abs_lt. rewrite Z_abs_sgn.
enough (Z.abs (Z.abs n mod Z.abs m) < 2 ^ (Z.of_N (N.pos width) - 1)) by now destruct n.
lia.
Qed.

Definition sint_smod {width: positive} (a b: sint (Npos width))
: sint (Npos width)
:= bound_int_of_Z_conj (smod (Z_of_sint a) (Z_of_sint b))
                       (sint_smod_bound a b).