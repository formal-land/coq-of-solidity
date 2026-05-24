From Coq Require Import QArith Qround.

Require Arith2.

Lemma Q_floor_via_Z (a: Z) (b: positive):
  Qfloor (a # b) = (a / Zpos b)%Z.
Proof.
rewrite Zdiv_Qdiv.
rewrite Qmake_Qdiv.
trivial.
Qed.

Lemma Q_ceiling_via_Z (a: Z) (b: positive):
  Qceiling (a # b) = (- ((- a) / Zpos b))%Z.
Proof.
unfold Qround.Qceiling.
rewrite Qmake_Qdiv.
rewrite Zdiv_Qdiv.
rewrite inject_Z_opp.
f_equal. f_equal.
unfold Qdiv. unfold Qmult. cbn.
repeat rewrite Z.mul_1_r.
trivial.
Qed.

Lemma Q_ceiling_via_Z_floor (a: Z) (b: positive):
  Qceiling (a # b) = ((a + Z.pos b - 1) / Zpos b)%Z.
Proof.
rewrite Q_ceiling_via_Z.
apply Arith2.Z_ceiling_via_floor.
rewrite<- Z.leb_le.
trivial.
Qed.