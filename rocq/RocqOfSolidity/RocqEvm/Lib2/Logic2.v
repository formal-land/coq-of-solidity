From Coq Require Setoid.

Lemma b_false {b: bool} {P: Prop} (R: b = true <-> P):
  b = false <-> ~P.
Proof.
split; intro H; destruct b; try intro T; try easy.
{ apply R in T.  discriminate. }
exfalso. apply H. apply R. trivial.
Qed.

Lemma relation_quad {TA TB TC TD: Type}
                     {R1: TA -> TB -> Prop}
                     {R2: TC -> TD -> Prop}
                     {r1: TA -> TB -> bool}
                     {r2: TC -> TD -> bool}
                     (H1: forall x y, r1 x y = true <-> R1 x y)
                     (H2: forall x y, r2 x y = true <-> R2 x y)
                     (a: TA) (b: TB) (c: TC) (d: TD):
  (r1 a b = r2 c d) <-> (R1 a b <-> R2 c d).
Proof.
split; intro K; repeat rewrite<- H;
  remember (r1 a b) as rab; symmetry in Heqrab;
  remember (r2 c d) as rcd; symmetry in Heqrcd;
  destruct rab; destruct rcd;
  try rewrite H1 in Heqrab; try rewrite H2 in Heqrcd; try easy.
  {
    split; intro Q.
    { rewrite<- H1 in Q. rewrite Heqrab in Q. discriminate. }
    { rewrite<- H2 in Q. rewrite Heqrcd in Q. discriminate. }
  }
  {
    rewrite K in Heqrab. rewrite<- H2 in Heqrab.
    rewrite<- Heqrab. rewrite<- Heqrcd. reflexivity.
  }
  rewrite<- K in Heqrcd. rewrite<- H1 in Heqrcd.
  rewrite<- Heqrab. rewrite<- Heqrcd. reflexivity.
Qed.
