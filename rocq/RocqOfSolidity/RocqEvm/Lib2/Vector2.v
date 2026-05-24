From Coq Require Vector.
From Coq Require List.

Fixpoint append_one {A: Type} {n: nat} (v: Vector.t A n) (new: A)
: Vector.t A (S n)
:= match v with
   | Vector.nil _ => Vector.cons _ new _ (Vector.nil _)
   | Vector.cons _ h _ t => Vector.cons _ h _ (append_one t new)
   end.

Fixpoint rev {A: Type} {n: nat} (v: Vector.t A n) 
: Vector.t A n
:= match v with
   | Vector.nil _ => Vector.nil _
   | Vector.cons _ h _ t => append_one (rev t) h
   end.

(* Try doing that with Vector.rev! *)
Example rev_example:
  rev
    (Vector.cons nat 30 2 (Vector.cons nat 20 1 (Vector.cons nat 10 0 (Vector.nil nat))))
  = (Vector.cons nat 10 2 (Vector.cons nat 20 1 (Vector.cons nat 30 0 (Vector.nil nat)))).
Proof. trivial. Qed.

Local Lemma vector_0_nil' {T: Type} {z} (v: Vector.t T z) (Zero: z = 0):
  v = match (eq_sym Zero) in _ = y return Vector.t T y with
      | eq_refl => Vector.nil _
      end.
Proof.
revert Zero v. destruct z, v; intros; try discriminate;
  assert (X: Zero = eq_refl) by (apply Eqdep_dec.eq_proofs_unicity; decide equality);
  now rewrite X.
Qed.

Lemma vector_0_nil {T: Type} (v: Vector.t T 0):
  v = Vector.nil _.
Proof.
apply vector_0_nil' with (Zero := eq_refl).
Qed.