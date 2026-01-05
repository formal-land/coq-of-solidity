From Coq Require Import List Arith.

Local Open Scope list_scope.

Lemma skipn_skipn {A} (l: list A) (n m: nat):
  skipn n (skipn m l) = skipn (n + m) l.
Proof.
revert n l.
induction m, l; intros; try repeat rewrite skipn_nil; try easy.
{ cbn. now rewrite Nat.add_0_r. }
replace (n + S m) with (S (n + m)) by auto with arith.
repeat rewrite skipn_cons.
apply IHm.
Qed.

Lemma nth_hd_skipn {A} (l: list A) (n: nat):
  nth_error l n = hd_error (skipn n l).
Proof.
revert l. induction n, l; try easy.
cbn. apply IHn.
Qed.

Fixpoint list_eqb {A} (eqb: A -> A -> bool) (l l': list A)
: bool
:= match l with
   | nil => match l' with
            | nil => true
            | _ => false
            end
   | h :: t => match l' with
               | nil => false
               | h' :: t' => if eqb h h'
                               then list_eqb eqb t t'
                               else false
               end
   end.

