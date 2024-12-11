From Coq Require Import Arith.
From Coq Require List.

(** A tuplevector is a tuple containing items of the same type. *)
Fixpoint t (T: Type) (n: nat)
: Type
:= match n with
   | O => unit
   | 1%nat => T
   | S k => (t T k * T)%type
   end.

(** The tuplevector type simply expands to a power of its base type: *)
Local Example type_example: t nat 3 = (nat * nat * nat)%type.
Proof. trivial. Qed.

(** Coq already has a notation for a tuplevector. The type needs to be supplied though. *)
Local Example example_tuple_5: t nat 5 := (10, 20, 30, 40, 50).

(** As an exception, a tuple with one item is just the item itself.
    In Lisp terms, a tuple is an improper list (also backwards, that is,
    the head is in the rightmost position).
 *)
Local Example example_tuple_1: t nat 1 := 10.

(** Let can destructure a tuplevector with an apostrophe: *)
Local Example destructuring_example:
  (let tuple := (10, 20, 30, 40, 50): t nat 5 in
   let '(a, b, c, d, e) := tuple in 
   a) 
    = 
  10.
Proof. trivial. Qed.

(** [snoc] is a term from Haskell, it means cons backwards. *)
Definition snoc {T n} (tv: t T n) (last: T)
: t T (S n)
:= match n, tv with
   | 0, _ => last
   | S _, x => (x, last)
   end.

Local Example snoc_example:
  snoc ((10, 20, 30): t nat 3) 40 = (10, 20, 30, 40).
Proof. trivial. Qed.

Definition last {T n} (tv: t T (S n))
: T
:= match n, tv with
   | 0, x => x
   | S _, (_, x) => x
   end.

Lemma last_of_snoc {T n} (tv: t T n) (x: T):
  last (snoc tv x) = x.
Proof.
destruct n; easy.
Qed.

Definition but_last {T n} (tv: t T (S n))
: t T n
:= match n, tv with
   | 0, x => tt
   | S k, (rest, x) => rest
   end.

Lemma but_last_of_snoc {T n} (tv: t T n) (x: T):
  but_last (snoc tv x) = tv.
Proof.
destruct n. { now destruct tv. }
destruct n; easy.
Qed.

Lemma snoc_ok {T n} (tv: t T (S n)):
  snoc (but_last tv) (last tv) = tv.
Proof.
destruct n. { easy. }
now destruct tv.
Qed.

Fixpoint app_to_list {T n} (tv: t T n) (l: list T)
: list T
:= match n as n' return (t T n' -> list T) with
   | 0 => fun _ => l
   | S k => fun tv' => app_to_list (but_last tv') (last tv' :: l)%list
   end tv.

Local Example app_to_list_example:
  app_to_list ((5, 15): t _ 2) (10 :: 20 :: 30 :: nil)%list = (5 :: 15 :: 10 :: 20 :: 30 :: nil)%list.
Proof. trivial. Qed.

Lemma app_to_list_length {T n} (tv: t T n) (l: list T):
  length (app_to_list tv l) = n + length l.
Proof.
revert l.
induction n. { easy. }
cbn. intros. rewrite IHn. cbn.
symmetry. apply plus_n_Sm.
Qed.

Fixpoint prepend {T: Type} {n: nat} (new: T) (tv: t T n)
: t T (S n)
:= match n, tv with
   | 0, _ => new
   | S _, x => (prepend new (but_last x), last x)
   end.

Local Example prepend_example:
  prepend 5 ((2, 3, 4): t nat 3) = (5, 2, 3, 4).
Proof. trivial. Qed.

Fixpoint rev {T: Type} {n: nat} (tv: t T n)
: t T n
:= match n, tv with
   | 0, _ => tt
   | S _, x => prepend (last x) (rev (but_last x))
   end.

Local Example rev_example:
   rev ((1, 2, 3, 4): t nat 4) = (4, 3, 2, 1).
Proof. trivial. Qed.

(************************************************)

Local Lemma take_from_list_helper {T k} {head: T} {tail: list T}
                                   (H: S k <= length (head :: tail)%list):
  k <= length tail.
Proof.
apply le_S_n. apply H.
Qed. 

Fixpoint take_from_list_rev {T n} (l: list T) (ok: n <= length l)
: t T n * list T
:= match n as n' return n' <= length l -> t T n' * list T with
   | O => fun _ => (tt, l)
   | S k =>
      match l as l' return S k <= length l' -> t T (S k) * list T with
      | nil => fun X => False_rect _ (Nat.nle_succ_0 k X)
      | (head :: tail)%list => fun X =>
           let (prefix, rest) := take_from_list_rev tail (take_from_list_helper X) in
           (snoc prefix head, rest)
      end
   end ok.

Fixpoint to_list_backwards {T n} (tv: t T n)
: list T
:= match n, tv with
   | 0, _ => nil
   | S _, x => last x :: to_list_backwards (but_last x)
   end.

Local Example to_list_backwards_example:
   to_list_backwards ((1, 2, 3, 4): t nat 4) = (4 :: 3 :: 2 :: 1 :: nil)%list.
Proof. trivial. Qed.

Lemma take_from_list_rev_firstn {T n} (l: list T) (ok: n <= length l):
  to_list_backwards (fst (take_from_list_rev l ok)) = List.firstn n l.
Proof.
revert l ok. induction n, l; try easy. intros.
cbn.
assert (M := IHn l (take_from_list_helper ok)).
remember (take_from_list_rev l (take_from_list_helper ok)) as pq. destruct pq as (p, q).
cbn in *.
rewrite last_of_snoc. rewrite but_last_of_snoc. f_equal.
exact M.
Qed.

Lemma take_from_list_rev_skipn {T n} (l: list T) (ok: n <= length l):
  snd (take_from_list_rev l ok) = List.skipn n l.
Proof.
revert l ok. induction n, l; try easy. intros.
cbn.
assert (M := IHn l (take_from_list_helper ok)).
remember (take_from_list_rev l (take_from_list_helper ok)) as pq. destruct pq as (p, q).
cbn in *. exact M.
Qed.

(** This function fixes the flip of take_from_list_rev by applying rev.
    The name reflects the opinion that this function should be avoided 
    because rev is quadratic.
 *)
Definition take_from_list_slow {T n} (l: list T) (ok: n <= length l)
: t T n * list T
:= let (prefix, rest) := take_from_list_rev l ok
   in (rev prefix, rest).

(**********************************************************************************)

Local Lemma gather_helper_nil {T} {x: T} {l: list T} {block_len}:
  ~ (length (x :: l) = 0 * block_len).
Proof. discriminate. Qed.

Local Lemma gather_helper_block_len {T} (k block_len: nat) (l: list T)
                                     (E : length l = S k * block_len):
  block_len <= length l.
Proof. 
rewrite E.
rewrite<- Nat.mul_1_l at 1.
apply Nat.mul_le_mono_r.  
apply le_n_S.
apply Nat.le_0_l.
Qed.

Definition take_from_list_rev_dep_skipn {T n} (l: list T) (ok: n <= length l)
: { x: t T n * list T | snd x = List.skipn n l }
:= exist _ (take_from_list_rev l ok) (take_from_list_rev_skipn l ok).

Local Lemma gather_helper_skipn {T k block_len l}
            (ok: length l = S k * block_len)
            (p: {x : t T block_len * list T | snd x = List.skipn block_len l}):
  length (snd (proj1_sig p)) = k * block_len.
Proof.
assert (P := proj2_sig p). cbn in P. rewrite P.
rewrite List.skipn_length.
rewrite ok.
cbn.
rewrite Nat.add_comm.
rewrite Nat.add_sub.
trivial.
Qed.

Fixpoint gather {T} (l: list T) (n block_len: nat) (ok: length l = n * block_len)
{struct n}
: list (t T block_len)
:= match n as n' return length l = n' * block_len -> list (t T block_len) with
   | O => match l as l' return length l' = 0 * block_len -> _ with
          | nil => fun _ => nil
          | cons _ _ => fun ok' => False_rect _ (gather_helper_nil ok')
          end
   | S k => fun ok' =>
              let p := take_from_list_rev_dep_skipn l (gather_helper_block_len k block_len l ok') in
              (fst (proj1_sig p) :: gather (snd (proj1_sig p)) k block_len
                                           (gather_helper_skipn ok' p))%list
   end ok.

Example gather_example:
  gather (1 :: 2 :: 3 :: 4 :: 5 :: 6 :: 7 :: 8 :: 9 :: 10 :: nil)%list 5 2 eq_refl
   =
  ((2, 1) :: (4, 3) :: (6, 5) :: (8, 7) :: (10, 9) :: nil)%list.
Proof. trivial. Qed.

Lemma gather_length {T} (l: list T) (n block_len: nat) (ok: length l = n * block_len):
  List.length (gather l n block_len ok) = n.
Proof.
revert l ok. induction n; intros; destruct l; cbn;
  trivial; try easy; f_equal; apply IHn.
Qed.