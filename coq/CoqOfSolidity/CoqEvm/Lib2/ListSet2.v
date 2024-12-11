(**
 This file continues theories/Lists/ListSet.v from the standard library of Coq.
 *)

From Coq Require Import List ListSet.

(** in_dec is a sumbool version of set_mem. *)
Lemma set_mem_in_dec {M: Type} (E: forall x y: M, {x = y} + {x <> y})
                     (x: M) (l: list M):
  set_mem E x l = if in_dec E x l then true else false.
Proof.
induction l. { trivial. }
simpl. destruct (E x a) as [EQ | NE].
{ subst. now destruct (E a a). }
remember (match E a x with left _ => _ | right _ => _ end) as m.
destruct (E a x) as [EQ | NE2].
{ clear Heqm. symmetry in EQ. contradiction. }
destruct in_dec; now subst.
Qed.

Lemma set_mem_true {M: Type} (E: forall x y: M, {x = y} + {x <> y})
                     (x: M) (l: list M):
  set_mem E x l = true <-> In x l.
Proof.
rewrite set_mem_in_dec.
now destruct in_dec.
Qed.

Lemma set_mem_false {M: Type} (E: forall x y: M, {x = y} + {x <> y})
                     (x: M) (l: list M):
  set_mem E x l = false <-> ~In x l.
Proof.
rewrite set_mem_in_dec.
now destruct in_dec.
Qed.

(** nodup doesn't change set_mem.
    This is a set_mem version of [nodup_In l x: In x (nodup l) <-> In x l].
 *)
Lemma set_mem_nodup {M: Type} (E: forall x y: M, {x = y} + {x <> y})
                    (x: M) (l: list M):
  set_mem E x (nodup E l) = set_mem E x l.
Proof.
repeat rewrite set_mem_in_dec.
destruct in_dec as [IN | IN]; 
  rewrite nodup_In in IN; 
  destruct in_dec; 
  trivial;
  contradiction.
Qed.

Definition nodup_list_in {M: Type} (E: forall x y: M, {x = y} + {x <> y})
                          (x: M) (a: {l : list M | NoDup l})
: bool
:= set_mem E x (proj1_sig a).

Definition list_is_empty {M: Type} (l: list M)
: bool
:= match l with
   | nil => true
   | _ => false
   end.

Lemma list_is_empty_ok {M: Type} (l: list M):
  list_is_empty l = true <-> l = nil.
Proof.
destruct l; cbn. { tauto. }
split; congruence.
Qed.

Lemma list_add_ok {M: Type} (E: forall x y: M, {x = y} + {x <> y})
                   (x: M) (l: list M) (y: M):
  set_mem E y (set_add E x l) = if E x y then true else set_mem E y l.
Proof.
destruct (E x y) as [EQ|NE].
{
  apply set_mem_correct2. 
  apply set_add_intro2.
  symmetry. assumption.
}
remember (set_mem E y l) as m.
destruct m; symmetry in Heqm.
{
  apply set_mem_correct1 in Heqm.
  apply set_mem_correct2.
  apply set_add_intro1. assumption.
}
apply set_mem_complete1 in Heqm.
apply set_mem_complete2.
intro H. apply set_add_elim2 in H. { contradiction. }
intro EQ. symmetry in EQ. contradiction.
Qed.

Definition nodup_list_add {M: Type} (E: forall x y: M, {x = y} + {x <> y})
                           (x: M) (a: {l : list M | NoDup l})
: {l : list M | NoDup l}
:= exist _ (set_add E x (proj1_sig a))
           (set_add_nodup E x (proj2_sig a)).

Lemma nodup_list_add_ok {M: Type} (E: forall x y: M, {x = y} + {x <> y})
                         (x: M) (a: {l : list M | NoDup l}) (y: M):
  nodup_list_in E y (nodup_list_add E x a) = if E x y then true else nodup_list_in E y a.
Proof.
apply list_add_ok.
Qed.

Lemma list_remove_ok {M: Type} (E: forall x y: M, {x = y} + {x <> y})
                   (x: M) (l: list M) (N: NoDup l) (y: M):
  set_mem E y (set_remove E x l) = if E x y then false else set_mem E y l.
Proof.
destruct (E x y) as [EQ|NE].
{
  apply set_mem_complete2. intro H.
  apply (set_remove_2 E N H). 
  symmetry. assumption.
}
remember (set_mem E y l) as m.
destruct m; symmetry in Heqm.
{
  apply set_mem_correct1 in Heqm.
  apply set_mem_correct2.
  apply set_remove_3. assumption.
  intro H. symmetry in H. contradiction.
}
apply set_mem_complete1 in Heqm.
apply set_mem_complete2.
intro H. apply set_remove_1 in H. contradiction.
Qed.

Definition nodup_list_remove {M: Type} (E: forall x y: M, {x = y} + {x <> y})
                              (x: M) (a: {l : list M | NoDup l})
: {l : list M | NoDup l}
:= exist _ (set_remove E x (proj1_sig a))
           (set_remove_nodup E x (proj2_sig a)).

Lemma nodup_list_remove_ok {M: Type} (E: forall x y: M, {x = y} + {x <> y})
                            (x: M) (a: {l : list M | NoDup l}) (y: M):
  nodup_list_in E y (nodup_list_remove E x a) = if E x y then false else nodup_list_in E y a.
Proof.
apply list_remove_ok. apply (proj2_sig a).
Qed.

(****************************************************************************)

Ltac bool := repeat
  (  rewrite Bool.andb_true_iff in *
  || rewrite Bool.andb_false_iff in *
  || rewrite Bool.orb_true_iff in *
  || rewrite Bool.orb_false_iff in *
  || rewrite Bool.negb_true_iff in *
  || rewrite Bool.negb_false_iff in *
  || rewrite set_mem_true in *
  || rewrite set_mem_false in *).

Lemma list_union_ok {M: Type} (E: forall x y: M, {x = y} + {x <> y})
                     (a b: list M) (x: M):
      set_mem E x (set_union E a b)
       =
      orb (set_mem E x a) (set_mem E x b).
Proof.
remember (set_mem E x (set_union E a b)) as in_a_or_b.
symmetry. symmetry in Heqin_a_or_b. 
destruct in_a_or_b; bool; rewrite set_union_iff in Heqin_a_or_b; tauto.
Qed.

Lemma list_inter_ok {M: Type} (E: forall x y: M, {x = y} + {x <> y})
                     (a b: list M) (x: M):
      set_mem E x (set_inter E a b)
       =
      andb (set_mem E x a) (set_mem E x b).
Proof.
remember (set_mem E x (set_inter E a b)) as in_a_and_b.
symmetry. symmetry in Heqin_a_and_b.
destruct in_a_and_b;
 bool; rewrite set_inter_iff in Heqin_a_and_b.
{ assumption. }
destruct (in_dec E x a); destruct (in_dec E x b); tauto.
Qed.

Lemma list_diff_ok {M: Type} (E: forall x y: M, {x = y} + {x <> y})
                     (a b: list M) (x: M):
      set_mem E x (set_diff E a b)
       =
      andb (set_mem E x a) (negb (set_mem E x b)).
Proof.
remember (set_mem E x (set_diff E a b)) as in_a_and_not_b.
symmetry. symmetry in Heqin_a_and_not_b.
destruct in_a_and_not_b; bool;
  rewrite set_diff_iff in Heqin_a_and_not_b.
{ assumption. }
destruct (in_dec E x a); destruct (in_dec E x b); tauto.
Qed.

Definition nodup_list_union {M: Type} (E: forall x y: M, {x = y} + {x <> y})
                             (a b: {l : list M | NoDup l})
: {l : list M | NoDup l}
:= exist _ (set_union E (proj1_sig a) (proj1_sig b))
           (set_union_nodup E (proj2_sig a) (proj2_sig b)).

Definition nodup_list_inter {M: Type} (E: forall x y: M, {x = y} + {x <> y})
                             (a b: {l : list M | NoDup l})
: {l : list M | NoDup l}
:= exist _ (set_inter E (proj1_sig a) (proj1_sig b))
           (set_inter_nodup E (proj2_sig a) (proj2_sig b)).

Definition nodup_list_diff {M: Type} (E: forall x y: M, {x = y} + {x <> y})
                             (a b: {l : list M | NoDup l})
: {l : list M | NoDup l}
:= exist _ (set_diff E (proj1_sig a) (proj1_sig b))
           (set_diff_nodup E (proj2_sig a) (proj2_sig b)).

Lemma nodup_list_union_ok {M: Type} (E: forall x y: M, {x = y} + {x <> y})
                     (a b: {l : list M | NoDup l}) (x: M):
      nodup_list_in E x (nodup_list_union E a b)
       =
      orb (nodup_list_in E x a) (nodup_list_in E x b).
Proof.
apply list_union_ok.
Qed.

Lemma nodup_list_inter_ok {M: Type} (E: forall x y: M, {x = y} + {x <> y})
                     (a b: {l : list M | NoDup l}) (x: M):
      nodup_list_in E x (nodup_list_inter E a b)
       =
      andb (nodup_list_in E x a) (nodup_list_in E x b).
Proof.
apply list_inter_ok.
Qed.

Lemma nodup_list_diff_ok {M: Type} (E: forall x y: M, {x = y} + {x <> y})
                     (a b: {l : list M | NoDup l}) (x: M):
      nodup_list_in E x (nodup_list_diff E a b)
       =
      andb (nodup_list_in E x a) (negb (nodup_list_in E x b)).
Proof.
apply list_diff_ok.
Qed.

Definition nodup_list_forall {M: Type}
                              (a: {l : list M | NoDup l})
                              (p: M -> bool)
: bool
:= forallb p (proj1_sig a).

Lemma nodup_list_forall_ok {M: Type} (E: forall x y: M, {x = y} + {x <> y})
                            (a: {l : list M | NoDup l}) (p: M -> bool):
  nodup_list_forall a p = true
   <->
  forall x: M,
    nodup_list_in E x a = true -> p x = true.
Proof.
unfold nodup_list_forall. unfold nodup_list_in.
destruct a as (l, N). cbn. clear N.
rewrite forallb_forall.
split; intros H x Z.
{ rewrite set_mem_true in Z. exact (H x Z). }
rewrite<- set_mem_true in Z. exact (H x Z).
Qed.

Definition list_subset {M: Type} (E: forall x y: M, {x = y} + {x <> y})
                        (a b: list M)
: bool
:= forallb (fun x => set_mem E x b) a.

Definition nodup_list_subset {M: Type} (E: forall x y: M, {x = y} + {x <> y})
                              (a b: {l : list M | NoDup l})
: bool
:= list_subset E (proj1_sig a) (proj1_sig b).

Lemma list_subset_ok {M: Type} (E: forall x y: M, {x = y} + {x <> y})
                      (a b: list M):
    list_subset E a b = true 
     <->
    forall x: M,
      orb (negb (set_mem E x a)) (set_mem E x b) = true.
Proof.
unfold list_subset.
rewrite forallb_forall.
split; intros H x; assert (Hx := H x); bool;
  destruct (in_dec E x a); destruct (in_dec E x b); tauto.
Qed.

Lemma nodup_list_subset_ok {M: Type} (E: forall x y: M, {x = y} + {x <> y})
                           (a b: {l : list M | NoDup l}):
    nodup_list_subset E a b = true 
     <->
    forall x: M,
      orb (negb (nodup_list_in E x a)) (nodup_list_in E x b) = true.
Proof.
apply list_subset_ok.
Qed.

Definition list_set_eq {M: Type} (E: forall x y: M, {x = y} + {x <> y})
                        (a b: list M)
: bool
:= andb (list_subset E a b) (list_subset E b a).

Lemma list_set_eq_ok {M: Type} (E: forall x y: M, {x = y} + {x <> y})
                      (a b: list M):
    list_set_eq E a b = true 
     <->
    forall x: M,
      set_mem E x a = set_mem E x b.
Proof.
unfold list_set_eq. bool. repeat rewrite list_subset_ok.
split.
{
  intros H x.
  destruct H as (Ha, Hb).
  assert (Hax := Ha x). clear Ha.
  assert (Hbx := Hb x). clear Hb.
  now destruct (set_mem E x a); destruct (set_mem E x b).
}
intros H. split; intro x; assert (Hx := H x); bool; repeat rewrite<- (set_mem_true E).
  destruct (set_mem E x a); destruct (set_mem E x b); firstorder.
rewrite Hx. destruct (set_mem E x b); firstorder.
Qed.

Definition nodup_list_set_eq {M: Type} (E: forall x y: M, {x = y} + {x <> y})
                         (a b: {l : list M | NoDup l})
: bool
:= list_set_eq E (proj1_sig a) (proj1_sig b).

Lemma nodup_list_set_eq_ok {M: Type} (E: forall x y: M, {x = y} + {x <> y})
                      (a b: {l : list M | NoDup l}):
    nodup_list_set_eq E a b = true 
     <->
    forall x: M,
      nodup_list_in E x a = nodup_list_in E x b.
Proof.
apply list_set_eq_ok.
Qed.