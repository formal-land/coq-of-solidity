From Coq Require Import Arith NArith Lia.
Require Import Nibble Instructions List2 Logic2.

(** This is N(i, w) defined in (141), quite close to the paper. *)
Definition paper_next_valid_instruction_position (i: N) (b: byte)
:= let push1  := N_of_byte (byte_of_instruction (PUSH  1 eq_refl)) in
   let push32 := N_of_byte (byte_of_instruction (PUSH 32 eq_refl)) in
   let w := N_of_byte b in
   (if ((push1 <=? w)  &&  (w <=? push32))%bool
     then i + w - push1 + 2
     else i + 1)%N.

(** This is a nicer equivalent of the previous function. *)
Definition next_valid_instruction_position (i: N) (b: byte)
:= (i + match instruction_of_byte b with
        | Some (PUSH n _) => n + 1
        | _               => 1
        end)%N.

Lemma next_valid_instruction_position_ok (i: N) (b: byte):
  next_valid_instruction_position i b = paper_next_valid_instruction_position i b.
Proof.
unfold paper_next_valid_instruction_position.
match goal with
|- _ = if ?cond then (i + ?a - ?b + ?c)%N else (i + 1)%N =>
    replace (if cond then (i + a - b + c)%N else (i + 1)%N) 
      with  (i + if cond then a - b + c else 1)%N
end.
2:{
  remember (andb _ _) as cond. destruct cond.
  repeat (rewrite N.add_sub_assoc || rewrite N.add_assoc). 1-3: trivial.
  symmetry in Heqcond.
  apply Bool.andb_true_iff in Heqcond.
  apply N.leb_le. tauto.
}
unfold next_valid_instruction_position.
f_equal.
(* this is stupid, we need an is_push test *)
destruct b as (b7, b6, b5, b4, b3, b2, b1, b0).
destruct b7; destruct b6; destruct b5; destruct b4;
destruct b3; destruct b2; destruct b1; destruct b0; trivial.
Qed.

Lemma next_valid_instruction_position_bound (i: N) (b: byte):
  (i + 1 <= next_valid_instruction_position i b)%N.
Proof.
unfold next_valid_instruction_position.
destruct (instruction_of_byte b) as [op|]; try destruct op; try apply N.le_refl.
lia.
Qed.

(**
   This is as close to D_J(c, i) defined in (140) as feasible,
   however, fuel had to be introduced to satisfy Coq's termination check.
 *)
Fixpoint paper_valid_jump_destinations_from (code: list byte)
                                             (i: N)
                                             (fuel: nat)
: list N
:= match fuel with
   | O => nil
   | S remaining_fuel =>
      match List.nth_error code (N.to_nat i) with
      | None => nil
      | Some b =>
         let tail := paper_valid_jump_destinations_from
                       code
                       (next_valid_instruction_position i b)
                       remaining_fuel
         in if (N_of_byte b =? N_of_byte (byte_of_instruction JUMPDEST))%N
                then i :: tail
                else tail
      end
   end.

Local Lemma valid_jump_destinations_from_2_helper
                (code: list byte)
                (i: N)
                (b: byte)
                (code_tail: list byte)
                (ok: code_tail = List.skipn (N.to_nat i) code):
  let next := next_valid_instruction_position i b in
  List.skipn (N.to_nat (next - i)) code_tail = List.skipn (N.to_nat next) code.
Proof.
subst. intro. unfold next_valid_instruction_position in next.
rewrite skipn_skipn.
f_equal. subst next.
rewrite N.add_comm.
rewrite<- N.add_sub_assoc by apply N.le_refl.
rewrite N.sub_diag.
rewrite N.add_0_r.
symmetry. apply N2Nat.inj_add.
Qed.

(* This version carries around the code tail so that it doesn't have to count from the start. *)
Local Fixpoint valid_jump_destinations_from_2 (code: list byte)
                                                (i: N)
                                                (fuel: nat)
                                                (code_tail: list byte)
                                                (ok: code_tail = List.skipn (N.to_nat i) code)
: list N
:= match fuel with
   | O => nil
   | S remaining_fuel =>
      match List.hd_error code_tail with
      | None => nil
      | Some b =>
         let next := next_valid_instruction_position i b in
         let tail := valid_jump_destinations_from_2
                       code
                       next
                       remaining_fuel
                       (List.skipn (N.to_nat (next - i)) code_tail)
                       (valid_jump_destinations_from_2_helper code i b code_tail ok)
         in if (N_of_byte b =? N_of_byte (byte_of_instruction JUMPDEST))%N
                then (i :: tail)%list
                else tail
      end
   end.

Local Lemma valid_jump_destinations_from_2_ok (code: list byte)
                                                (i: N)
                                                (fuel: nat)
                                                (code_tail: list byte)
                                                (ok: code_tail = List.skipn (N.to_nat i) code):
  paper_valid_jump_destinations_from code i fuel
   =
  valid_jump_destinations_from_2 code i fuel code_tail ok.
Proof.
revert ok. revert code_tail. revert i code.
induction fuel. { easy. }
intros. cbn.
subst code_tail. rewrite<- List2.nth_hd_skipn.
destruct (List.nth_error code (N.to_nat i)). 2:{ trivial. }
destruct (N_of_byte b =? _)%N; now rewrite<- IHfuel.
Qed.

(* This version replaces hd_error with a match and also drops [code] and [ok] parameters. *)
Local Fixpoint valid_jump_destinations_from_3 (code_tail: list byte)
                                                (i: N)
                                                (fuel: nat)
: list N
:= match fuel with
   | O => nil
   | S remaining_fuel =>
      match code_tail with
      | nil => nil
      | (b :: _)%list =>
         let next := next_valid_instruction_position i b in
         let tail := valid_jump_destinations_from_3
                       (List.skipn (N.to_nat (next - i)) code_tail)
                       next
                       remaining_fuel
         in if (N_of_byte b =? N_of_byte (byte_of_instruction JUMPDEST))%N
                then (i :: tail)%list
                else tail
      end
   end.

Local Lemma valid_jump_destinations_from_3_ok (code: list byte)
                                               (i: N)
                                               (fuel: nat)
                                               (code_tail: list byte)
                                               (ok: code_tail = List.skipn (N.to_nat i) code):
  valid_jump_destinations_from_3 code_tail i fuel
   =
  valid_jump_destinations_from_2 code i fuel code_tail ok.
Proof.
revert code i code_tail ok.
induction fuel. { easy. }
intros. cbn.
destruct code_tail; cbn. { trivial. }
destruct (N_of_byte b =? _)%N; now rewrite<- IHfuel.
Qed.

(* This version gets rid of the fuel and does skipping by itself. *)
Local Fixpoint valid_jump_destinations_from_4 (code: list byte) (current: N) (next_valid: N)
: list N
:= match code with
   | nil => nil
   | (h :: t)%list =>
        if (current <? next_valid)%N
           then valid_jump_destinations_from_4 t (current + 1)%N next_valid
           else
             let tail := valid_jump_destinations_from_4 t 
                                                        (current + 1)%N
                                                        (next_valid_instruction_position current h)
             in if (N_of_byte h =? N_of_byte (byte_of_instruction JUMPDEST))%N
                  then (current :: tail)%list
                  else tail
  end.

Local Lemma valid_jump_destinations_from_4_skips (code: list byte) (current: N) (next_valid: N)
                                                  (ok: (current <= next_valid)%N):
  valid_jump_destinations_from_4 code current next_valid
   =
  valid_jump_destinations_from_4 (List.skipn (N.to_nat (next_valid - current)) code) 
                                 next_valid 
                                 next_valid.
Proof.
remember (N.to_nat (next_valid - current)) as k.
assert(K: next_valid = (current + N.of_nat k)%N) by lia.
clear Heqk ok. subst next_valid.
revert code current.
induction k; intros. { cbn. now repeat rewrite N.add_0_r. }
destruct code; cbn. { trivial. }
replace (current <? current + N.pos (Pos.of_succ_nat k))%N with true. 
2:{
  symmetry.
  apply N.ltb_lt.
  lia.
}
replace (current + N.pos (Pos.of_succ_nat k))%N with (current + 1 + N.of_nat k)%N by lia.
apply IHk.
Qed.

Local Lemma valid_jump_destinations_from_4_ok (code: list byte)
                                               (i: N)
                                               (fuel: nat)
                                               (EnoughFuel: (length code < fuel)%nat):
  valid_jump_destinations_from_4 code i i
   =
  valid_jump_destinations_from_3 code i fuel.
Proof.
revert code EnoughFuel i.
induction fuel; intros. { now apply Nat.nlt_0_r in EnoughFuel. }
cbn. destruct code. { easy. }
cbn.
replace (i <? i)%N with false.
2:{ symmetry. apply (b_false (N.ltb_lt _ _)). apply N.lt_irrefl. }
replace (valid_jump_destinations_from_4 code (i + 1) (next_valid_instruction_position i b))
  with (valid_jump_destinations_from_3
        (List.skipn (N.to_nat (next_valid_instruction_position i b - i)) (b :: code))
        (next_valid_instruction_position i b) fuel).
{ trivial. }
assert (B := next_valid_instruction_position_bound i b).
rewrite valid_jump_destinations_from_4_skips by assumption.
symmetry. rewrite IHfuel.
{ 
  replace (N.to_nat (next_valid_instruction_position i b - i))
     with (S ((N.to_nat (next_valid_instruction_position i b - (i + 1))))) by lia.
  now rewrite List.skipn_cons.
}
rewrite List.skipn_length.
cbn in EnoughFuel.
lia.
Qed.