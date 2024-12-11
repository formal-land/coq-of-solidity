From Coq Require Import Ascii.
From Coq Require Import NArith.
From Coq Require Import ZArith.
From Coq Require Import Uint63.
From Coq Require Import Lia.
From Coq Require String Ascii.

From CoqOfSolidity Require Import UInt63 Arith2.

Inductive nibble := Nibble (x3 x2 x1 x0: bool).
Inductive hex_digit :=
| x0 | x1 | x2 | x3
| x4 | x5 | x6 | x7
| x8 | x9 | xA | xB
| xC | xD | xE | xF.

Definition ascii_of_hex_digit (digit: hex_digit) (lower: bool)
: ascii
:= match digit with
   | x0 => "0"
   | x1 => "1"
   | x2 => "2"
   | x3 => "3"
   | x4 => "4"
   | x5 => "5"
   | x6 => "6"
   | x7 => "7"
   | x8 => "8"
   | x9 => "9"
   | xA => if lower then "a" else "A"
   | xB => if lower then "b" else "B"
   | xC => if lower then "c" else "C"
   | xD => if lower then "d" else "D"
   | xE => if lower then "e" else "E"
   | xF => if lower then "f" else "F"
   end.

Definition hex_digit_of_ascii (a: ascii)
: option hex_digit
:= match a with
   | "0" => Some x0
   | "1" => Some x1
   | "2" => Some x2
   | "3" => Some x3
   | "4" => Some x4
   | "5" => Some x5
   | "6" => Some x6
   | "7" => Some x7
   | "8" => Some x8
   | "9" => Some x9
   | "a" | "A" => Some xA
   | "b" | "B" => Some xB
   | "c" | "C" => Some xC
   | "d" | "D" => Some xD
   | "e" | "E" => Some xE
   | "f" | "F" => Some xF
   | _ => None
   end%char.

Definition is_hex_digit (a: ascii)
:= match hex_digit_of_ascii a with
   | Some _ => true
   | None => false
   end.

Lemma hex_digit_of_ascii_of_hex_digit (h: hex_digit) (lower: bool):
  hex_digit_of_ascii (ascii_of_hex_digit h lower) = Some h.
Proof.
destruct lower; destruct h; trivial.
Qed.

Lemma is_hex_digit_true (a: ascii):
  is_hex_digit a = true  ->  hex_digit_of_ascii a <> None.
Proof.
unfold is_hex_digit. now destruct hex_digit_of_ascii.
Qed.

Definition hex_digit_of_ascii' (a: ascii) (ok: is_hex_digit a = true)
: hex_digit
:= match hex_digit_of_ascii a as h return _ = h -> _ with
   | Some x => fun _ => x
   | None => fun E => False_rect _ (is_hex_digit_true a ok E)
   end eq_refl.

Lemma hex_digit_of_ascii_of_hex_digit' (h: hex_digit) (lower: bool)
                                       (ok: is_hex_digit (ascii_of_hex_digit h lower) = true):
  hex_digit_of_ascii' (ascii_of_hex_digit h lower) ok = h.
Proof.
destruct lower; destruct h; trivial.
Qed.

Definition nibble_of_hex_digit (digit: hex_digit)
: nibble
:= match digit with
   | x0 => Nibble false false false false
   | x1 => Nibble false false false true
   | x2 => Nibble false false true  false
   | x3 => Nibble false false true  true
   | x4 => Nibble false true  false false
   | x5 => Nibble false true  false true
   | x6 => Nibble false true  true  false
   | x7 => Nibble false true  true  true
   | x8 => Nibble true  false false false
   | x9 => Nibble true  false false true
   | xA => Nibble true  false true  false
   | xB => Nibble true  false true  true
   | xC => Nibble true  true  false false
   | xD => Nibble true  true  false true
   | xE => Nibble true  true  true  false
   | xF => Nibble true  true  true  true
   end.

Definition hex_digit_of_nibble (n: nibble)
: hex_digit
:= match n with
   | Nibble false false false false => x0
   | Nibble false false false true  => x1
   | Nibble false false true  false => x2
   | Nibble false false true  true  => x3
   | Nibble false true  false false => x4
   | Nibble false true  false true  => x5
   | Nibble false true  true  false => x6
   | Nibble false true  true  true  => x7
   | Nibble true  false false false => x8
   | Nibble true  false false true  => x9
   | Nibble true  false true  false => xA
   | Nibble true  false true  true  => xB
   | Nibble true  true  false false => xC
   | Nibble true  true  false true  => xD
   | Nibble true  true  true  false => xE
   | Nibble true  true  true  true  => xF
   end.

Lemma hex_digit_of_nibble_of_hex_digit (d: hex_digit):
  hex_digit_of_nibble (nibble_of_hex_digit d) = d.
Proof.
destruct d; easy.
Qed.

Lemma nibble_of_hex_digit_of_nibble (n: nibble):
  nibble_of_hex_digit (hex_digit_of_nibble n) = n.
Proof.
destruct n as (a3, a2, a1, a0).
destruct a3; destruct a2; destruct a1; destruct a0; easy.
Qed.

Definition N_of_hex_digit (digit: hex_digit)
: N 
:= match digit with
   | x0 =>  0
   | x1 =>  1
   | x2 =>  2
   | x3 =>  3
   | x4 =>  4
   | x5 =>  5
   | x6 =>  6
   | x7 =>  7
   | x8 =>  8
   | x9 =>  9
   | xA => 10
   | xB => 11
   | xC => 12
   | xD => 13
   | xE => 14
   | xF => 15
   end.

Lemma N_of_hex_digit_ub (digit: hex_digit):
  (N_of_hex_digit digit < 16)%N.
Proof.
  destruct digit; cbn; rewrite<- N.ltb_lt; trivial.
Qed.

Definition N_of_nibble (n: nibble)
: N
:= let f (a: bool) := if a then xI else xO in
   match n with
   | Nibble true a2 a1 a0 => Npos (f a0 (f a1 (f a2 xH)))
   | Nibble false true a1 a0 => Npos (f a0 (f a1 xH))
   | Nibble false false true a0 => Npos (f a0 xH)
   | Nibble false false false true => Npos xH
   | Nibble false false false false => N0
   end.

Lemma N_of_nibble_bound (n: nibble):
  (N_of_nibble n < 16)%N.
Proof.
  destruct n as (a3, a2, a1, a0); destruct a3; destruct a2; destruct a1; destruct a0; easy.
Qed.

Lemma hex_digit_to_N_via_nibble (d: hex_digit):
  N_of_nibble (nibble_of_hex_digit d) = N_of_hex_digit d.
Proof.
  destruct d; easy.
Qed.

Lemma nibble_to_N_via_hex_digit (n: nibble):
  N_of_hex_digit (hex_digit_of_nibble n) = N_of_nibble n.
Proof.
  destruct n as (a3, a2, a1, a0); destruct a3; destruct a2; destruct a1; destruct a0; easy.
Qed.

Definition push_bit (n: N) (bit: bool)
: N
:= match n with
   | N0 => if bit then 1 else 0
   | Npos p => Npos ((if bit then xI else xO) p)
   end.

Lemma push_bit_arith (n: N) (bit: bool):
  push_bit n bit = (2 * n + if bit then 1 else 0)%N.
Proof.
destruct bit; now destruct n.
Qed.

Definition last_bit (n: N)
: bool
:= match n with
   | N0      | Npos (xO _) => false
   | Npos xH | Npos (xI _) => true
   end.

Lemma last_bit_odd (n: N):
  last_bit n = N.odd n.
Proof.
destruct n. { trivial. }
destruct p; easy.
Qed.

Lemma push_bit_then_shr1 (n: N) (bit: bool):
  N.div2 (push_bit n bit) = n.
Proof.
  destruct n; destruct bit; easy.
Qed.

Lemma last_of_push_bit (n: N) (bit: bool):
  last_bit (push_bit n bit) = bit.
Proof.
  destruct n; destruct bit; easy.
Qed.

Lemma push_last_bit (n: N):
  push_bit (N.div2 n) (last_bit n) = n.
Proof.
  destruct n. easy.
  destruct p; easy.
Qed.

Definition push_nibble (n: N) (nib: nibble)
: N
:= match nib with
   | Nibble a3 a2 a1 a0 => push_bit (push_bit (push_bit (push_bit n a3) a2) a1) a0
   end.

Lemma push_nibble_arith (n: N) (nib: nibble):
  push_nibble n nib = (16 * n + N_of_nibble nib)%N.
Proof.
destruct nib as (a3, a2, a1, a0).
unfold push_nibble.
repeat rewrite push_bit_arith.
repeat rewrite N.mul_add_distr_l.
repeat rewrite<- N.add_assoc.
f_equal.
{ now repeat rewrite N.mul_assoc. }
destruct a3; destruct a2; destruct a1; destruct a0; easy.
Qed.

Definition pop_nibble (n: N)
: N * nibble
:= let a0 := last_bit n in
   let n1 := N.div2 n in
   let a1 := last_bit n1 in
   let n2 := N.div2 n1 in
   let a2 := last_bit n2 in
   let n3 := N.div2 n2 in
   let a3 := last_bit n3 in
   let n4 := N.div2 n3 in
     (n4, Nibble a3 a2 a1 a0).

Lemma push_nibble_then_pop (n: N) (nib: nibble):
  pop_nibble (push_nibble n nib) = (n, nib).
Proof.
  destruct nib as (a3, a2, a1, a0). unfold pop_nibble. cbn.
  repeat rewrite push_bit_then_shr1.
  now repeat rewrite last_of_push_bit. 
Qed.

Lemma pop_nibble_then_push (n: N):
  push_nibble (fst (pop_nibble n)) (snd (pop_nibble n)) = n.
Proof.
  destruct n. easy.
  unfold pop_nibble. unfold fst. unfold snd.
  unfold push_nibble.
  now repeat rewrite push_last_bit.
Qed.

Definition nibble_of_N (n: N)
: nibble
:= snd (pop_nibble n).

Lemma N_of_nibble_of_N (n: N) (B: (n < 16)%N):
  N_of_nibble (nibble_of_N n) = n.
Proof.
assert(P := pop_nibble_then_push n).
rewrite push_nibble_arith in P.
unfold nibble_of_N.
remember (N_of_nibble _) as k. clear Heqk.
remember (fst _) as z. clear Heqz.
lia.
Qed.

Definition pop_nibble_arith (a b: N) (B: (b < 16)%N):
  pop_nibble (16 * a + b) = (a, nibble_of_N b).
Proof.
enough (E: push_nibble a (nibble_of_N b) = (16 * a + b)%N).
{ rewrite<- E. apply push_nibble_then_pop. }
rewrite push_nibble_arith.
f_equal. apply N_of_nibble_of_N.
assumption.
Qed.

Definition pop_nibble_arith_small (b: N) (B: (b < 16)%N):
  pop_nibble b = (0%N, nibble_of_N b).
Proof.
rewrite<- (pop_nibble_arith _ _ B).
f_equal.
Qed.

Definition nibble_of_uint63 (i: int)
:= Nibble (0 <? (i land 8))%uint63
          (0 <? (i land 4))%uint63
          (0 <? (i land 2))%uint63
          (0 <? (i land 1))%uint63.

Definition uint63_of_nibble (n: nibble)
:= match n with
   | Nibble a8 a4 a2 a1 =>
       ((if a8 then 8%uint63 else 0%uint63)
         lor
        (if a4 then 4%uint63 else 0%uint63)
         lor
        (if a2 then 2%uint63 else 0%uint63)
         lor
        (if a1 then 1%uint63 else 0%uint63))%uint63
   end.

Lemma nibble_of_uint63_of_nibble (n: nibble):
  nibble_of_uint63 (uint63_of_nibble n) = n.
Proof.
destruct n as (a3, a2, a1, a0).
destruct a3; destruct a2; destruct a1; destruct a0; easy.
Qed.

(** A direct conversion from a native int to a hex digit via an if cascade. *)
Definition hex_digit_of_uint63 (i: int)
:= if (0 <? (i land 8))%uint63 then
     if (0 <? (i land 4))%uint63 then
       if (0 <? (i land 2))%uint63 then
         if (0 <? (i land 1))%uint63 then xF else xE
       else
         if (0 <? (i land 1))%uint63 then xD else xC
     else
       if (0 <? (i land 2))%uint63 then
         if (0 <? (i land 1))%uint63 then xB else xA
       else
         if (0 <? (i land 1))%uint63 then x9 else x8
   else
     if (0 <? (i land 4))%uint63 then
       if (0 <? (i land 2))%uint63 then
         if (0 <? (i land 1))%uint63 then x7 else x6
       else
         if (0 <? (i land 1))%uint63 then x5 else x4
     else
       if (0 <? (i land 2))%uint63 then
         if (0 <? (i land 1))%uint63 then x3 else x2
       else
         if (0 <? (i land 1))%uint63 then x1 else x0.

Lemma hex_digit_of_nibble_of_uint63 (i: int):
  hex_digit_of_nibble (nibble_of_uint63 i) = hex_digit_of_uint63 i.
Proof.
unfold hex_digit_of_nibble. unfold nibble_of_uint63. unfold hex_digit_of_uint63.
destruct (0 <? i land 8)%uint63;
  destruct (0 <? i land 4)%uint63;
  destruct (0 <? i land 2)%uint63;
  destruct (0 <? i land 1)%uint63; easy.
Qed.

Lemma nibble_of_uint63_of_N (n: N):
  nibble_of_uint63 (uint63_of_N n) = nibble_of_N n.
Proof.
unfold nibble_of_N. unfold pop_nibble. cbn.
remember (uint63_of_N n) as i.
unfold nibble_of_uint63.
repeat rewrite last_bit_odd.
repeat rewrite N.div2_spec.
repeat rewrite N.shiftr_shiftr.
repeat rewrite<- N.testbit_odd.
rewrite<- N.bit0_odd.
repeat rewrite uint63_testbit_N_low_digit; try lia.
unfold get_digit. rewrite<- Heqi. cbn.
f_equal; trivial.
Qed.

(***************************************************************************************)

(* This is basically the standard Ascii thing except that bits are ordered MSB-to-LSB. *)
Inductive byte := Byte (a7 a6 a5 a4 a3 a2 a1 a0: bool).

Definition low_nibble (b: byte)
: nibble
:= match b with
   | Byte _ _ _ _ a3 a2 a1 a0 => Nibble a3 a2 a1 a0
   end.

Definition high_nibble (b: byte)
: nibble
:= match b with
   | Byte a7 a6 a5 a4 _ _ _ _ => Nibble a7 a6 a5 a4
   end.

Definition byte_of_nibbles (high low: nibble)
: byte
:= match high with
   | Nibble a7 a6 a5 a4 =>
      match low with
      | Nibble a3 a2 a1 a0 =>
         Byte a7 a6 a5 a4 a3 a2 a1 a0
      end
   end.

Lemma low_nibble_ok (high low: nibble):
  low_nibble (byte_of_nibbles high low) = low.
Proof.
  destruct low. destruct high. easy.
Qed.

Lemma high_nibble_ok (high low: nibble):
  high_nibble (byte_of_nibbles high low) = high.
Proof.
  destruct low. destruct high. easy.
Qed.

Lemma byte_of_nibbles_ok (b: byte):
  byte_of_nibbles (high_nibble b) (low_nibble b) = b.
Proof.
  now destruct b.
Qed.

Definition byte_of_hex_digits (high low: hex_digit)
: byte
:= byte_of_nibbles (nibble_of_hex_digit high) (nibble_of_hex_digit low).

Definition hex_digits_of_byte (b: byte)
: hex_digit * hex_digit
:= (hex_digit_of_nibble (high_nibble b),
    hex_digit_of_nibble (low_nibble b)).

Definition N_of_byte (b: byte)
: N
:= let f (a: bool) := if a then xI else xO in
   match b with
   | Byte true a6 a5 a4 a3 a2 a1 a0 => Npos (f a0 (f a1 (f a2 (f a3 (f a4 (f a5 (f a6 xH)))))))
   | Byte false true a5 a4 a3 a2 a1 a0 => Npos (f a0 (f a1 (f a2 (f a3 (f a4 (f a5 xH))))))
   | Byte false false true a4 a3 a2 a1 a0 => Npos (f a0 (f a1 (f a2 (f a3 (f a4 xH)))))
   | Byte false false false true a3 a2 a1 a0 => Npos (f a0 (f a1 (f a2 (f a3 xH))))
   | Byte false false false false true a2 a1 a0 => Npos (f a0 (f a1 (f a2 xH)))
   | Byte false false false false false true a1 a0 => Npos (f a0 (f a1 xH))
   | Byte false false false false false false true a0 => Npos (f a0 xH)
   | Byte false false false false false false false true => Npos xH
   | Byte false false false false false false false false => N0
   end.

Definition pop_byte (n: N)
: N * byte
:= let (n1, x) := pop_nibble n in
   let (n2, y) := pop_nibble n1 in
     (n2, byte_of_nibbles y x).

Definition byte_of_N (n: N)
: byte
:= snd (pop_byte n).

Lemma byte_of_N_arith (high low: N)
                       (H16: (high < 16)%N)
                       (L16: (low < 16)%N):
  byte_of_N (16 * high + low) = byte_of_nibbles (nibble_of_N high) (nibble_of_N low).
Proof.
unfold byte_of_N. unfold pop_byte.
rewrite (pop_nibble_arith _ _ L16).
remember (nibble_of_N low) as nib. clear Heqnib low L16.
rewrite (pop_nibble_arith_small _ H16).
trivial.
Qed.

Lemma byte_of_N_of_byte (b: byte):
  byte_of_N (N_of_byte b) = b.
Proof.
destruct b as (a7, a6, a5, a4, a3, a2, a1, a0).
destruct a7; destruct a6; destruct a5; destruct a4;
destruct a3; destruct a2; destruct a1; destruct a0; trivial.
Qed.

Definition byte_of_int (i: int)
:= Byte (0 <? (i land 128))%uint63
        (0 <? (i land 64))%uint63
        (0 <? (i land 32))%uint63
        (0 <? (i land 16))%uint63
        (0 <? (i land 8))%uint63
        (0 <? (i land 4))%uint63
        (0 <? (i land 2))%uint63
        (0 <? (i land 1))%uint63.

Definition int_of_byte (b: byte)
:= match b with
   | Byte b7 b6 b5 b4 b3 b2 b1 b0 =>
     (let a7 := if b7 then 128 else 0 in
      let a6 := if b6 then  64 lor a7 else a7 in
      let a5 := if b5 then  32 lor a6 else a6 in
      let a4 := if b4 then  16 lor a5 else a5 in
      let a3 := if b3 then   8 lor a4 else a4 in
      let a2 := if b2 then   4 lor a3 else a3 in
      let a1 := if b1 then   2 lor a2 else a2 in
                if b0 then   1 lor a1 else a1)%uint63
   end.

Lemma byte_of_int_of_byte (b: byte):
  byte_of_int (int_of_byte b) = b.
Proof.
destruct b as (a7, a6, a5, a4, a3, a2, a1, a0).
destruct a7; destruct a6; destruct a5; destruct a4;
destruct a3; destruct a2; destruct a1; destruct a0; trivial.
Qed.

Fixpoint hex_of_bytes (b: list byte) (lower: bool)
: String.string
:= match b with
   | nil => String.EmptyString
   | (h :: t)%list =>
        let (hi, lo) := hex_digits_of_byte h in
          String.String (ascii_of_hex_digit hi lower)
                        (String.String (ascii_of_hex_digit lo lower)
                                       (hex_of_bytes t lower))
   end.

Definition byte_of_ascii (a: ascii)
:= let (b0, b1, b2, b3, b4, b5, b6, b7) := a in Byte b7 b6 b5 b4 b3 b2 b1 b0.

Fixpoint bytes_of_string (s: String.string)
: list byte
:= match s with
   | String.EmptyString => nil
   | String.String h t => byte_of_ascii h :: bytes_of_string t
   end.

(* TODO: to Str *)
Fixpoint string_forallb (f: ascii -> bool) (s: String.string)
: bool
:= match s with
   | String.EmptyString => true
   | String.String h t => f h && string_forallb f t
   end.

Lemma string_forallb_iff (f: ascii -> bool) (s: String.string):
  string_forallb f s = List.forallb f (String.list_ascii_of_string s).
Proof.
induction s; cbn. { trivial. }
f_equal. exact IHs.
Qed.

Definition is_hex_string (s: String.string)
: bool
:= Nat.even (String.length s) 
    &&
   string_forallb is_hex_digit s.

Fixpoint bytes_of_hex (s: String.string)
                       (ok: is_hex_string s = true)
: list byte.
Proof.
refine(match s as s' return s = s' -> _ with
       | String.EmptyString => fun _ => nil
       | String.String h String.EmptyString => fun E => _
       | String.String hi (String.String lo rest) => fun E =>
           (byte_of_hex_digits (hex_digit_of_ascii' hi _) (hex_digit_of_ascii' lo _)
            ::
            bytes_of_hex rest _)%list
       end eq_refl); 
  unfold is_hex_string in ok; unfold string_forallb in ok; subst; cbn in *;
  repeat (rewrite Bool.andb_true_iff in *); try easy.
fold string_forallb in ok. unfold is_hex_string.
rewrite Bool.andb_true_iff.
tauto.
Defined.

Lemma ascii_of_hex_digit_is_hex_digit (h: hex_digit) (lower: bool):
  is_hex_digit (ascii_of_hex_digit h lower) = true.
Proof.
unfold is_hex_digit. now rewrite hex_digit_of_ascii_of_hex_digit.
Qed.

Lemma hex_of_bytes_is_hex_string (b: list byte) (lower: bool)
: is_hex_string (hex_of_bytes b lower) = true.
Proof.
unfold is_hex_string. repeat (rewrite Bool.andb_true_iff).
split; induction b; try easy.
cbn. repeat rewrite ascii_of_hex_digit_is_hex_digit.
rewrite IHb. trivial.
Qed.

Lemma bytes_of_hex_of_bytes (b: list byte) (lower: bool):
  let hex := hex_of_bytes b lower in
  forall ok: is_hex_string hex = true,
    bytes_of_hex hex ok = b.
Proof.
induction b. { easy. }
cbn zeta in *. intro ok.
cbn. f_equal.
{
  unfold byte_of_hex_digits.
  repeat rewrite hex_digit_of_ascii_of_hex_digit'.
  repeat rewrite nibble_of_hex_digit_of_nibble.
  apply byte_of_nibbles_ok.
}
apply IHb.
Qed.
