(**
  This is Keccak-256 and SHA3-256 ported from Go's 
    golang.org/x/crypto/sha3
 *)

From Coq Require Import List.
From Coq Require HexString.
From Coq Require Import String.
From Coq Require Import NArith ZArith Lia.
From Coq Require Import Uint63.

From CoqOfSolidity Require UInt64 Tuplevector.
From CoqOfSolidity Require Import Nibble.

Local Open Scope string_scope.

Definition rc_hex: list string
:= "0x0000000000000001"
:: "0x0000000000008082"
:: "0x800000000000808A"
:: "0x8000000080008000"
:: "0x000000000000808B"
:: "0x0000000080000001"
:: "0x8000000080008081"
:: "0x8000000000008009"
:: "0x000000000000008A"
:: "0x0000000000000088"
:: "0x0000000080008009"
:: "0x000000008000000A"
:: "0x000000008000808B"
:: "0x800000000000008B"
:: "0x8000000000008089"
:: "0x8000000000008003"
:: "0x8000000000008002"
:: "0x8000000000000080"
:: "0x000000000000800A"
:: "0x800000008000000A"
:: "0x8000000080008081"
:: "0x8000000000008080"
:: "0x0000000080000001"
:: "0x8000000080008008"
:: nil.

Definition rc := map UInt64.uint64_of_Z_mod (map HexString.to_Z rc_hex).
Lemma rc_ok:
  map UInt64.Z_of_uint64 rc = map HexString.to_Z rc_hex.
Proof. trivial. Qed.

Definition rc_quads_backwards := Tuplevector.gather rc 6 4 eq_refl.

Inductive vec25 (T: Type)
:= Vec25 (a0  a1  a2  a3  a4
          a5  a6  a7  a8  a9
          a10 a11 a12 a13 a14
          a15 a16 a17 a18 a19
          a20 a21 a22 a23 a24: T).
Arguments Vec25 {_}.

Definition vec25_fill {T: Type} (x: T)
:= Vec25 x x x x x
         x x x x x
         x x x x x
         x x x x x
         x x x x x.

Definition uint64 := UInt64.uint64.

Definition vec25_zeros := vec25_fill (UInt64.uint64_0).

Section Permutation.

Local Notation "x ^ y"  := (UInt64.bitwise_xor x y).

Definition vec25_xor_tuple17_backwards (a: vec25 uint64) (b: Tuplevector.t uint64 17)
:= match a with
   | Vec25 a0  a1  a2  a3  a4
           a5  a6  a7  a8  a9
          a10 a11 a12 a13 a14
          a15 a16 a17 a18 a19
          a20 a21 a22 a23 a24 =>
      match b with
      | (b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0) =>
             Vec25 ( a0 ^  b0)  (a1 ^  b1)  (a2 ^  b2)  (a3 ^  b3)  (a4 ^  b4)
                   ( a5 ^  b5)  (a6 ^  b6)  (a7 ^  b7)  (a8 ^  b8)  (a9 ^  b9)
                   (a10 ^ b10) (a11 ^ b11) (a12 ^ b12) (a13 ^ b13) (a14 ^ b14)
                   (a15 ^ b15) (a16 ^ b16)  a17         a18         a19
                    a20         a21         a22         a23         a24
      end
   end.

Local Notation "x << y" := (UInt64.shl_uint63 x y).
Local Notation "x >> y" := (UInt64.shr_uint63 x y).
Local Notation "x | y"  := (UInt64.bitwise_or x y)  (at level 30). (* dangerous! messes up match! *)
Local Notation "x & y"  := (UInt64.bitwise_and x y) (at level 30).
Local Notation "~ x"  := (UInt64.bitwise_not x).

Definition rot x k := ((x << k) | (x >> (64 - k)%uint63)).

Definition round (rc: uint64) (a: vec25 uint64) (b: vec25 uint64)
: vec25 uint64
:= match a, b with
   | Vec25 a0  a1  a2  a3  a4
           a5  a6  a7  a8  a9
           a10 a11 a12 a13 a14
           a15 a16 a17 a18 a19
           a20 a21 a22 a23 a24,
     Vec25 b0  b1  b2  b3  b4
           b5  b6  b7  b8  b9
           b10 b11 b12 b13 b14
           b15 b16 b17 b18 b19
           b20 b21 b22 b23 b24 =>
 
      let bc0 := a0 ^ a5 ^ a10 ^ a15 ^ a20 in
      let bc1 := a1 ^ a6 ^ a11 ^ a16 ^ a21 in
      let bc2 := a2 ^ a7 ^ a12 ^ a17 ^ a22 in
      let bc3 := a3 ^ a8 ^ a13 ^ a18 ^ a23 in
      let bc4 := a4 ^ a9 ^ a14 ^ a19 ^ a24 in

      let d0 := bc4 ^ rot bc1 1%uint63 in
      let d1 := bc0 ^ rot bc2 1%uint63 in
      let d2 := bc1 ^ rot bc3 1%uint63 in
      let d3 := bc2 ^ rot bc4 1%uint63 in
      let d4 := bc3 ^ rot bc0 1%uint63 in

      let p0 := b0 ^ d0 in
      let p1 := rot (b1 ^ d1) 44%uint63 in
      let p2 := rot (b2 ^ d2) 43%uint63 in
      let p3 := rot (b3 ^ d3) 21%uint63 in
      let p4 := rot (b4 ^ d4) 14%uint63 in

      let z0  := p0 ^ (p2 & ~ p1) ^ rc in
      let z1  := p1 ^ (p3 & ~ p2) in
      let z2  := p2 ^ (p4 & ~ p3) in
      let z3  := p3 ^ (p0 & ~ p4) in
      let z4  := p4 ^ (p1 & ~ p0) in

      let q2 := rot (b5 ^ d0)  3%uint63 in
      let q3 := rot (b6 ^ d1) 45%uint63 in
      let q4 := rot (b7 ^ d2) 61%uint63 in
      let q0 := rot (b8 ^ d3) 28%uint63 in
      let q1 := rot (b9 ^ d4) 20%uint63 in

      let z5  := q0 ^ (q2 & ~ q1) in
      let z6  := q1 ^ (q3 & ~ q2) in
      let z7  := q2 ^ (q4 & ~ q3) in
      let z8  := q3 ^ (q0 & ~ q4) in
      let z9  := q4 ^ (q1 & ~ q0) in

      let r4 := rot (b10 ^ d0) 18%uint63 in
      let r0 := rot (b11 ^ d1)  1%uint63 in
      let r1 := rot (b12 ^ d2)  6%uint63 in
      let r2 := rot (b13 ^ d3) 25%uint63 in
      let r3 := rot (b14 ^ d4)  8%uint63 in

      let z10 := r0 ^ (r2 & ~ r1) in
      let z11 := r1 ^ (r3 & ~ r2) in
      let z12 := r2 ^ (r4 & ~ r3) in
      let z13 := r3 ^ (r0 & ~ r4) in
      let z14 := r4 ^ (r1 & ~ r0) in

      let s1 := rot (b15 ^ d0) 36%uint63 in
      let s2 := rot (b16 ^ d1) 10%uint63 in
      let s3 := rot (b17 ^ d2) 15%uint63 in
      let s4 := rot (b18 ^ d3) 56%uint63 in
      let s0 := rot (b19 ^ d4) 27%uint63 in

      let z15 := s0 ^ (s2 & ~ s1) in
      let z16 := s1 ^ (s3 & ~ s2) in
      let z17 := s2 ^ (s4 & ~ s3) in
      let z18 := s3 ^ (s0 & ~ s4) in
      let z19 := s4 ^ (s1 & ~ s0) in

      let t3 := rot (b20 ^ d0) 41%uint63 in
      let t4 := rot (b21 ^ d1)  2%uint63 in
      let t0 := rot (b22 ^ d2) 62%uint63 in
      let t1 := rot (b23 ^ d3) 55%uint63 in
      let t2 := rot (b24 ^ d4) 39%uint63 in

      let z20 := t0 ^ (t2 & ~ t1) in
      let z21 := t1 ^ (t3 & ~ t2) in
      let z22 := t2 ^ (t4 & ~ t3) in
      let z23 := t3 ^ (t0 & ~ t4) in
      let z24 := t4 ^ (t1 & ~ t0) in

      Vec25 z0  z1  z2  z3  z4
            z5  z6  z7  z8  z9
            z10 z11 z12 z13 z14
            z15 z16 z17 z18 z19
            z20 z21 z22 z23 z24
   end.

Definition permute1 {T} (a: vec25 T)
:= match a with
   | Vec25 a0  a1  a2  a3  a4
           a5  a6  a7  a8  a9
           a10 a11 a12 a13 a14
           a15 a16 a17 a18 a19
           a20 a21 a22 a23 a24 =>
     Vec25 a0  a11 a22 a8  a19
           a15 a1  a12 a23 a9
           a5  a16 a2  a13 a24
           a20 a6  a17 a3  a14
           a10 a21 a7  a18 a4
   end.
Definition permute2 {T} (a: vec25 T)
:= match a with
   | Vec25 a0  a1  a2  a3  a4
           a5  a6  a7  a8  a9
           a10 a11 a12 a13 a14
           a15 a16 a17 a18 a19
           a20 a21 a22 a23 a24 =>
     Vec25 a0  a16 a7  a23 a14
           a20 a11 a2  a18 a9
           a15 a6  a22 a13 a4
           a10 a1  a17 a8  a24
           a5  a21 a12 a3  a19
   end.
Definition permute3 {T} (a: vec25 T)
:= match a with
   | Vec25 a0  a1  a2  a3  a4
           a5  a6  a7  a8  a9
           a10 a11 a12 a13 a14
           a15 a16 a17 a18 a19
           a20 a21 a22 a23 a24 =>
     Vec25 a0  a6  a12 a18 a24
           a10 a16 a22 a3  a9
           a20 a1  a7  a13 a19
           a5  a11 a17 a23 a4
           a15 a21 a2  a8  a14
   end.
Lemma permute1_of_permute3 {T} (a: vec25 T):
  permute1 (permute3 a) = a.
Proof. now destruct a. Qed.
Lemma permute3_of_permute1 {T} (a: vec25 T):
  permute3 (permute1 a) = a.
Proof. now destruct a. Qed.
Lemma permute2_of_permute2 {T} (a: vec25 T):
  permute2 (permute2 a) = a.
Proof. now destruct a. Qed.


Definition quad_round (a: vec25 uint64) (rcs: Tuplevector.t uint64 4)
: vec25 uint64
:= match rcs with
   | (rc4, rc3, rc2, rc1) =>
        let a1 := permute1 (round rc1 a  (permute3 a))  in
        let a2 := permute2 (round rc2 a1 (permute2 a1)) in
        let a3 := permute3 (round rc3 a2 (permute1 a2)) in
        round rc4 a3 a3
   end.

Definition F1600 := fold_left quad_round rc_quads_backwards.

End Permutation.

(* Create padding of the given length (of the padding, not of the data). *)
Definition padding (len: positive) (start: int) (* start is 1 for Ethereum's Keccak, otherwise 6 *)
: list byte
:= match len with
   | 1%positive => byte_of_int (128 lor start)%uint63 :: nil
   | _ => (byte_of_int start) :: repeat (byte_of_int 0) (N.to_nat (N.pos len - 2)) ++ 
            byte_of_int 128 :: nil
   end.

(* The padding has the requested length *)
Lemma padding_ok (len: positive) (start: int):
  List.length (padding len start) = Pos.to_nat len.
Proof.
unfold padding.
remember (byte_of_int start :: 
          repeat (byte_of_int 0) (N.to_nat (N.pos len - 2)) ++
          byte_of_int 128 ::
          nil) as l.
assert (cons_length: forall {T} h (t: list T), List.length (h :: t) = S (List.length t)) by easy.
destruct len; cbn; subst;
  repeat (rewrite List.app_length || rewrite List.repeat_length || rewrite cons_length);
  replace (List.length (@nil byte)) with 0 by trivial; lia.
Qed.

(** Calculate the padding length given the data length. *)
Definition padding_length (data_length: N) (rate: positive)
: positive
:= match (data_length mod N.pos rate)%N with
   | 0%N => rate
   | Npos p => rate - p
   end.

Lemma padding_length_ok (data_length: N) (rate: positive):
  ((data_length + N.pos (padding_length data_length rate)) mod N.pos rate = 0)%N.
Proof.
unfold padding_length.
remember (data_length mod N.pos rate)%N as m.
destruct m; rewrite N.Div0.add_mod by discriminate; rewrite<- Heqm.
{ rewrite N.add_0_l. rewrite N.Div0.mod_same by discriminate. apply N.Div0.mod_0_l. }
assert(L: (N.pos p < N.pos rate)%N).
{ rewrite Heqm. apply N.mod_upper_bound. discriminate. }
replace (N.pos (rate - p) mod N.pos rate)%N with (N.pos (rate - p)).
2:{ symmetry. apply N.mod_small. lia. }
replace (N.pos p + N.pos (rate - p))%N with (N.pos rate) by lia.
apply N.Div0.mod_same.
Qed.

Definition pad (unpadded_data: list byte) (rate: positive) (start: int)
: list byte
:= (unpadded_data ++ padding (padding_length (N.of_nat (List.length unpadded_data)) rate) start)%list.

Lemma pad_ok_mod (data: list byte) (rate: positive) (start: int):
  (N.of_nat (List.length (pad data rate start)) mod N.pos rate = 0)%N.
Proof.
unfold pad. rewrite List.app_length. rewrite Nat2N.inj_add.
remember (List.length data) as n. rewrite padding_ok.
rewrite positive_nat_N. rewrite padding_length_ok.
trivial.
Qed.

Lemma pad_ok (data: list byte) (rate: positive) (start: int):
  let d := List.length (pad data rate start) / Pos.to_nat rate in
    List.length (pad data rate start) = d * Pos.to_nat rate.
Proof.
apply Nat2N.inj.
assert (M := pad_ok_mod data rate start).
remember (List.length  _) as len. clear Heqlen.
match goal with |- ?lhs = ?rhs => rewrite<- (N.add_0_r rhs) end.
rewrite<- M.
rewrite Nat.mul_comm.
rewrite Nat2N.inj_mul.
rewrite Arith2.Nat2N_inj_div.
remember (Pos.to_nat rate) as r.
assert (R: N.pos rate = N.of_nat r).
{ subst. symmetry. apply positive_nat_N. }
rewrite R. rewrite R in M.
apply N.div_mod.
subst. assert(P := Pos2Nat.is_pos rate).
destruct (Pos.to_nat rate).
{ now apply Nat.lt_irrefl in P. }
discriminate.
Qed.

Local Lemma can_gather_by_8 (n: nat):
  n = n / 136 * 136  ->  n = (n / 136 * 17) * 8.
Proof.
now rewrite<- Nat.mul_assoc.
Qed.

Definition pad_by_136_and_gather_into_uint64s (data: list byte) (padding_start: int)
:= let padded := pad data 136%positive padding_start in
   let PadOk  := pad_ok data 136%positive padding_start in
   List.map UInt64.uint64_of_be_bytes
            (Tuplevector.gather padded _ 8 (can_gather_by_8 _ PadOk)).

Lemma pad_by_136_and_gather_into_uint64s_length (data: list byte) (s: int):
  List.length (pad_by_136_and_gather_into_uint64s data s) 
   =
  (List.length (pad data 136 s)) / 136 * 17.
Proof.
unfold pad_by_136_and_gather_into_uint64s.
rewrite List.map_length.
apply (Tuplevector.gather_length (pad data 136 s)
             (Datatypes.length (pad data 136 s) / 136 * 17) 8
             (can_gather_by_8 (Datatypes.length (pad data 136 s)) (pad_ok data 136 s))).
Qed.

Definition blocks (data: list byte) (padding_start: int)
:= Tuplevector.gather (pad_by_136_and_gather_into_uint64s data padding_start)
                      _ 17
                      (pad_by_136_and_gather_into_uint64s_length data padding_start).

Definition absorb (data: list byte) (padding_start: int)
:= fold_left (fun state block => F1600 (vec25_xor_tuple17_backwards state block))
             (blocks data padding_start)
             vec25_zeros.

Definition squeeze_256 (a: vec25 uint64) 
:= match a with
   | Vec25 a0  a1  a2  a3  _
           _   _   _   _   _
           _   _   _   _   _
           _   _   _   _   _
           _   _   _   _   _ =>
      let eights: list (Tuplevector.t byte 8)
                := map UInt64.uint64_to_le_bytes (a0 :: a1 :: a2 :: a3 :: nil)
      in fold_right Tuplevector.app_to_list nil eights
   end.

Definition keccak_256 (data: list byte): list byte := squeeze_256 (absorb data 1).
Definition sha3_256   (data: list byte): list byte := squeeze_256 (absorb data 6).

Definition keccak_256_of_string (s: String.string)
:= keccak_256 (bytes_of_string s).
Definition sha3_256_of_string (s: String.string)
:= sha3_256 (bytes_of_string s).

Definition keccak_256_hex (data: list byte)
: String.string
:= hex_of_bytes (keccak_256 data) true.
Definition sha3_256_hex (data: list byte)
: String.string
:= hex_of_bytes (sha3_256 data) true.

Definition keccak_256_hex_of_string (s: String.string)
: String.string
:= hex_of_bytes (keccak_256_of_string s) true.
Definition sha3_256_hex_of_string (s: String.string)
: String.string
:= hex_of_bytes (sha3_256_of_string s) true.

(* This test is from Go's sha3_test.go. *)
Example keccak_256_smoke_test:
  keccak_256_hex_of_string "abc"
   =
  "4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45".
Proof. trivial. Qed.

(* A byte-long test from XKCP's ShortMsgKAT_SHA3-256.txt. *)
Example sha3_256_test_CC:
  sha3_256_hex (byte_of_N (HexString.to_N "0xCC") :: nil) 
   = 
  "677035391cd3701293d385f037ba32796252bb7ce180b00b582dd9b20aaad7f0".
Proof. trivial. Qed.
