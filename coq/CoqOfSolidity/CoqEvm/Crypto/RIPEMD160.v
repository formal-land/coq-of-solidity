From Coq Require Import NArith ZArith Uint63 String.
From Coq Require HexString.

From CoqOfSolidity Require Import Nibble.
From CoqOfSolidity Require Vec16.
From CoqOfSolidity Require SHA256.


(** This is a port of Go's golang.org/x/crypto/ripemd160. *)
(** See also:
  https://homes.esat.kuleuven.be/~bosselae/ripemd160.html
   and
  https://en.bitcoin.it/wiki/RIPEMD-160
*)


Local Open Scope int63_scope.
Local Open Scope string_scope.

(* This is almost the same as SHA256 padding but the length is little-endian. *)
Definition pad (data: list byte)
: list byte
:= let len := N.of_nat (List.length data) in
   let len_in_bits := N.shiftl len 3 in
   data
    ++
   SHA256.padding (SHA256.padding_length len)
    ++
   Tuplevector.app_to_list
    (UInt64.uint64_to_le_bytes 
      (UInt64.uint64_of_Z_mod 
        (Z.of_N len_in_bits)): Tuplevector.t _ 8)
    nil.

(* This is exactly the same as its SHA256 counterpart. *)
Lemma pad_ok_mod (data: list byte):
  ((N.of_nat (List.length (pad data))) mod 64 = 0)%N.
Proof.
unfold pad.
repeat rewrite List.app_length.
rewrite Tuplevector.app_to_list_length.
repeat rewrite Nat2N.inj_add.
rewrite N.add_assoc.
rewrite N.Div0.add_mod by discriminate.
cbn.
remember (N.of_nat (List.length data)) as n.
rewrite SHA256.padding_ok.
rewrite SHA256.padding_length_ok.
trivial.
Qed.

Lemma pad_ok (data: list byte):
  let d := (List.length (pad data) / 64)%nat in
    (List.length (pad data) = d * 64)%nat.
Proof.
apply Nat2N.inj.
assert (M := pad_ok_mod data).
remember (List.length  _) as len. clear Heqlen.
match goal with |- ?lhs = ?rhs => rewrite<- (N.add_0_r rhs) end.
rewrite<- M.
rewrite Nat.mul_comm.
rewrite Nat2N.inj_mul.
rewrite Arith2.Nat2N_inj_div.
apply N.div_mod.
subst. discriminate.
Qed.

Definition int_of_4_be_bytes (b: byte * byte * byte * byte)
: int
:= let '(b3, b2, b1, b0) := b in
   ((int_of_byte b3 << 24) lor 
    (int_of_byte b2 << 16) lor
    (int_of_byte b1 <<  8) lor
    (int_of_byte b0))%uint63.

Definition pad_and_gather_into_uint32s (data: list byte)
:= let padded := pad data in
   let PadOk  := pad_ok data in
   List.map int_of_4_be_bytes (* gather flips the tuples *)
            (Tuplevector.gather padded _ 4 (SHA256.can_gather_by_4 _ PadOk)).

Lemma pad_and_gather_into_uint32s_length (data: list byte):
  let d := (List.length (pad data) / 64)%nat in
    (List.length (pad_and_gather_into_uint32s data) = d * 16)%nat.
Proof.
unfold pad_and_gather_into_uint32s.
rewrite List.map_length.
apply (Tuplevector.gather_length (pad data) (Datatypes.length (pad data) / 64 * 16) 4
     (SHA256.can_gather_by_4 (Datatypes.length (pad data)) (pad_ok data))).
Qed.

Definition block_of_tuple (block: Tuplevector.t int 16)
: Vec16.t int
:= let '(bF, bE, bD, bC, bB, bA, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0) := block in
   Vec16.Vec16 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 bA bB bC bD bE bF.

Definition blocks (data: list byte)
: list (Vec16.t int)
:= List.map block_of_tuple
            (Tuplevector.gather (pad_and_gather_into_uint32s data)
                                _ 16
                                (pad_and_gather_into_uint32s_length data)).

(*************************************************************************)

Inductive vec5 (T: Type)
:= Vec5 (a b c d e: T).
Arguments Vec5 {_}.

Definition vec5_to_list {T: Type} (v: vec5 T)
: list T
:= let 'Vec5 a b c d e := v in
   a :: b :: c :: d :: e :: nil.

Definition vec5_map {A B: Type} (f: A -> B) (v: vec5 A)
: vec5 B
:= let 'Vec5 a b c d e := v in
   Vec5 (f a) (f b) (f c) (f d) (f e).

(* ripemd160block.go *)
Local Definition _n1: Vec16.t int := Vec16.Vec16 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15.
Local Definition _n2: Vec16.t int := Vec16.Vec16 7 4 13 1 10 6 15 3 12 0 9 5 2 14 11 8.
Local Definition _n3: Vec16.t int := Vec16.Vec16 3 10 14 4 9 15 8 1 2 7 0 6 13 11 5 12.
Local Definition _n4: Vec16.t int := Vec16.Vec16 1 9 11 10 0 8 12 4 13 3 7 15 14 5 6 2.
Local Definition _n5: Vec16.t int := Vec16.Vec16 4 0 5 9 7 12 2 10 14 1 3 8 11 6 15 13.

Local Definition _r1: Vec16.t int := Vec16.Vec16 11 14 15 12 5 8 7 9 11 13 14 15 6 7 9 8.
Local Definition _r2: Vec16.t int := Vec16.Vec16 7 6 8 13 11 9 7 15 7 12 15 9 11 7 13 12.
Local Definition _r3: Vec16.t int := Vec16.Vec16 11 13 6 7 14 9 13 15 14 8 13 6 5 12 7 5.
Local Definition _r4: Vec16.t int := Vec16.Vec16 11 12 14 15 14 15 9 8 9 14 5 6 8 6 5 12.
Local Definition _r5: Vec16.t int := Vec16.Vec16 9 15 5 11 6 8 13 12 5 12 13 14 11 8 5 6.

Local Definition n_1: Vec16.t int := Vec16.Vec16 5 14 7 0 9 2 11 4 13 6 15 8 1 10 3 12.
Local Definition n_2: Vec16.t int := Vec16.Vec16 6 11 3 7 0 13 5 10 14 15 8 12 4 9 1 2.
Local Definition n_3: Vec16.t int := Vec16.Vec16 15 5 1 3 7 14 6 9 11 8 12 2 10 0 4 13.
Local Definition n_4: Vec16.t int := Vec16.Vec16 8 6 4 1 3 11 15 0 5 12 2 13 9 7 10 14.
Local Definition n_5: Vec16.t int := Vec16.Vec16 12 15 10 4 1 5 8 7 6 2 13 14 0 3 9 11.

Local Definition r_1: Vec16.t int := Vec16.Vec16 8 9 9 11 13 15 15 5 7 7 8 11 14 14 12 6.
Local Definition r_2: Vec16.t int := Vec16.Vec16 9 13 15 7 12 8 9 11 7 7 12 7 6 15 13 11.
Local Definition r_3: Vec16.t int := Vec16.Vec16 9 7 15 11 8 6 6 14 12 13 5 14 13 13 7 5.
Local Definition r_4: Vec16.t int := Vec16.Vec16 15 5 8 11 14 14 6 14 6 9 12 9 12 5 15 8.
Local Definition r_5: Vec16.t int := Vec16.Vec16 8 5 12 9 12 5 14 6 8 13 6 5 15 13 11 11.

Definition uint32_mask: int := (1 << 32) - 1.
Definition uint32_not (i: int) := (uint32_mask lxor i)%uint63.

(* Rotate an int left as if it was uint32. *)
Definition rot x k := ((x << k) lor ((x land uint32_mask) >> (32 - k)))%uint63.

Definition f1 (x y z: int): int := x lxor y lxor z.
Definition f2 (x y z: int): int := (x land y) lor (uint32_not x land z).
Definition f3 (x y z: int): int := (x lor uint32_not y) lxor z.
Definition f4 (x y z: int): int := (x land z) lor (y land uint32_not z).
Definition f5 (x y z: int): int := x lxor (y lor uint32_not z).

Definition round (n r: Vec16.t int) (const: int) (f: int -> int -> int -> int)
                  (x: Vec16.t int) (s: vec5 int) (i: int)
: vec5 int
:= let 'Vec5 a b c d e := s in
   let alpha := (a 
              + f b c d
              + Vec16.get_by_int x (Vec16.get_by_int n i)
              + const)%uint63 in
   let alpha' := (rot alpha (Vec16.get_by_int r i) + e)%uint63 in
   let beta := rot c 10 in
   Vec5 e alpha' b beta d.

Definition int_of_hex (s: string) := Uint63.of_Z (HexString.to_Z s).

Definition iota: Vec16.t int := Vec16.Vec16 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15.

Definition round1a x := Vec16.fold_left (round _n1 _r1 (int_of_hex        "0x0") f1 x) iota.
Definition round2a x := Vec16.fold_left (round _n2 _r2 (int_of_hex "0x5a827999") f2 x) iota.
Definition round3a x := Vec16.fold_left (round _n3 _r3 (int_of_hex "0x6ed9eba1") f3 x) iota.
Definition round4a x := Vec16.fold_left (round _n4 _r4 (int_of_hex "0x8f1bbcdc") f4 x) iota.
Definition round5a x := Vec16.fold_left (round _n5 _r5 (int_of_hex "0xa953fd4e") f5 x) iota.
Definition round1b x := Vec16.fold_left (round n_1 r_1 (int_of_hex "0x50a28be6") f5 x) iota.
Definition round2b x := Vec16.fold_left (round n_2 r_2 (int_of_hex "0x5c4dd124") f4 x) iota.
Definition round3b x := Vec16.fold_left (round n_3 r_3 (int_of_hex "0x6d703ef3") f3 x) iota.
Definition round4b x := Vec16.fold_left (round n_4 r_4 (int_of_hex "0x7a6d76e9") f2 x) iota.
Definition round5b x := Vec16.fold_left (round n_5 r_5 (int_of_hex        "0x0") f1 x) iota.

Local Definition init_hex: vec5 string
:= Vec5 "0x67452301"
        "0xefcdab89"
        "0x98badcfe"
        "0x10325476"
        "0xc3d2e1f0".
Local Definition init: vec5 int := vec5_map int_of_hex init_hex.

Definition rounds_a x s := round5a x (round4a x (round3a x (round2a x (round1a x s)))).
Definition rounds_b x s := round5b x (round4b x (round3b x (round2b x (round1b x s)))).

Definition absorb_block (s: vec5 int) (x: Vec16.t int)
: vec5 int
:= let 'Vec5 s0 s1 s2 s3 s4 := s in
   let 'Vec5 a0 a1 a2 a3 a4 := rounds_a x s in
   let 'Vec5 b0 b1 b2 b3 b4 := rounds_b x s in
   Vec5 (s1 + a2 + b3)%uint63
        (s2 + a3 + b4)%uint63
        (s3 + a4 + b0)%uint63
        (s4 + a0 + b1)%uint63
        (s0 + a1 + b2)%uint63.

Definition absorb (data: list byte)
:= List.fold_left absorb_block (blocks data) init.

Definition le_4_bytes_of_int (i: int)
:= (byte_of_int i
 :: byte_of_int (i >> 8)
 :: byte_of_int (i >> 16)
 :: byte_of_int (i >> 24) :: nil)%list%uint63.

Definition squeeze (state: vec5 int)
:= List.concat (List.map le_4_bytes_of_int (vec5_to_list state)).

Definition ripemd160 (data: list byte)
: list byte
:= squeeze (absorb data).

Definition ripemd160_of_string (s: String.string)
:= ripemd160 (bytes_of_string s).

Definition ripemd160_hex (data: list byte)
: String.string
:= hex_of_bytes (ripemd160 data) true.

Definition ripemd160_hex_of_string (s: String.string)
: String.string
:= hex_of_bytes (ripemd160_of_string s) true.

(* From https://homes.esat.kuleuven.be/~bosselae/ripemd160.html *)
Example smoke_test:
  ripemd160_hex_of_string
    "abcdefghijklmnopqrstuvwxyz"
   =
  "f71c27109c692c1b56bbdceb5b9d2865b3708dbc"%string.
Proof. trivial. Qed.