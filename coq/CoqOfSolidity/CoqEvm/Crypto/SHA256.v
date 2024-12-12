(** This is a port of Go's crypto/sha256. *)

From Coq Require Import NArith ZArith Lia Uint63.
From Coq Require Import String HexString.

From CoqOfSolidity Require Import Nibble UInt64.
From CoqOfSolidity Require Tuplevector Vec8.

Definition output_size := 32.
Definition block_size := 64.


Definition vec8_add (a b: Vec8.t int)
:= let 'Vec8.Vec8 a0 a1 a2 a3 a4 a5 a6 a7 := a in
   let 'Vec8.Vec8 b0 b1 b2 b3 b4 b5 b6 b7 := b in
   (Vec8.Vec8 (a0 + b0) (a1 + b1) (a2 + b2) (a3 + b3)
              (a4 + b4) (a5 + b5) (a6 + b6) (a7 + b7))%uint63.

Definition init_hex: Vec8.t string
:= (Vec8.Vec8 "0x6A09E667"
              "0xBB67AE85"
              "0x3C6EF372"
              "0xA54FF53A"
              "0x510E527F"
              "0x9B05688C"
              "0x1F83D9AB"
              "0x5BE0CD19")%string.

Definition init := Vec8.map Uint63.of_Z (Vec8.map HexString.to_Z init_hex).

Definition K_hex: Vec8.t (Vec8.t string)
:= (Vec8.Vec8 (Vec8.Vec8 "0x428a2f98" "0x71374491" "0xb5c0fbcf" "0xe9b5dba5"
                         "0x3956c25b" "0x59f111f1" "0x923f82a4" "0xab1c5ed5")
              (Vec8.Vec8 "0xd807aa98" "0x12835b01" "0x243185be" "0x550c7dc3"
                         "0x72be5d74" "0x80deb1fe" "0x9bdc06a7" "0xc19bf174")
              (Vec8.Vec8 "0xe49b69c1" "0xefbe4786" "0x0fc19dc6" "0x240ca1cc"
                         "0x2de92c6f" "0x4a7484aa" "0x5cb0a9dc" "0x76f988da")
              (Vec8.Vec8 "0x983e5152" "0xa831c66d" "0xb00327c8" "0xbf597fc7"
                         "0xc6e00bf3" "0xd5a79147" "0x06ca6351" "0x14292967")
              (Vec8.Vec8 "0x27b70a85" "0x2e1b2138" "0x4d2c6dfc" "0x53380d13"
                         "0x650a7354" "0x766a0abb" "0x81c2c92e" "0x92722c85")
              (Vec8.Vec8 "0xa2bfe8a1" "0xa81a664b" "0xc24b8b70" "0xc76c51a3"
                         "0xd192e819" "0xd6990624" "0xf40e3585" "0x106aa070")
              (Vec8.Vec8 "0x19a4c116" "0x1e376c08" "0x2748774c" "0x34b0bcb5"
                         "0x391c0cb3" "0x4ed8aa4a" "0x5b9cca4f" "0x682e6ff3")
              (Vec8.Vec8 "0x748f82ee" "0x78a5636f" "0x84c87814" "0x8cc70208"
                         "0x90befffa" "0xa4506ceb" "0xbef9a3f7" "0xc67178f2"))%string.
Definition K := Vec8.map (Vec8.map (fun hex => Uint63.of_Z (HexString.to_Z hex))) K_hex.


(** Calculate the padding length given the data length. *)
Definition padding_length (data_length: N)
: N
:= let m := (data_length mod 64)%N in
   if (m <? 56)%N
      then (56 - m)%N
      else (64 + 56 - m)%N.

Lemma padding_length_nonzero (len: N):
  padding_length len <> 0%N.
Proof.
unfold padding_length.
remember (_ <? _)%N as c. symmetry in Heqc.
destruct c.
{ rewrite N.ltb_lt in Heqc. lia. }
rewrite N.ltb_ge in Heqc.
assert (F: (64 <> 0)%N) by discriminate.
assert (B := N.mod_upper_bound len 64 F).
lia.
Qed.

Lemma padding_length_ok (len: N):
  ((len + padding_length len) mod 64 = 56)%N.
Proof.
unfold padding_length.
assert (F: (64 <> 0)%N) by discriminate.
assert (B := N.mod_upper_bound len 64 F).
rewrite N.Div0.add_mod by discriminate.
rewrite N.Div0.add_mod_idemp_r by discriminate.
remember (len mod 64)%N as n.
remember (_ <? _)%N as c. symmetry in Heqc.
destruct c.
{
  rewrite N.ltb_lt in Heqc.
  replace (n + (56 - n))%N with 56%N. { easy. }
  lia.
}
rewrite N.ltb_ge in Heqc.
replace (n + (64 + 56 - n))%N with (64 + 56)%N. { easy. }
lia.
Qed.

Definition padding (len: N)
:= match N.to_nat len with
   | O => nil
   | S k => (byte_of_int 128 :: List.repeat (byte_of_int 0) k)%list
   end.

Lemma padding_ok (len: N):
  N.of_nat (List.length (padding len)) = len.
Proof.
unfold padding.
destruct len. { easy. }
rewrite positive_N_nat.
assert (P := Pos2Nat.is_pos p).
rewrite<- positive_nat_N.
remember (Pos.to_nat p) as n.
destruct n. { now apply Nat.lt_irrefl in P. }
cbn. now rewrite List.repeat_length.
Qed.

Definition pad (data: list byte)
: list byte
:= let len := N.of_nat (List.length data) in
   let len_in_bits := N.shiftl len 3 in
   data
    ++
   padding (padding_length len)
    ++
   Tuplevector.app_to_list
    (uint64_to_be_bytes 
      (uint64_of_Z_mod 
        (Z.of_N len_in_bits)): Tuplevector.t _ 8)
    nil.

Lemma pad_ok_mod (data: list byte):
  ((N.of_nat (List.length (pad data))) mod 64 = 0)%N.
Proof.
unfold pad.
repeat rewrite List.length_app.
rewrite Tuplevector.app_to_list_length.
repeat rewrite Nat2N.inj_add.
rewrite N.add_assoc.
rewrite N.Div0.add_mod by discriminate.
cbn.
remember (N.of_nat (List.length data)) as n.
rewrite padding_ok.
rewrite padding_length_ok.
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

Lemma can_gather_by_4 (n: nat):
  (n = n / 64 * 64  ->  n = (n / 64 * 16) * 4)%nat.
Proof.
now rewrite<- Nat.mul_assoc.
Qed.

Definition int_of_4_le_bytes (b: byte * byte * byte * byte)
: int
:= let '(b0, b1, b2, b3) := b in
   ((int_of_byte b3 << 24) lor 
    (int_of_byte b2 << 16) lor
    (int_of_byte b1 <<  8) lor
    (int_of_byte b0))%uint63.

Definition pad_and_gather_into_uint32s (data: list byte)
:= let padded := pad data in
   let PadOk  := pad_ok data in
   List.map int_of_4_le_bytes (* gather flips the tuples *)
            (Tuplevector.gather padded _ 4 (can_gather_by_4 _ PadOk)).

Lemma pad_and_gather_into_uint32s_length (data: list byte):
  let d := (List.length (pad data) / 64)%nat in
    (List.length (pad_and_gather_into_uint32s data) = d * 16)%nat.
Proof.
unfold pad_and_gather_into_uint32s.
rewrite List.length_map.
apply (Tuplevector.gather_length (pad data) (Datatypes.length (pad data) / 64 * 16) 4
     (can_gather_by_4 (Datatypes.length (pad data)) (pad_ok data))).
Qed.

Definition vec64 (T: Type) := Vec8.t (Vec8.t T).

Definition block_of_tuple (block: Tuplevector.t int 16)
: vec64 int
:= let z := (Vec8.Vec8 0 0 0 0 0 0 0 0)%uint63 in
   let '(bF, bE, bD, bC, bB, bA, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0) := block in
   Vec8.Vec8 (Vec8.Vec8 b0 b1 b2 b3 b4 b5 b6 b7) (Vec8.Vec8 b8 b9 bA bB bC bD bE bF) z z z z z z.

Definition blocks (data: list byte)
: list (vec64 int)
:= List.map block_of_tuple
            (Tuplevector.gather (pad_and_gather_into_uint32s data)
                                _ 16
                                (pad_and_gather_into_uint32s_length data)).

Definition vec64_get {T: Type} (v: vec64 T) (i: int)
:= Vec8.get (Vec8.get v (i >> 3)%uint63) i.

Definition vec64_set {T: Type} (v: vec64 T) (i: int) (new: T)
:= let hi := (i >> 3)%uint63 in
   Vec8.set v hi (Vec8.set (Vec8.get v hi) i new).

Definition uint32_mask := ((1 << 32) - 1)%uint63.

Definition shr (i sh: int) := ((i land uint32_mask) >> sh)%uint63.
Definition rot (i sh: int) := (shr i sh lor (i << (32 - sh)))%uint63.

Fixpoint calc_w_rec (n: nat) (start: vec64 int)
:= match n with
   | O => start
   | S k => (let w := calc_w_rec k start in
             let i := Uint63.of_Z (Z.of_nat n + 15)%Z in
             let v1 := vec64_get w (i -  2)%uint63 in
             let t1 := (rot v1 17) lxor (rot v1 19) lxor (shr v1 10) in
             let v2 := vec64_get w (i - 15)%uint63 in
             let t2 := (rot v2 7) lxor (rot v2 18) lxor (shr v2 3) in
             vec64_set w i (t1 + vec64_get w (i-7) + t2 + vec64_get w (i-16)))%uint63
   end.
Definition calc_w (w: vec64 int) := calc_w_rec 48 w.

Fixpoint do_block_rec (n: nat) (initial_state: Vec8.t int) (w_after_calc: vec64 int)
: Vec8.t int
:= match n with
   | O => initial_state
   | S k => let state := do_block_rec k initial_state w_after_calc in
            let i := Uint63.of_Z (Z.of_nat k) in
            let 'Vec8.Vec8 a b c d e f g h := state in
            (let t1 := h + ((rot e 6) lxor (rot e 11) lxor (rot e 25)) 
                         + ((e land f) lxor ((e lxor uint32_mask) land g))
                         + vec64_get K i
                         + vec64_get w_after_calc i in
             let t2 := ((rot a 2) lxor (rot a 13) lxor (rot a 22))
                         + ((a land b) lxor (a land c) lxor (b land c)) in
             Vec8.Vec8 (t1 + t2) a b c (d + t1) e f g)%uint63
   end.
Definition do_block (state: Vec8.t int) (w: vec64 int)
:= do_block_rec 64 state w.

Definition absorb_block (state: Vec8.t int) (w: vec64 int)
:= vec8_add state (do_block state (calc_w w)).

Definition absorb (data: list byte)
:= List.fold_left absorb_block (blocks data) init.

Definition be_4_bytes_of_int (i: int)
:= (byte_of_int (i >> 24)
 :: byte_of_int (i >> 16)
 :: byte_of_int (i >> 8)
 :: byte_of_int i :: nil)%list%uint63.

Definition squeeze (state: Vec8.t int)
:= List.concat (List.map be_4_bytes_of_int (Vec8.to_list state)).

Definition sha256 (data: list byte)
: list byte
:= squeeze (absorb data).

Definition sha256_of_string (s: String.string)
:= sha256 (bytes_of_string s).

Definition sha256_hex (data: list byte)
: String.string
:= hex_of_bytes (sha256 data) true.

Definition sha256_hex_of_string (s: String.string)
: String.string
:= hex_of_bytes (sha256_of_string s) true.

(* This test is from Go's sha256_test.go. *)
Example smoke_test:
  sha256_hex_of_string
    "For every action there is an equal and opposite government program."
   =
  "23b1018cd81db1d67983c5f7417c44da9deb582459e378d7a068552ea649dc9f"%string.
Proof. trivial. Qed.