From Coq Require Import List.
From Coq Require HexString.
From Coq Require Import String.
From Coq Require Import NArith ZArith Lia.
From Coq Require Import Uint63.

From CoqOfSolidity Require UInt64 Tuplevector Vec8 Vec16.
From CoqOfSolidity Require Import Nibble.


(** This is a clean room implementation of the F function of BLAKE2b.
     https://github.com/ethereum/EIPs/blob/master/EIPS/eip-152.md
     https://tools.ietf.org/html/rfc7693 *)

Local Open Scope string_scope.

Definition iv_hex: Vec8.t string
:= Vec8.Vec8 "0x6a09e667f3bcc908"
             "0xbb67ae8584caa73b"
             "0x3c6ef372fe94f82b"
             "0xa54ff53a5f1d36f1"
             "0x510e527fade682d1"
             "0x9b05688c2b3e6c1f"
             "0x1f83d9abfb41bd6b"
             "0x5be0cd19137e2179".
Definition iv := Vec8.map UInt64.uint64_of_Z_mod (Vec8.map HexString.to_Z iv_hex).
Lemma iv_ok:
  Vec8.map UInt64.Z_of_uint64 iv = Vec8.map HexString.to_Z iv_hex.
Proof. trivial. Qed.


(* 3.1.  Mixing Function G *)
Local Notation "x ^ y"  := (UInt64.bitwise_xor x y).
Section MixingFunctionG.

Local Notation "x << y" := (UInt64.shl_uint63 x y).
Local Notation "x >> y" := (UInt64.shr_uint63 x y).
Local Notation "x | y"  := (UInt64.bitwise_or x y)  (at level 30). (* dangerous! messes up match! *)
Local Notation "x & y"  := (UInt64.bitwise_and x y) (at level 30).
Local Notation "x + y"  := (UInt64.add x y).
Local Notation "~ x"  := (UInt64.bitwise_not x).
Definition rot x k := ((x >> k) | (x << (64 - k)%uint63)).
Local Notation "x >>> y" := (rot x y) (at level 30).


(** 2.1 Parameters. *)

(** G rotation *)
Definition R1 := 32%uint63.
Definition R2 := 24%uint63.
Definition R3 := 16%uint63.
Definition R4 := 63%uint63.

Definition G (v: Vec16.t UInt64.t) (a b c d: Uint63.int) (x y: UInt64.t)
: Vec16.t UInt64.t
:= let ua := (Vec16.get_by_int v a) + (Vec16.get_by_int v b) + x in
   let ud := ((Vec16.get_by_int v d) ^ ua) >>> R1 in
   let uc := (Vec16.get_by_int v c) + ud in
   let ub := ((Vec16.get_by_int v b) ^ uc) >>> R2 in
   let wa := ua + ub + y in
   let wd := (ud ^ wa) >>> R3 in
   let wc := uc + wd in
   let wb := (ub ^ wc) >>> R4 in
   let va := Vec16.set_by_int v a wa in
   let vb := Vec16.set_by_int va b wb in
   let vc := Vec16.set_by_int vb c wc in
             Vec16.set_by_int vc d wd.

End MixingFunctionG.


Definition f_round (v m: Vec16.t UInt64.t) (s: Vec16.t Uint63.int)
: Vec16.t UInt64.t
:= let ms i := Vec16.get_by_int m (Vec16.get_by_int s i) in
   (let v1 := G v  0 4  8 12 (ms  0) (ms  1) in
    let v2 := G v1 1 5  9 13 (ms  2) (ms  3) in
    let v3 := G v2 2 6 10 14 (ms  4) (ms  5) in
    let v4 := G v3 3 7 11 15 (ms  6) (ms  7) in
    let v5 := G v4 0 5 10 15 (ms  8) (ms  9) in
    let v6 := G v5 1 6 11 12 (ms 10) (ms 11) in
    let v7 := G v6 2 7  8 13 (ms 12) (ms 13) in
              G v7 3 4  9 14 (ms 14) (ms 15))%uint63.

Definition sigma
: Vec16.t (Vec16.t Uint63.int)
:= (let z := Vec16.fill 0 in
    Vec16.Vec16 (Vec16.Vec16  0  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15)
                (Vec16.Vec16 14 10  4  8  9 15 13  6  1 12  0  2 11  7  5  3)
                (Vec16.Vec16 11  8 12  0  5  2 15 13 10 14  3  6  7  1  9  4)
                (Vec16.Vec16  7  9  3  1 13 12 11 14  2  6  5 10  4  0 15  8)
                (Vec16.Vec16  9  0  5  7  2  4 10 15 14  1 11 12  6  8  3 13)
                (Vec16.Vec16  2 12  6 10  0 11  8  3  4 13  7  5 15 14  1  9)
                (Vec16.Vec16 12  5  1 15 14 13  4 10  0  7  6  3  9  2  8 11)
                (Vec16.Vec16 13 11  7 14 12  1  3  9  5  0 15  4  8  6  2 10)
                (Vec16.Vec16  6 15 14  9 11  3  0  8 12  2 13  7  1  4 10  5)
                (Vec16.Vec16 10  2  8  4  7  6  1  5 15 11  9 14  3 12 13  0)
                z z z z z z)%uint63.

Fixpoint do_f_rounds_rec (v m: Vec16.t UInt64.t) (rounds_left: nat) (round_digit: Uint63.int)
{struct rounds_left}
: Vec16.t UInt64.t
:= match rounds_left with
   | O => v
   | S k => do_f_rounds_rec (f_round v m (Vec16.get_by_int sigma round_digit))
                            m
                            k
                            (if round_digit <? 9
                               then round_digit + 1
                               else 0)%uint63
   end.

Definition do_f_rounds (v m: Vec16.t UInt64.t) (rounds: Z)
:= do_f_rounds_rec v m (Z.to_nat rounds) 0%uint63.

Definition F (h: Vec8.t UInt64.t) (m: Vec16.t UInt64.t)
              (c0 c1: UInt64.t) (final: bool) (rounds: UInt64.t)
: Vec8.t UInt64.t
:= let 'Vec8.Vec8 v0 v1 v2 v3 v4 v5 v6 v7 := h in
   let 'Vec8.Vec8 v8 v9 va vb Xc Xd Xe vf := iv in
   let vc := UInt64.bitwise_xor Xc c0 in
   let vd := UInt64.bitwise_xor Xd c1 in
   let ve := if final then UInt64.bitwise_not Xe else Xe in
   let v := Vec16.Vec16 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 va vb vc vd ve vf in
   let u := do_f_rounds v m (UInt64.Z_of_uint64 rounds) in
   let 'Vec16.Vec16 u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 ua ub uc ud ue uf := u in
   Vec8.Vec8 (v0 ^ u0 ^ u8)
             (v1 ^ u1 ^ u9)
             (v2 ^ u2 ^ ua)
             (v3 ^ u3 ^ ub)
             (v4 ^ u4 ^ uc)
             (v5 ^ u5 ^ ud)
             (v6 ^ u6 ^ ue)
             (v7 ^ u7 ^ uf).