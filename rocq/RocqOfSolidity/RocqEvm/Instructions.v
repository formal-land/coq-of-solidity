From Coq Require Import Arith NArith ZArith String.
From Coq Require Import Lia Bool.
From Coq Require Import Eqdep_dec.
From Coq Require Import Uint63.

Require Import Nibble.
Local Open Scope N_scope.

Inductive instruction :=
(* 0x00 *)
| STOP
| ADD
| MUL
| SUB
| DIV
| SDIV
| MOD
| SMOD
| ADDMOD
| MULMOD
| EXP
| SIGNEXTEND

(* 0x10 *)
| LT
| GT
| SLT
| SGT
| EQ
| ISZERO
| AND
| OR
| XOR
| NOT
| BYTE
| SHL
| SHR
| SAR

(* 0x20 *)
| SHA3

(* 0x30 *)
| ADDRESS
| BALANCE
| ORIGIN
| CALLER
| CALLVALUE
| CALLDATALOAD
| CALLDATASIZE
| CALLDATACOPY
| CODESIZE
| CODECOPY
| GASPRICE
| EXTCODESIZE
| EXTCODECOPY
| RETURNDATASIZE
| RETURNDATACOPY
| EXTCODEHASH

(* 0x40 *)
| BLOCKHASH
| COINBASE
| TIMESTAMP
| NUMBER
| DIFFICULTY
| GASLIMIT
| CHAINID (* https://eips.ethereum.org/EIPS/eip-1344 *)
| SELFBALANCE

(* 0x50 *)
| POP
| MLOAD
| MSTORE
| MSTORE8
| SLOAD
| SSTORE
| JUMP
| JUMPI
| PC
| MSIZE
| GAS
| JUMPDEST

(* 0x60 *)
| PUSH (n: N) (ok: andb (0 <? n) (n <=? 32) = true)

(* 0x80 *)
| DUP  (n: N) (ok: andb (0 <? n) (n <=? 16) = true)

(* 0x90 *)
| SWAP (n: N) (ok: andb (0 <? n) (n <=? 16) = true)

(* 0xa0 *)
| LOG (n: N) (ok: n <=? 4 = true)

(* 0xf0 *)
| CREATE
| CALL
| CALLCODE
| RETURN
| DELEGATECALL
| CREATE2
| STATICCALL
| REVERT
| SELFDESTRUCT.

Definition opcode_of_push (n: N) (ok: andb (0 <? n) (n <=? 32) = true)
: byte
:= byte_of_N (N_of_byte (byte_of_hex_digits x6 x0) + N.pred n).

Definition opcode_of_dup (n: N) (ok: andb (0 <? n) (n <=? 16) = true)
: byte
:= byte_of_N (N_of_byte (byte_of_hex_digits x8 x0) + N.pred n).

Definition opcode_of_swap (n: N) (ok: andb (0 <? n) (n <=? 16) = true)
: byte
:= byte_of_N (N_of_byte (byte_of_hex_digits x9 x0) + N.pred n).

Definition opcode_of_log (n: N) (ok: n <=? 4 = true)
: byte
:= byte_of_N (N_of_byte (byte_of_hex_digits xA x0) + n).

Lemma push_helper_0 (d: hex_digit):
  ((0 <? N_of_hex_digit d + 1) && (N_of_hex_digit d + 1 <=? 32))%bool = true.
Proof.
  apply andb_true_intro. split.
  { rewrite N.ltb_lt. apply N.add_pos_r. apply N.lt_0_1. }
  rewrite N.leb_le. 
  assert(UB := N_of_hex_digit_ub d).
  (* lia works here but it's too late, here's the manual proof: *)
  apply N.lt_pred_le. rewrite N.add_1_r. rewrite N.pred_succ.
  apply (N.lt_trans _ _ _ UB).
  rewrite<- N.ltb_lt. trivial.
Qed.

Lemma push_helper_16 (d: hex_digit):
  ((0 <? N_of_hex_digit d + 17) && (N_of_hex_digit d + 17 <=? 32))%bool = true.
Proof.
  apply andb_true_intro. split.
  { rewrite N.ltb_lt. apply N.add_pos_r. apply N.lt_0_1. }
  rewrite N.leb_le. 
  assert(UB := N_of_hex_digit_ub d).
  remember (N_of_hex_digit d) as n. clear Heqn.
  apply N.lt_le_pred in UB. cbn in UB.
  apply (N.add_le_mono n 15 17 17) in UB.
  { cbn in UB. exact UB. }
  apply N.le_refl.
Qed.

Definition x6_to_push (low: hex_digit)
: instruction
:= PUSH (N_of_hex_digit low + 1) (push_helper_0 low).

Definition x7_to_push (low: hex_digit)
: instruction
:= PUSH (N_of_hex_digit low + 17) (push_helper_16 low).

Lemma dup_swap_helper (d: hex_digit):
  ((0 <? N_of_hex_digit d + 1) && (N_of_hex_digit d + 1 <=? 16))%bool = true.
Proof.
  apply andb_true_intro. split.
  { rewrite N.ltb_lt. apply N.add_pos_r. apply N.lt_0_1. }
  rewrite N.leb_le. 
  assert(UB := N_of_hex_digit_ub d).
  apply N.lt_pred_le. rewrite N.add_1_r. rewrite N.pred_succ.
  exact UB.
Qed.

Definition x8_to_dup (low: hex_digit)
: instruction
:= DUP (N_of_hex_digit low + 1) (dup_swap_helper low).

Definition x9_to_swap (low: hex_digit)
: instruction
:= SWAP (N_of_hex_digit low + 1) (dup_swap_helper low).

Definition byte_of_instruction (op: instruction)
: byte
:= let x := byte_of_hex_digits in
   match op with
   (* 0x00 *)
   | STOP       => x x0 x0
   | ADD        => x x0 x1
   | MUL        => x x0 x2
   | SUB        => x x0 x3
   | DIV        => x x0 x4
   | SDIV       => x x0 x5
   | MOD        => x x0 x6
   | SMOD       => x x0 x7
   | ADDMOD     => x x0 x8
   | MULMOD     => x x0 x9
   | EXP        => x x0 xA
   | SIGNEXTEND => x x0 xB

   (* 0x10 *)
   | LT     => x x1 x0
   | GT     => x x1 x1
   | SLT    => x x1 x2
   | SGT    => x x1 x3
   | EQ     => x x1 x4
   | ISZERO => x x1 x5
   | AND    => x x1 x6
   | OR     => x x1 x7
   | XOR    => x x1 x8
   | NOT    => x x1 x9
   | BYTE   => x x1 xA
   | SHL    => x x1 xB
   | SHR    => x x1 xC
   | SAR    => x x1 xD

   (* 0x20 *)
   | SHA3 => x x2 x0

   (* 0x30 *)
   | ADDRESS        => x x3 x0
   | BALANCE        => x x3 x1
   | ORIGIN         => x x3 x2
   | CALLER         => x x3 x3
   | CALLVALUE      => x x3 x4
   | CALLDATALOAD   => x x3 x5
   | CALLDATASIZE   => x x3 x6
   | CALLDATACOPY   => x x3 x7
   | CODESIZE       => x x3 x8
   | CODECOPY       => x x3 x9
   | GASPRICE       => x x3 xA
   | EXTCODESIZE    => x x3 xB
   | EXTCODECOPY    => x x3 xC
   | RETURNDATASIZE => x x3 xD
   | RETURNDATACOPY => x x3 xE
   | EXTCODEHASH    => x x3 xF

   (* 0x40 *)
   | BLOCKHASH   => x x4 x0
   | COINBASE    => x x4 x1
   | TIMESTAMP   => x x4 x2
   | NUMBER      => x x4 x3
   | DIFFICULTY  => x x4 x4
   | GASLIMIT    => x x4 x5
   | CHAINID     => x x4 x6
   | SELFBALANCE => x x4 x7

   (* 0x50 *)
   | POP      => x x5 x0
   | MLOAD    => x x5 x1
   | MSTORE   => x x5 x2
   | MSTORE8  => x x5 x3
   | SLOAD    => x x5 x4
   | SSTORE   => x x5 x5
   | JUMP     => x x5 x6
   | JUMPI    => x x5 x7
   | PC       => x x5 x8
   | MSIZE    => x x5 x9
   | GAS      => x x5 xA
   | JUMPDEST => x x5 xB

   (* 0x60 *)
   | PUSH n ok => opcode_of_push n ok

   (* 0x80 *)
   | DUP n ok => opcode_of_dup n ok

   (* 0x90 *)
   | SWAP n ok => opcode_of_swap n ok

   (* 0xa0 *)
   | LOG n ok => opcode_of_log n ok

   (* 0xf0 *)
   | CREATE       => x xF x0
   | CALL         => x xF x1
   | CALLCODE     => x xF x2
   | RETURN       => x xF x3
   | DELEGATECALL => x xF x4
   | CREATE2      => x xF x5
   | STATICCALL   => x xF xA
   | REVERT       => x xF xD
   | SELFDESTRUCT => x xF xF
   end.

Definition instruction_of_byte (b: byte)
: option instruction
:= let (high, low) := hex_digits_of_byte b in
   match high with
   | x0 => 
      match low with
      | x0 => Some STOP
      | x1 => Some ADD
      | x2 => Some MUL
      | x3 => Some SUB
      | x4 => Some DIV
      | x5 => Some SDIV
      | x6 => Some MOD
      | x7 => Some SMOD
      | x8 => Some ADDMOD
      | x9 => Some MULMOD
      | xA => Some EXP
      | xB => Some SIGNEXTEND
      | _ => None
      end
   | x1 =>
      match low with
      | x0 => Some LT
      | x1 => Some GT
      | x2 => Some SLT
      | x3 => Some SGT
      | x4 => Some EQ
      | x5 => Some ISZERO
      | x6 => Some AND
      | x7 => Some OR
      | x8 => Some XOR
      | x9 => Some NOT
      | xA => Some BYTE
      | xB => Some SHL
      | xC => Some SHR
      | xD => Some SAR
      | _ => None
      end
   | x2 =>
      match low with
      | x0 => Some SHA3
      | _ => None
      end
   | x3 =>
      match low with
      | x0 => Some ADDRESS
      | x1 => Some BALANCE
      | x2 => Some ORIGIN
      | x3 => Some CALLER
      | x4 => Some CALLVALUE
      | x5 => Some CALLDATALOAD
      | x6 => Some CALLDATASIZE
      | x7 => Some CALLDATACOPY
      | x8 => Some CODESIZE
      | x9 => Some CODECOPY
      | xA => Some GASPRICE
      | xB => Some EXTCODESIZE
      | xC => Some EXTCODECOPY
      | xD => Some RETURNDATASIZE
      | xE => Some RETURNDATACOPY
      | xF => Some EXTCODEHASH
      end
    | x4 =>
      match low with
      | x0 => Some BLOCKHASH
      | x1 => Some COINBASE
      | x2 => Some TIMESTAMP
      | x3 => Some NUMBER
      | x4 => Some DIFFICULTY
      | x5 => Some GASLIMIT
      | x6 => Some CHAINID
      | x7 => Some SELFBALANCE
      | _ => None
      end
    | x5 =>
      match low with
      | x0 => Some POP
      | x1 => Some MLOAD
      | x2 => Some MSTORE
      | x3 => Some MSTORE8
      | x4 => Some SLOAD
      | x5 => Some SSTORE
      | x6 => Some JUMP
      | x7 => Some JUMPI
      | x8 => Some PC
      | x9 => Some MSIZE
      | xA => Some GAS
      | xB => Some JUMPDEST
      | _ => None
      end
    | x6 => Some (x6_to_push low)
    | x7 => Some (x7_to_push low)
    | x8 => Some (x8_to_dup low)
    | x9 => Some (x9_to_swap low)
    | xA => 
      match low with
      | x0 => Some (LOG 0 eq_refl)
      | x1 => Some (LOG 1 eq_refl)
      | x2 => Some (LOG 2 eq_refl)
      | x3 => Some (LOG 3 eq_refl)
      | x4 => Some (LOG 4 eq_refl)
      | _ => None
      end
    | xF => 
      match low with
      | x0 => Some CREATE
      | x1 => Some CALL
      | x2 => Some CALLCODE
      | x3 => Some RETURN
      | x4 => Some DELEGATECALL
      | x5 => Some CREATE2
      (* 6-9 => None *)
      | xA => Some STATICCALL
      (* B,C => None *)
      | xD => Some REVERT
      (* E => None *)
      | xF => Some SELFDESTRUCT
      | _ => None
      end
    | _ => None
   end.

Lemma byte_of_instruction_of_byte (b: byte):
  match instruction_of_byte b with
  | Some op => byte_of_instruction op = b
  | None => True
  end.
Proof.
cbn. destruct b. 
destruct a7; destruct a6; destruct a5; destruct a4; 
destruct a3; destruct a2; destruct a1; destruct a0; easy.
Qed.

Lemma instruction_irrel {bound: N}
                        (OP: forall n: N, (0 <? n) && (n <=? bound) = true -> instruction)
                        {a b: N}
                        (OkA: (0 <? a) && (a <=? bound) = true)
                        (OkB: (0 <? b) && (b <=? bound) = true)
                        (E: a = b):
  OP a OkA = OP b OkB.
Proof.
subst. f_equal. apply eq_proofs_unicity. decide equality.
Qed.

Lemma instruction_of_byte_of_instruction (op: instruction):
  instruction_of_byte (byte_of_instruction op) = Some op.
Proof.
cbn. destruct op; trivial; remember (byte_of_instruction _) as b;
  unfold byte_of_instruction in Heqb;
  try (
    assert (ok' := ok);
    try rewrite andb_true_iff in ok';
    try destruct ok' as (LB, UB);
    try apply N.ltb_lt in LB;
    try apply N.leb_le in UB;
    try apply N.leb_le in ok'
  );
  remember (pop_nibble (N.pred n)) as p;
  assert(Q := pop_nibble_then_push (N.pred n));
  destruct p as (k, nib);
  rewrite<- Heqp in Q; cbn in Q;
  rewrite push_nibble_arith in Q;
  unfold opcode_of_push in Heqb;
  unfold opcode_of_dup in Heqb;
  unfold opcode_of_swap in Heqb;
  unfold opcode_of_log in Heqb;
  rewrite<- Q in Heqp;
  assert (B16 := N_of_nibble_bound nib);
  remember (N_of_nibble nib) as m; clear Heqm;
  subst.
{ (* PUSH *)
  rewrite<- Q.
  replace (N_of_byte (byte_of_hex_digits x6 x0) + (16 * k + m)) with 
          (16 * (k + 6) + m).
  2:{
    remember (N_of_byte (byte_of_hex_digits _ _)) as offset.
    cbn in Heqoffset. subst.
    lia.
  }
  rewrite byte_of_N_arith; try assumption. 2:{ lia. }
  rewrite high_nibble_ok. rewrite low_nibble_ok.
  remember (nibble_of_N m) as low.
  assert (M: m = N_of_nibble low).
  { subst. now rewrite N_of_nibble_of_N. }
  clear Heqlow.
  assert (R: n = 16 * k + m + 1). { lia. }
  clear Q.
  assert (K: k <= 1). { lia. }
  destruct k.
  {
    cbn. subst. f_equal.
    unfold x6_to_push.
    apply instruction_irrel.
    destruct low as (a3, a2, a1, a0); destruct a3; destruct a2; destruct a1; destruct a0; easy.
  }
  assert (P: p = 1%positive). { lia. }
  subst. unfold x7_to_push. cbn. f_equal.
  apply instruction_irrel.
  destruct low as (a3, a2, a1, a0); destruct a3; destruct a2; destruct a1; destruct a0; easy.
}
{ (* DUP *)
  assert (K: k = 0). { lia. } subst k. rewrite<- Q in *.
  replace (N_of_byte (byte_of_hex_digits x8 x0) + (16 * 0 + m)) with 
          (16 * 8 + m).
  2:{
    remember (N_of_byte (byte_of_hex_digits _ _)) as offset.
    cbn in Heqoffset. subst.
    lia.
  }
  rewrite byte_of_N_arith; try assumption. 2:{ lia. }
  rewrite high_nibble_ok. rewrite low_nibble_ok.
  remember (nibble_of_N m) as low.
  assert (M: m = N_of_nibble low).
  { subst. now rewrite N_of_nibble_of_N. }
  clear Heqlow.
  assert (R: n = m + 1). { lia. } 
  cbn. unfold x8_to_dup. f_equal.
  apply instruction_irrel. subst.
  destruct low as (a3, a2, a1, a0); destruct a3; destruct a2; destruct a1; destruct a0; easy.
}
{ (* SWAP *) (* XXX: just copying *)
  assert (K: k = 0). { lia. } subst k. rewrite<- Q in *.
  replace (N_of_byte (byte_of_hex_digits x9 x0) + (16 * 0 + m)) with 
          (16 * 9 + m).
  2:{
    remember (N_of_byte (byte_of_hex_digits _ _)) as offset.
    cbn in Heqoffset. subst.
    lia.
  }
  rewrite byte_of_N_arith; try assumption. 2:{ lia. }
  rewrite high_nibble_ok. rewrite low_nibble_ok.
  remember (nibble_of_N m) as low.
  assert (M: m = N_of_nibble low).
  { subst. now rewrite N_of_nibble_of_N. }
  clear Heqlow.
  assert (R: n = m + 1). { lia. } 
  cbn. unfold x9_to_swap. f_equal.
  apply instruction_irrel. subst.
  destruct low as (a3, a2, a1, a0); destruct a3; destruct a2; destruct a1; destruct a0; easy.
}
(* LOG *)
clear Heqp Q B16 m nib k.
remember (pop_nibble n) as p.
assert(Q := pop_nibble_then_push n).
destruct p as (k, nib).
rewrite<- Heqp in Q. cbn in Q.
rewrite push_nibble_arith in Q.
unfold opcode_of_log.
rewrite<- Q in Heqp.
assert (B16 := N_of_nibble_bound nib).
remember (N_of_nibble nib) as m; clear Heqm.

assert (K: k = 0). { lia. } subst k.
replace (N_of_byte (byte_of_hex_digits xA x0) + n) with 
        (16 * 10 + m).
2:{
  remember (N_of_byte (byte_of_hex_digits _ _)) as offset.
  cbn in Heqoffset. subst.
  lia.
}
rewrite byte_of_N_arith; try assumption. 2:{ lia. }
rewrite high_nibble_ok. rewrite low_nibble_ok.
remember (nibble_of_N m) as low.
assert (M: m = N_of_nibble low).
{ subst. now rewrite N_of_nibble_of_N. }
clear Heqlow.
assert (R: n = m). { lia. } clear Q.
subst. cbn.
destruct low as (a3, a2, a1, a0); destruct a3; destruct a2; destruct a1; destruct a0;
cbn in *; try easy; repeat f_equal; apply eq_proofs_unicity; decide equality.
Qed.

(* This is the deltas and alphas from the instruction set table in Appendix H.2
   and (along with some new instructions) it's also in go-ethereum/core/vm/jump_table.go
   with go-ethereum/core/vm/eips.go.
*)
Definition consume_and_produce_count (op: instruction)
: int * int
:= (match op with
   (* 0x00 *)
   | STOP       => (0, 0)
   | ADD        => (2, 1)
   | MUL        => (2, 1)
   | SUB        => (2, 1)
   | DIV        => (2, 1)
   | SDIV       => (2, 1)
   | MOD        => (2, 1)
   | SMOD       => (2, 1)
   | ADDMOD     => (3, 1)
   | MULMOD     => (3, 1)
   | EXP        => (2, 1)
   | SIGNEXTEND => (2, 1)

   (* 0x10 *)
   | LT     => (2, 1)
   | GT     => (2, 1)
   | SLT    => (2, 1)
   | SGT    => (2, 1)
   | EQ     => (2, 1)
   | ISZERO => (1, 1)
   | AND    => (2, 1)
   | OR     => (2, 1)
   | XOR    => (2, 1)
   | NOT    => (1, 1)
   | BYTE   => (2, 1)
   | SHL    => (2, 1)
   | SHR    => (2, 1)
   | SAR    => (2, 1)

   (* 0x20 *)
   | SHA3 => (2, 1)

   (* 0x30 *)
   | ADDRESS        => (0, 1)
   | BALANCE        => (1, 1)
   | ORIGIN         => (0, 1)
   | CALLER         => (0, 1)
   | CALLVALUE      => (0, 1)
   | CALLDATALOAD   => (1, 1)
   | CALLDATASIZE   => (0, 1)
   | CALLDATACOPY   => (3, 0)
   | CODESIZE       => (0, 1)
   | CODECOPY       => (3, 0)
   | GASPRICE       => (0, 1)
   | EXTCODESIZE    => (1, 1)
   | EXTCODECOPY    => (4, 0)
   | RETURNDATASIZE => (0, 1)
   | RETURNDATACOPY => (3, 0)
   | EXTCODEHASH    => (1, 1)

   (* 0x40 *)
   | BLOCKHASH   => (1, 1)
   | COINBASE    => (0, 1)
   | TIMESTAMP   => (0, 1)
   | NUMBER      => (0, 1)
   | DIFFICULTY  => (0, 1)
   | GASLIMIT    => (0, 1)
   | CHAINID     => (0, 1)
   | SELFBALANCE => (0, 1)

   (* 0x50 *)
   | POP      => (1, 0)
   | MLOAD    => (1, 1)
   | MSTORE   => (2, 0)
   | MSTORE8  => (2, 0)
   | SLOAD    => (1, 1)
   | SSTORE   => (2, 0)
   | JUMP     => (1, 0)
   | JUMPI    => (2, 0)
   | PC       => (0, 1)
   | MSIZE    => (0, 1)
   | GAS      => (0, 1)
   | JUMPDEST => (0, 0)

   (* 0x60 *)
   | PUSH n ok => (0, 1)

   (* 0x80 *)
   | DUP n ok => let k := of_Z (Z.of_N n) in (k, k + 1)

   (* 0x90 *)
   | SWAP n ok => let k := of_Z (Z.of_N n) in (k + 1, k + 1)

   (* 0xa0 *)
   | LOG n ok => let k := of_Z (Z.of_N n) in (k + 2, 0)

   (* 0xf0 *)
   | CREATE       => (3, 1)
   | CALL         => (7, 1)
   | CALLCODE     => (7, 1)
   | RETURN       => (2, 0)
   | DELEGATECALL => (6, 1)
   | CREATE2      => (4, 1)
   | STATICCALL   => (6, 1)
   | REVERT       => (2, 0)
   | SELFDESTRUCT => (1, 0)
   end)%uint63.

Definition consume_count (op: instruction) := fst (consume_and_produce_count op).
Definition produce_count (op: instruction) := snd (consume_and_produce_count op).