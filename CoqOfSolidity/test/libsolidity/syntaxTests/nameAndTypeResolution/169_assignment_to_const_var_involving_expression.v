(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Contract *)
Module C.
  Definition x : Value.t :=
    M.bin_op (|
      "+",
      Value.Integer 0x123,
      Value.Integer 0x456
    |).
End C.
