(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Pragma abicoderv2 *)

(* Contract *)
Module C.
  Definition e (α : list Value.t) : M :=
    match α with
    | [a] =>
      let _ :=
        M.return_ (|
          Value.Integer 7
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.
