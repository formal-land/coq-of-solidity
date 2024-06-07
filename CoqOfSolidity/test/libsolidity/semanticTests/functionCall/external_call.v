(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Pragma solidity>=0.6.0 *)

(* Contract *)
Module C.
  Definition g (α : list Value.t) : M :=
    match α with
    | [n] =>
      let _ :=
        M.return_ (|
          M.bin_op (|
            "+",
            M.get_name (| "n" |),
            Value.Integer 1
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition f (α : list Value.t) : M :=
    match α with
    | [n] =>
      let _ :=
        M.return_ (|
          M.call (|
            M.member_access (|
              M.get_name (| "this" |),
              "g"
            |),
            [
              M.bin_op (|
                "*",
                Value.Integer 2,
                M.get_name (| "n" |)
              |)
            ]
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.
