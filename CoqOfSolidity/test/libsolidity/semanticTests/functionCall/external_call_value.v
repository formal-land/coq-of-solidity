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
          Value.Tuple [
            M.bin_op (|
              "*",
              M.member_access (|
                M.get_name (| "msg" |),
                "value"
              |),
              Value.Integer 1000
            |),
            M.get_name (| "n" |)
          ]
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
            FunctionCallOptions M.member_access (|
              M.get_name (| "this" |),
              "g"
            |) [value, ] Value.Integer 10
,
            [
              M.get_name (| "n" |)
            ]
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.
