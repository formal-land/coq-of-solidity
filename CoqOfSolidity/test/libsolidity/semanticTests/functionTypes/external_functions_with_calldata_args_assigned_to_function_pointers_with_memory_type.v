(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Contract *)
Module C.
  Definition g (α : list Value.t) : M :=
    match α with
    | [_] =>
      let _ :=
        M.return_ (|
          Value.Bool true
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition main (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.define (|
          [ "ptr" ],
          M.member_access (|
            M.get_name (| "this" |),
            "g"
          |)
        |) in
      let _ :=
        M.return_ (|
          M.call (|
            M.get_name (| "ptr" |),
            [
              Value.String "testString"
            ]
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.
