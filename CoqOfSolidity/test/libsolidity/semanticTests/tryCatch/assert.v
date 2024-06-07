(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Contract *)
Module C.
  Definition g (α : list Value.t) : M :=
    match α with
    | [x] =>
      let _ :=
        M.call (|
          M.get_name (| "assert" |),
          [
            M.get_name (| "x" |)
          ]
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition f (α : list Value.t) : M :=
    match α with
    | [x] =>
      let _ :=
        TryStatement M.call (|
          FunctionCallOptions M.member_access (|
            M.get_name (| "this" |),
            "g"
          |) [gas, ] Value.Integer 8000
,
          [
            M.get_name (| "x" |)
          ]
        |) TryCatchClause   let _ :=
          M.return_ (|
            Value.Integer 1
          |) in
        Value.Tuple [], TryCatchClause   let _ :=
          M.return_ (|
            Value.Integer 2
          |) in
        Value.Tuple [] in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.
