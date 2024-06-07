(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Contract *)
Module C.
  Definition f (α : list Value.t) : M :=
    match α with
    | [a, b, c] =>
      let _ :=
        M.return_ (|
          Value.Tuple [
            M.get_name (| "a" |),
            M.member_access (|
              M.get_name (| "b" |),
              "length"
            |),
            M.index_access (|
              M.get_name (| "b" |),
              Some (Value.Integer 3)
            |),
            M.get_name (| "c" |)
          ]
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition f_external (α : list Value.t) : M :=
    match α with
    | [a, b, c] =>
      let _ :=
        M.return_ (|
          Value.Tuple [
            M.get_name (| "a" |),
            M.member_access (|
              M.get_name (| "b" |),
              "length"
            |),
            M.index_access (|
              M.get_name (| "b" |),
              Some (Value.Integer 3)
            |),
            M.get_name (| "c" |)
          ]
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.
