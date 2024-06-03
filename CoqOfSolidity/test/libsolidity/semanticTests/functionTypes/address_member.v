(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Contract *)
Module C.
  Definition f (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.assign (|
          "=",
          M.get_name (| "a1" |),
          M.member_access (|
            M.member_access (|
              M.get_name (| "this" |),
              "f"
            |),
            "address"
          |)
        |) in
      let _ :=
        M.member_access (|
          M.member_access (|
            M.get_name (| "this" |),
            "f"
          |),
          "address"
        |) in
      let _ :=
        M.index_access (|
          Value.Array [
            M.member_access (|
              M.member_access (|
                M.get_name (| "this" |),
                "f"
              |),
              "address"
            |)
          ],
          Some (Value.Integer 0)
        |) in
      let _ :=
        M.assign (|
          "=",
          M.get_name (| "a2" |),
          M.index_access (|
            Value.Array [
              M.member_access (|
                M.member_access (|
                  M.get_name (| "this" |),
                  "f"
                |),
                "address"
              |)
            ],
            Some (Value.Integer 0)
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.
