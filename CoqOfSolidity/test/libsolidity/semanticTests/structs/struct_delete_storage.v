(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Contract *)
Module C.
  (* Struct S *)

  Definition b : Value.t :=
    Value.Integer 23.

  Definition s : Value.t :=
    undefined.

  Definition a : Value.t :=
    Value.Integer 17.

  Definition f (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.assign (|
          "=",
          M.member_access (|
            M.get_name (| "s" |),
            "x"
          |),
          Value.Integer 42
        |) in
      let _ :=
        M.assign (|
          "=",
          M.member_access (|
            M.get_name (| "s" |),
            "y"
          |),
          Value.Integer 42
        |) in
      let _ :=
        M.assign (|
          "=",
          M.member_access (|
            M.get_name (| "s" |),
            "y"
          |),
          Value.Integer 42
        |) in
      let _ :=
        M.un_op (|
          true,
          "delete",
          M.get_name (| "s" |)
        |) in
      let _ :=
        M.call (|
          M.get_name (| "assert" |),
          [
            M.bin_op (|
              "==",
              M.member_access (|
                M.get_name (| "s" |),
                "x"
              |),
              Value.Integer 0
            |)
          ]
        |) in
      let _ :=
        M.call (|
          M.get_name (| "assert" |),
          [
            M.bin_op (|
              "==",
              M.member_access (|
                M.get_name (| "s" |),
                "y"
              |),
              Value.Integer 0
            |)
          ]
        |) in
      let _ :=
        M.call (|
          M.get_name (| "assert" |),
          [
            M.bin_op (|
              "==",
              M.member_access (|
                M.get_name (| "s" |),
                "z"
              |),
              Value.Integer 0
            |)
          ]
        |) in
      let _ :=
        M.call (|
          M.get_name (| "assert" |),
          [
            M.bin_op (|
              "==",
              M.get_name (| "b" |),
              Value.Integer 23
            |)
          ]
        |) in
      let _ :=
        M.call (|
          M.get_name (| "assert" |),
          [
            M.bin_op (|
              "==",
              M.get_name (| "a" |),
              Value.Integer 17
            |)
          ]
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.
