(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Contract *)
Module test.
  (* Struct s2 *)

  Definition data : Value.t :=
    undefined.

  Definition check (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.return_ (|
          M.bin_op (|
            "&&",
            M.bin_op (|
              "&&",
              M.bin_op (|
                "&&",
                M.bin_op (|
                  "==",
                  M.member_access (|
                    M.get_name (| "data" |),
                    "z"
                  |),
                  Value.Integer 2
                |),
                M.bin_op (|
                  "==",
                  M.member_access (|
                    M.index_access (|
                      M.member_access (|
                        M.get_name (| "data" |),
                        "recursive"
                      |),
                      Some (Value.Integer 0)
                    |),
                    "z"
                  |),
                  Value.Integer 3
                |)
              |),
              M.bin_op (|
                "==",
                M.member_access (|
                  M.index_access (|
                    M.member_access (|
                      M.index_access (|
                        M.member_access (|
                          M.get_name (| "data" |),
                          "recursive"
                        |),
                        Some (Value.Integer 0)
                      |),
                      "recursive"
                    |),
                    Some (Value.Integer 1)
                  |),
                  "z"
                |),
                Value.Integer 0
              |)
            |),
            M.bin_op (|
              "==",
              M.member_access (|
                M.index_access (|
                  M.member_access (|
                    M.index_access (|
                      M.member_access (|
                        M.get_name (| "data" |),
                        "recursive"
                      |),
                      Some (Value.Integer 0)
                    |),
                    "recursive"
                  |),
                  Some (Value.Integer 0)
                |),
                "z"
              |),
              Value.Integer 1
            |)
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition set (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.assign (|
          "=",
          M.member_access (|
            M.get_name (| "data" |),
            "z"
          |),
          Value.Integer 2
        |) in
      let _ :=
        M.define (|
          [ "map" ],
          M.member_access (|
            M.get_name (| "data" |),
            "recursive"
          |)
        |) in
      let _ :=
        M.define (|
          [ "inner" ],
          M.index_access (|
            M.get_name (| "map" |),
            Some (Value.Integer 0)
          |)
        |) in
      let _ :=
        M.assign (|
          "=",
          M.member_access (|
            M.get_name (| "inner" |),
            "z"
          |),
          Value.Integer 3
        |) in
      let _ :=
        M.assign (|
          "=",
          M.member_access (|
            M.index_access (|
              M.member_access (|
                M.get_name (| "inner" |),
                "recursive"
              |),
              Some (Value.Integer 0)
            |),
            "z"
          |),
          M.bin_op (|
            "+",
            M.member_access (|
              M.index_access (|
                M.member_access (|
                  M.get_name (| "inner" |),
                  "recursive"
                |),
                Some (Value.Integer 1)
              |),
              "z"
            |),
            Value.Integer 1
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End test.
