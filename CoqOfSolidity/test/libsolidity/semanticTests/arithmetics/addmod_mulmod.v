(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Contract *)
Module C.
  Definition test (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        if M.bin_op (|
          "!=",
          M.bin_op (|
            "%",
            Value.Tuple [
              M.bin_op (|
                "+",
                M.bin_op (|
                  "**",
                  Value.Integer 2,
                  Value.Integer 255
                |),
                M.bin_op (|
                  "**",
                  Value.Integer 2,
                  Value.Integer 255
                |)
              |)
            ],
            Value.Integer 7
          |),
          M.call (|
            M.get_name (| "addmod" |),
            [
              M.bin_op (|
                "**",
                Value.Integer 2,
                Value.Integer 255
              |),
              M.bin_op (|
                "**",
                Value.Integer 2,
                Value.Integer 255
              |),
              Value.Integer 7
            ]
          |)
        |) then
          M.return_ (|
            Value.Integer 1
          |)
        else
          Value.Tuple [] in
      let _ :=
        if M.bin_op (|
          "!=",
          M.bin_op (|
            "%",
            Value.Tuple [
              M.bin_op (|
                "+",
                M.bin_op (|
                  "**",
                  Value.Integer 2,
                  Value.Integer 255
                |),
                M.bin_op (|
                  "**",
                  Value.Integer 2,
                  Value.Integer 255
                |)
              |)
            ],
            Value.Integer 7
          |),
          M.call (|
            M.get_name (| "addmod" |),
            [
              M.bin_op (|
                "**",
                Value.Integer 2,
                Value.Integer 255
              |),
              M.bin_op (|
                "**",
                Value.Integer 2,
                Value.Integer 255
              |),
              Value.Integer 7
            ]
          |)
        |) then
          M.return_ (|
            Value.Integer 2
          |)
        else
          Value.Tuple [] in
      let _ :=
        M.return_ (|
          Value.Integer 0
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.
