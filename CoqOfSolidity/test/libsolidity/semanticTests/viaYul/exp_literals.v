(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Contract *)
Module C.
  Definition exp_2 (α : list Value.t) : M :=
    match α with
    | [y] =>
      let _ :=
        M.return_ (|
          M.bin_op (|
            "**",
            Value.Integer 2,
            M.get_name (| "y" |)
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition exp_minus_2 (α : list Value.t) : M :=
    match α with
    | [y] =>
      let _ :=
        M.return_ (|
          M.bin_op (|
            "**",
            Value.Tuple [
              M.un_op (|
                true,
                "-",
                Value.Integer 2
              |)
            ],
            M.get_name (| "y" |)
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition exp_uint_max (α : list Value.t) : M :=
    match α with
    | [y] =>
      let _ :=
        M.return_ (|
          M.bin_op (|
            "**",
            Value.Tuple [
              M.bin_op (|
                "-",
                M.bin_op (|
                  "**",
                  Value.Integer 2,
                  Value.Integer 256
                |),
                Value.Integer 1
              |)
            ],
            M.get_name (| "y" |)
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition exp_int_max (α : list Value.t) : M :=
    match α with
    | [y] =>
      let _ :=
        M.return_ (|
          M.bin_op (|
            "**",
            Value.Tuple [
              M.bin_op (|
                "**",
                Value.Tuple [
                  M.un_op (|
                    true,
                    "-",
                    Value.Integer 2
                  |)
                ],
                Value.Integer 255
              |)
            ],
            M.get_name (| "y" |)
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition exp_5 (α : list Value.t) : M :=
    match α with
    | [y] =>
      let _ :=
        M.return_ (|
          M.bin_op (|
            "**",
            Value.Integer 5,
            M.get_name (| "y" |)
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition exp_minus_5 (α : list Value.t) : M :=
    match α with
    | [y] =>
      let _ :=
        M.return_ (|
          M.bin_op (|
            "**",
            Value.Tuple [
              M.un_op (|
                true,
                "-",
                Value.Integer 5
              |)
            ],
            M.get_name (| "y" |)
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition exp_256 (α : list Value.t) : M :=
    match α with
    | [y] =>
      let _ :=
        M.return_ (|
          M.bin_op (|
            "**",
            Value.Integer 256,
            M.get_name (| "y" |)
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition exp_minus_256 (α : list Value.t) : M :=
    match α with
    | [y] =>
      let _ :=
        M.return_ (|
          M.bin_op (|
            "**",
            Value.Tuple [
              M.un_op (|
                true,
                "-",
                Value.Integer 256
              |)
            ],
            M.get_name (| "y" |)
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.
