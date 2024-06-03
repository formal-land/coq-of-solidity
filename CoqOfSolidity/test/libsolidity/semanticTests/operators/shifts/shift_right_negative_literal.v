(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Contract *)
Module C.
  Definition f1 (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.return_ (|
          M.bin_op (|
            "==",
            Value.Tuple [
              M.bin_op (|
                ">>",
                M.un_op (|
                  true,
                  "-",
                  Value.Integer 4266
                |),
                Value.Integer 0
              |)
            ],
            M.un_op (|
              true,
              "-",
              Value.Integer 4266
            |)
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition f2 (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.return_ (|
          M.bin_op (|
            "==",
            Value.Tuple [
              M.bin_op (|
                ">>",
                M.un_op (|
                  true,
                  "-",
                  Value.Integer 4266
                |),
                Value.Integer 1
              |)
            ],
            M.un_op (|
              true,
              "-",
              Value.Integer 2133
            |)
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition f3 (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.return_ (|
          M.bin_op (|
            "==",
            Value.Tuple [
              M.bin_op (|
                ">>",
                M.un_op (|
                  true,
                  "-",
                  Value.Integer 4266
                |),
                Value.Integer 4
              |)
            ],
            M.un_op (|
              true,
              "-",
              Value.Integer 267
            |)
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition f4 (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.return_ (|
          M.bin_op (|
            "==",
            Value.Tuple [
              M.bin_op (|
                ">>",
                M.un_op (|
                  true,
                  "-",
                  Value.Integer 4266
                |),
                Value.Integer 8
              |)
            ],
            M.un_op (|
              true,
              "-",
              Value.Integer 17
            |)
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition f5 (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.return_ (|
          M.bin_op (|
            "==",
            Value.Tuple [
              M.bin_op (|
                ">>",
                M.un_op (|
                  true,
                  "-",
                  Value.Integer 4266
                |),
                Value.Integer 16
              |)
            ],
            M.un_op (|
              true,
              "-",
              Value.Integer 1
            |)
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition f6 (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.return_ (|
          M.bin_op (|
            "==",
            Value.Tuple [
              M.bin_op (|
                ">>",
                M.un_op (|
                  true,
                  "-",
                  Value.Integer 4266
                |),
                Value.Integer 17
              |)
            ],
            M.un_op (|
              true,
              "-",
              Value.Integer 1
            |)
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition g1 (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.return_ (|
          M.bin_op (|
            "==",
            Value.Tuple [
              M.bin_op (|
                ">>",
                M.un_op (|
                  true,
                  "-",
                  Value.Integer 4267
                |),
                Value.Integer 0
              |)
            ],
            M.un_op (|
              true,
              "-",
              Value.Integer 4267
            |)
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition g2 (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.return_ (|
          M.bin_op (|
            "==",
            Value.Tuple [
              M.bin_op (|
                ">>",
                M.un_op (|
                  true,
                  "-",
                  Value.Integer 4267
                |),
                Value.Integer 1
              |)
            ],
            M.un_op (|
              true,
              "-",
              Value.Integer 2134
            |)
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition g3 (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.return_ (|
          M.bin_op (|
            "==",
            Value.Tuple [
              M.bin_op (|
                ">>",
                M.un_op (|
                  true,
                  "-",
                  Value.Integer 4267
                |),
                Value.Integer 4
              |)
            ],
            M.un_op (|
              true,
              "-",
              Value.Integer 267
            |)
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition g4 (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.return_ (|
          M.bin_op (|
            "==",
            Value.Tuple [
              M.bin_op (|
                ">>",
                M.un_op (|
                  true,
                  "-",
                  Value.Integer 4267
                |),
                Value.Integer 8
              |)
            ],
            M.un_op (|
              true,
              "-",
              Value.Integer 17
            |)
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition g5 (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.return_ (|
          M.bin_op (|
            "==",
            Value.Tuple [
              M.bin_op (|
                ">>",
                M.un_op (|
                  true,
                  "-",
                  Value.Integer 4267
                |),
                Value.Integer 16
              |)
            ],
            M.un_op (|
              true,
              "-",
              Value.Integer 1
            |)
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition g6 (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.return_ (|
          M.bin_op (|
            "==",
            Value.Tuple [
              M.bin_op (|
                ">>",
                M.un_op (|
                  true,
                  "-",
                  Value.Integer 4267
                |),
                Value.Integer 17
              |)
            ],
            M.un_op (|
              true,
              "-",
              Value.Integer 1
            |)
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.
