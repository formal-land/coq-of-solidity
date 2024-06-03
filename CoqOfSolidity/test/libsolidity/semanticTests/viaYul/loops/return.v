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
          M.get_name (| "x" |),
          Value.Integer 1
        |) in
      let _ :=
        M.define (|
          [ "a" ],
          Value.Default
        |) in
      let _ :=
        M.for_ (|
          Value.Tuple [],
          M.bin_op (|
            "<",
            M.get_name (| "a" |),
            Value.Integer 10
          |),
          M.assign (|
            "=",
            M.get_name (| "a" |),
            M.bin_op (|
              "+",
              M.get_name (| "a" |),
              Value.Integer 1
            |)
          |),
          let _ :=
            M.return_ (|
              M.get_name (| "x" |)
            |) in
          let _ :=
            M.assign (|
              "=",
              M.get_name (| "x" |),
              M.bin_op (|
                "+",
                M.get_name (| "x" |),
                M.get_name (| "x" |)
              |)
            |) in
          Value.Tuple []
        |) in
      let _ :=
        M.assign (|
          "=",
          M.get_name (| "x" |),
          M.bin_op (|
            "+",
            M.get_name (| "x" |),
            M.get_name (| "a" |)
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition g (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.assign (|
          "=",
          M.get_name (| "x" |),
          Value.Integer 1
        |) in
      let _ :=
        M.define (|
          [ "a" ],
          Value.Default
        |) in
      let _ :=
        M.while (|
          WhileKind.While,
          M.bin_op (|
            "<",
            M.get_name (| "a" |),
            Value.Integer 10
          |),
          let _ :=
            M.return_ (|
              M.get_name (| "x" |)
            |) in
          let _ :=
            M.assign (|
              "=",
              M.get_name (| "x" |),
              M.bin_op (|
                "+",
                M.get_name (| "x" |),
                M.get_name (| "x" |)
              |)
            |) in
          let _ :=
            M.assign (|
              "=",
              M.get_name (| "a" |),
              M.bin_op (|
                "+",
                M.get_name (| "a" |),
                Value.Integer 1
              |)
            |) in
          Value.Tuple []
        |) in
      let _ :=
        M.assign (|
          "=",
          M.get_name (| "x" |),
          M.bin_op (|
            "+",
            M.get_name (| "x" |),
            M.get_name (| "a" |)
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition h (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.assign (|
          "=",
          M.get_name (| "x" |),
          Value.Integer 1
        |) in
      let _ :=
        M.while (|
          WhileKind.DoWhile,
          M.bin_op (|
            "<",
            M.get_name (| "x" |),
            Value.Integer 3
          |),
          let _ :=
            M.assign (|
              "=",
              M.get_name (| "x" |),
              M.bin_op (|
                "+",
                M.get_name (| "x" |),
                Value.Integer 1
              |)
            |) in
          let _ :=
            M.return_ (|
              M.get_name (| "x" |)
            |) in
          Value.Tuple []
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.
