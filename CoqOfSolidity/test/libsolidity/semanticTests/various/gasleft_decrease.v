(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Contract *)
Module C.
  Definition v : Value.t :=
    undefined.

  Definition f (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.define (|
          [ "startGas" ],
          M.call (|
            M.get_name (| "gasleft" |),
            []
          |)
        |) in
      let _ :=
        M.un_op (|
          false,
          "++",
          M.get_name (| "v" |)
        |) in
      let _ :=
        M.call (|
          M.get_name (| "assert" |),
          [
            M.bin_op (|
              ">",
              M.get_name (| "startGas" |),
              M.call (|
                M.get_name (| "gasleft" |),
                []
              |)
            |)
          ]
        |) in
      let _ :=
        M.return_ (|
          Value.Bool true
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition g (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.define (|
          [ "startGas" ],
          M.call (|
            M.get_name (| "gasleft" |),
            []
          |)
        |) in
      let _ :=
        M.call (|
          M.get_name (| "assert" |),
          [
            M.bin_op (|
              ">",
              M.get_name (| "startGas" |),
              M.call (|
                M.get_name (| "gasleft" |),
                []
              |)
            |)
          ]
        |) in
      let _ :=
        M.return_ (|
          Value.Bool true
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.
