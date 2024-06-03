(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Contract *)
Module C.
  Definition f (α : list Value.t) : M :=
    match α with
    | [a, b] =>
      let _ :=
        M.assign (|
          "=",
          M.get_name (| "x" |),
          M.bin_op (|
            "*",
            M.get_name (| "a" |),
            M.get_name (| "b" |)
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition g (α : list Value.t) : M :=
    match α with
    | [a, b] =>
      let _ :=
        M.assign (|
          "=",
          M.get_name (| "x" |),
          M.bin_op (|
            "*",
            M.get_name (| "a" |),
            M.get_name (| "b" |)
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition h (α : list Value.t) : M :=
    match α with
    | [a, b] =>
      let _ :=
        M.assign (|
          "=",
          M.get_name (| "x" |),
          M.bin_op (|
            "*",
            M.get_name (| "a" |),
            M.get_name (| "b" |)
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.
