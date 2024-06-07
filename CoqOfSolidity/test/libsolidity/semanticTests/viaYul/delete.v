(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Contract *)
Module C.
  Definition internal_func (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.return_ (|
          Value.Integer 1
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition call_internal_func (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.define (|
          [ "func" ],
          M.get_name (| "internal_func" |)
        |) in
      let _ :=
        M.return_ (|
          M.bin_op (|
            "==",
            M.call (|
              M.get_name (| "func" |),
              []
            |),
            M.call (|
              M.get_name (| "internal_func" |),
              []
            |)
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition call_deleted_internal_func (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.define (|
          [ "func" ],
          M.get_name (| "internal_func" |)
        |) in
      let _ :=
        M.un_op (|
          true,
          "delete",
          M.get_name (| "func" |)
        |) in
      let _ :=
        M.return_ (|
          M.bin_op (|
            "==",
            M.call (|
              M.get_name (| "func" |),
              []
            |),
            M.call (|
              M.get_name (| "internal_func" |),
              []
            |)
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.
