(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Contract *)
Module test.
  Definition data : Value.t :=
    undefined.

  Definition dynamicData : Value.t :=
    undefined.

  Definition  (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.assign (|
          "=",
          M.index_access (|
            M.index_access (|
              M.get_name (| "data" |),
              Some (Value.Integer 2)
            |),
            Some (Value.Integer 2)
          |),
          Value.Integer 8
        |) in
      let _ :=
        M.for_ (|
          M.define (|
            [ "i" ],
            Value.Integer 0
          |),
          M.bin_op (|
            "<",
            M.get_name (| "i" |),
            Value.Integer 3
          |),
          M.un_op (|
            false,
            "++",
            M.get_name (| "i" |)
          |),
          M.call (|
            M.member_access (|
              M.index_access (|
                M.get_name (| "dynamicData" |),
                Some (Value.Integer 2)
              |),
              "push"
            |),
            []
          |)
        |) in
      let _ :=
        M.assign (|
          "=",
          M.index_access (|
            M.index_access (|
              M.get_name (| "dynamicData" |),
              Some (Value.Integer 2)
            |),
            Some (Value.Integer 2)
          |),
          Value.Integer 8
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End test.
