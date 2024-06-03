(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Contract *)
Module Other.
  Definition addTwo (α : list Value.t) : M :=
    match α with
    | [x] =>
      let _ :=
        M.return_ (|
          M.bin_op (|
            "+",
            M.get_name (| "x" |),
            Value.Integer 2
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End Other.


(* Contract *)
Module C.
  Definition ev : Value.t :=
    undefined.

  Definition x : Value.t :=
    undefined.

  Definition store (α : list Value.t) : M :=
    match α with
    | [y] =>
      let _ :=
        M.assign (|
          "=",
          M.get_name (| "x" |),
          M.get_name (| "y" |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition eval (α : list Value.t) : M :=
    match α with
    | [y] =>
      let _ :=
        M.return_ (|
          M.call (|
            M.get_name (| "y" |),
            [
              Value.Integer 7
            ]
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition t (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.call (|
          M.member_access (|
            M.get_name (| "this" |),
            "store"
          |),
          [
            M.member_access (|
              Value.Tuple [
                M.call (|
                  NewExpression Ty.path "Other"
,
                  []
                |)
              ],
              "addTwo"
            |)
          ]
        |) in
      let _ :=
        M.return_ (|
          M.call (|
            M.get_name (| "ev" |),
            [
              M.get_name (| "x" |)
            ]
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.
