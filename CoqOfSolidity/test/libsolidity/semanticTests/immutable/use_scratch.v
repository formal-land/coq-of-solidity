(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Contract *)
Module C.
  Definition x : Value.t :=
    undefined.

  Definition y : Value.t :=
    undefined.

  Definition m : Value.t :=
    undefined.

  Definition  (α : list Value.t) : M :=
    match α with
    | [_a] =>
      let _ :=
        M.assign (|
          "=",
          M.get_name (| "x" |),
          Value.Integer 42
        |) in
      let _ :=
        M.assign (|
          "=",
          M.get_name (| "y" |),
          Value.Integer 23
        |) in
      let _ :=
        M.assign (|
          "=",
          M.index_access (|
            M.get_name (| "m" |),
            Some (M.get_name (| "_a" |))
          |),
          Value.Integer 7
        |) in
      let _ :=
        M.call (|
          NewExpression Ty.array (Ty.path "uint") None
,
          [
            Value.Integer 4
          ]
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition f (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.return_ (|
          Value.Tuple [
            M.bin_op (|
              "+",
              M.get_name (| "x" |),
              M.get_name (| "x" |)
            |),
            M.get_name (| "y" |)
          ]
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.
