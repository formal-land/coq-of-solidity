(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Contract *)
Module C.
  Definition x : Value.t :=
    M.bin_op (|
      "-",
      M.member_access (|
        M.get_name (| "msg" |),
        "value"
      |),
      Value.Integer 10
    |).

  Definition  (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
         in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.


(* Contract *)
Module D.
  Definition f (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        let _ :=
          M.call (|
            NewExpression Ty.path "C"
,
            []
          |) in
        Value.Tuple [] in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition g (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.return_ (|
          M.call (|
            M.member_access (|
              Value.Tuple [
                M.call (|
                  FunctionCallOptions NewExpression Ty.path "C"
 [value, ] Value.Integer 11
,
                  []
                |)
              ],
              "x"
            |),
            []
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End D.
