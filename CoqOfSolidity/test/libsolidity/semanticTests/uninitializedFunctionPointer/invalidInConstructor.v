(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Contract *)
Module C.
  Definition storedFn : Value.t :=
    undefined.

  Definition flag : Value.t :=
    undefined.

  Definition  (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        if M.un_op (|
          true,
          "!",
          M.get_name (| "flag" |)
        |) then
          let _ :=
            M.assign (|
              "=",
              M.get_name (| "flag" |),
              Value.Bool true
            |) in
          let _ :=
            M.define (|
              [ "invalid" ],
              Value.Default
            |) in
          let _ :=
            M.assign (|
              "=",
              M.get_name (| "storedFn" |),
              M.get_name (| "invalid" |)
            |) in
          let _ :=
            M.call (|
              M.get_name (| "invalid" |),
              []
            |) in
          Value.Tuple []
        else
          Value.Tuple [] in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition f (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
         in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.


(* Contract *)
Module Test.
  Definition f (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.call (|
          NewExpression Ty.path "C"
,
          []
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End Test.
