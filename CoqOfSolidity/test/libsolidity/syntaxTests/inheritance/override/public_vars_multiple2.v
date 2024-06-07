(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Contract *)
Module A.
  Definition foo (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.return_ (|
          Value.Integer 4
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition foo (α : list Value.t) : M :=
    match α with
    | [_] =>
      let _ :=
        M.return_ (|
          Value.Integer 4
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition foo (α : list Value.t) : M :=
    match α with
    | [_, _] =>
      let _ :=
         in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End A.


(* Contract *)
Module X.
  Definition foo : Value.t :=
    undefined.
End X.
