(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Contract *)
Module I.
  Definition a (α : list Value.t) : M :=
    match α with
    | [] =>
      not implemented
    | _ => M.impossible "invalid number of parameters"
    end.
End I.


(* Contract *)
Module V.
  Definition b (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.return_ (|
          M.call (|
            M.get_name (| "a" |),
            []
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End V.
