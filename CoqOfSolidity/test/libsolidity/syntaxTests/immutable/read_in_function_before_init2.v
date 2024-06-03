(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Contract *)
Module C.
  Definition t : Value.t :=
    Value.Integer 2.

  Definition x : Value.t :=
    M.call (|
      M.get_name (| "f" |),
      []
    |).

  Definition f (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.return_ (|
          M.get_name (| "t" |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.
