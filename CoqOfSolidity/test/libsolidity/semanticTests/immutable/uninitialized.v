(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Contract *)
Module C.
  Definition u : Value.t :=
    undefined.

  Definition b : Value.t :=
    undefined.

  Definition a : Value.t :=
    undefined.

  Definition get (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.return_ (|
          Value.Tuple [
            M.get_name (| "u" |),
            M.get_name (| "b" |),
            M.get_name (| "a" |)
          ]
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.
