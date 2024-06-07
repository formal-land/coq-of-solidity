(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Contract *)
Module Test.
  Definition bytesToUint (α : list Value.t) : M :=
    match α with
    | [s] =>
      let _ :=
        M.return_ (|
          M.call (|
            Ty.path "uint64",
            [
              M.call (|
                Ty.path "uint32",
                [
                  M.get_name (| "s" |)
                ]
              |)
            ]
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End Test.
