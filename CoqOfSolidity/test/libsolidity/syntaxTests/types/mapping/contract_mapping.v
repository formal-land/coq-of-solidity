(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Interface *)
Module I.
  
End I.


(* Contract *)
Module J.
  
End J.


(* Contract *)
Module C.
  Definition i : Value.t :=
    undefined.

  Definition j : Value.t :=
    undefined.

  Definition f (α : list Value.t) : M :=
    match α with
    | [x, y] =>
      let _ :=
        M.return_ (|
          Value.Tuple [
            M.index_access (|
              M.get_name (| "i" |),
              Some (M.get_name (| "x" |))
            |),
            M.index_access (|
              M.get_name (| "j" |),
              Some (M.get_name (| "y" |))
            |)
          ]
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.
