(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Contract *)
Module Base.
  Definition  (α : list Value.t) : M :=
    match α with
    | [_] =>
      let _ :=
         in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End Base.


(* Contract *)
Module Derived.
  
End Derived.


(* Contract *)
Module Derived2.
  
End Derived2.
