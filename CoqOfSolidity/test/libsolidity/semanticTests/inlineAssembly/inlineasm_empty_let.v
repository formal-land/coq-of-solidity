(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Contract *)
Module C.
  Definition f (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        (* Beginning of a node! *)
id: 7
src: 68:55:0
nodeType: InlineAssembly
AST: TODO YulJson
externalReferences: src: 103:1:0declaration: 3isSlot: isOffset: alueSize: src: 113:1:0declaration: 5isSlot: isOffset: alueSize: 
evmVersion: cancun
 in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.
