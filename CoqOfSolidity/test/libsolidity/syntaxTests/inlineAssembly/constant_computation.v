(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Contract *)
Module C.
  Definition x : Value.t :=
    M.bin_op (|
      "**",
      Value.Integer 2,
      Value.Integer 20
    |).

  Definition f (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        (* Beginning of a node! *)
id: 8
src: 81:43:0
nodeType: InlineAssembly
AST: TODO YulJson
externalReferences: src: 113:1:0declaration: 5isSlot: isOffset: alueSize: 
evmVersion: cancun
 in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.
