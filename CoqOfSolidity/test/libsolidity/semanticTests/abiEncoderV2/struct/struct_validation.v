(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Pragma abicoderv2 *)

(* Contract *)
Module C.
  (* Struct S *)

  Definition f (α : list Value.t) : M :=
    match α with
    | [s] =>
      let _ :=
        (* Beginning of a node! *)
id: 20
src: 163:87:0
nodeType: InlineAssembly
AST: TODO YulJson
externalReferences: src: 177:1:0declaration: 14isSlot: isOffset: alueSize: src: 194:1:0declaration: 16isSlot: isOffset: alueSize: src: 222:1:0declaration: 18isSlot: isOffset: alueSize: src: 188:1:0declaration: 11isSlot: isOffset: alueSize: src: 209:1:0declaration: 11isSlot: isOffset: alueSize: src: 237:1:0declaration: 11isSlot: isOffset: alueSize: 
evmVersion: cancun
 in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.
