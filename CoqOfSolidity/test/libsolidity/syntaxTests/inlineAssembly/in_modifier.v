(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Contract *)
Module test.
  (* Beginning of a node! *)
id: 9
src: 20:97:0
nodeType: ModifierDefinition
name: m
nameLocation: 29:1:0
documentation: 
visibility: internal
parameters: ParameterList.make []
virtual: 0
overrides: 
body: let _ :=
    M.define (|
      [ "a" ],
      Value.Integer 1
    |) in
  let _ :=
    (* Beginning of a node! *)
id: 6
src: 61:39:0
nodeType: InlineAssembly
AST: TODO YulJson
externalReferences: src: 84:1:0declaration: 3isSlot: isOffset: alueSize: 
evmVersion: cancun
 in
  let _ :=
    (* Beginning of a node! *)
id: 7
src: 109:1:0
nodeType: PlaceholderStatement
 in
  Value.Tuple []


  Definition f (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
         in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End test.
