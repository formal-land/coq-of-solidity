(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Contract *)
Module C.
  (* Beginning of a node! *)
id: 12
src: 17:74:0
nodeType: ModifierDefinition
name: mod1
nameLocation: 26:4:0
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
    M.define (|
      [ "b" ],
      Value.Integer 2
    |) in
  let _ :=
    (* Beginning of a node! *)
id: 10
src: 83:1:0
nodeType: PlaceholderStatement
 in
  Value.Tuple []


  (* Beginning of a node! *)
id: 21
src: 96:68:0
nodeType: ModifierDefinition
name: mod2
nameLocation: 105:4:0
documentation: 
visibility: internal
parameters: ParameterList.make [
    Definition a : Value.t :=
      undefined.
  ]
virtual: 0
overrides: 
body: let _ :=
    if M.get_name (| "a" |) then
      M.return_ (|
        Value.Tuple []
      |)
    else
      (* Beginning of a node! *)
id: 18
src: 156:1:0
nodeType: PlaceholderStatement
 in
  Value.Tuple []


  Definition f (α : list Value.t) : M :=
    match α with
    | [a] =>
      let _ :=
        M.return_ (|
          Value.Integer 3
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.
