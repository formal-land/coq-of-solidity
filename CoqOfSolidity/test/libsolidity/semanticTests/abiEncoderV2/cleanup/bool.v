(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Pragma abicoderv2 *)

(* Contract *)
Module C.
  Definition gggg (α : list Value.t) : M :=
    match α with
    | [x] =>
      let _ :=
        M.return_ (|
          M.get_name (| "x" |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition f (α : list Value.t) : M :=
    match α with
    | [a] =>
      let _ :=
        M.define (|
          [ "x" ],
          Value.Bool false
        |) in
      let _ :=
        (* Beginning of a node! *)
id: 22
src: 218:19:0
nodeType: InlineAssembly
AST: TODO YulJson
externalReferences: src: 234:1:0declaration: 13isSlot: isOffset: alueSize: src: 229:1:0declaration: 19isSlot: isOffset: alueSize: 
evmVersion: cancun
 in
      let _ :=
        M.return_ (|
          M.call (|
            M.member_access (|
              M.get_name (| "this" |),
              "gggg"
            |),
            [
              M.get_name (| "x" |)
            ]
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.
