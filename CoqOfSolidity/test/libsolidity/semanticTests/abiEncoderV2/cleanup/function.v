(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Pragma abicoderv2 *)

(* Contract *)
Module C.
  (* Struct S *)

  Definition ggg (α : list Value.t) : M :=
    match α with
    | [x] =>
      let _ :=
        (* Beginning of a node! *)
id: 15
src: 172:33:0
nodeType: InlineAssembly
AST: TODO YulJson
externalReferences: src: 183:1:0declaration: 13isSlot: isOffset: alueSize: 
evmVersion: cancun
 in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition h (α : list Value.t) : M :=
    match α with
    | [x] =>
      let _ :=
        M.member_access (|
          M.get_name (| "x" |),
          "f"
        |) in
      let _ :=
        (* Beginning of a node! *)
id: 29
src: 330:33:0
nodeType: InlineAssembly
AST: TODO YulJson
externalReferences: src: 341:1:0declaration: 23isSlot: isOffset: alueSize: 
evmVersion: cancun
 in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition dummy (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
         in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition ffff (α : list Value.t) : M :=
    match α with
    | [a] =>
      let _ :=
        M.define (|
          [ "s" ],
          M.call (|
            M.get_name (| "S" |),
            [
              M.member_access (|
                M.get_name (| "this" |),
                "dummy"
              |)
            ]
          |)
        |) in
      let _ :=
        (* Beginning of a node! *)
id: 52
src: 519:25:0
nodeType: InlineAssembly
AST: TODO YulJson
externalReferences: src: 540:1:0declaration: 37isSlot: isOffset: alueSize: src: 537:1:0declaration: 46isSlot: isOffset: alueSize: 
evmVersion: cancun
 in
      let _ :=
        M.return_ (|
          Value.Tuple [
            M.call (|
              M.member_access (|
                M.get_name (| "this" |),
                "ggg"
              |),
              [
                M.member_access (|
                  M.get_name (| "s" |),
                  "f"
                |)
              ]
            |),
            M.call (|
              M.member_access (|
                M.get_name (| "this" |),
                "h"
              |),
              [
                M.get_name (| "s" |)
              ]
            |)
          ]
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.
