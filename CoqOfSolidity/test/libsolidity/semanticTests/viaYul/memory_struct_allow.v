(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Contract *)
Module C.
  (* Struct S *)

  Definition f (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        (* Beginning of a node! *)
id: 12
src: 142:226:0
nodeType: InlineAssembly
AST: TODO YulJson
externalReferences: 
evmVersion: cancun
 in
      let _ :=
        M.define (|
          [ "s" ],
          Value.Default
        |) in
      let _ :=
        M.return_ (|
          Value.Tuple [
            M.member_access (|
              M.get_name (| "s" |),
              "a"
            |),
            M.member_access (|
              M.get_name (| "s" |),
              "b"
            |)
          ]
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.
