(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Contract *)
Module C.
  Definition f (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.define (|
          [ "a" ],
          Value.Default
        |) in
      let _ :=
        M.define (|
          [ "b" ],
          Value.Default
        |) in
      let _ :=
        M.define (|
          [ "c" ],
          Value.Default
        |) in
      let _ :=
        (* Beginning of a node! *)
id: 14
src: 125:77:0
nodeType: InlineAssembly
AST: TODO YulJson
externalReferences: src: 148:1:0declaration: 6isSlot: isOffset: alueSize: src: 167:1:0declaration: 9isSlot: isOffset: alueSize: src: 186:1:0declaration: 12isSlot: isOffset: alueSize: 
evmVersion: cancun
 in
      let _ :=
        M.assign (|
          "=",
          M.get_name (| "x" |),
          M.bin_op (|
            "+",
            M.bin_op (|
              "+",
              M.get_name (| "a" |),
              M.get_name (| "b" |)
            |),
            M.get_name (| "c" |)
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.
