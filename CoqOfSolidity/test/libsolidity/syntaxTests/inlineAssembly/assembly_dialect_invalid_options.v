(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

Definition f (α : list Value.t) : M :=
  match α with
  | [] =>
    let _ :=
      (* Beginning of a node! *)
id: 3
src: 24:41:0
nodeType: InlineAssembly
AST: TODO YulJson
externalReferences: 
evmVersion: cancun
flags: [a, b, c, c, ]
 in
    Value.Tuple []
  | _ => M.impossible "invalid number of parameters"
  end.