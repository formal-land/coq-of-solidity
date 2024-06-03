(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Contract *)
Module C.
  (* Error E *)

  Definition r (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        (* Beginning of a node! *)
id: 9
src: 88:40:0
nodeType: InlineAssembly
AST: TODO YulJson
externalReferences: 
evmVersion: cancun
 in
      let _ :=
        M.return_ (|
          Value.Integer 42
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition f (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.call (|
          M.get_name (| "require" |),
          [
            Value.Bool false,
            M.call (|
              M.get_name (| "E" |),
              [
                M.call (|
                  M.get_name (| "r" |),
                  []
                |)
              ]
            |)
          ]
        |) in
      let _ :=
        M.return_ (|
          Value.Integer 42
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition g (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.call (|
          M.get_name (| "require" |),
          [
            Value.Bool true,
            M.call (|
              M.get_name (| "E" |),
              [
                M.call (|
                  M.get_name (| "r" |),
                  []
                |)
              ]
            |)
          ]
        |) in
      let _ :=
        M.return_ (|
          Value.Integer 42
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.
