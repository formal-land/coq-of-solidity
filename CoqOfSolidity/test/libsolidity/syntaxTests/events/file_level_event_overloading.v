(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Event E *)

(* Event E *)

(* Event E *)

(* Event E *)

Definition f (α : list Value.t) : M :=
  match α with
  | [] =>
    let _ :=
      EmitStatement M.call (|
        M.get_name (| "E" |),
        []
      |)
 in
    let _ :=
      EmitStatement M.call (|
        M.get_name (| "E" |),
        [
          Value.Integer 1
        ]
      |)
 in
    let _ :=
      EmitStatement M.call (|
        M.get_name (| "E" |),
        [
          Value.Integer 1,
          Value.String "abc",
          Value.String "abc",
          Value.Bool true
        ]
      |)
 in
    let _ :=
      EmitStatement M.call (|
        M.get_name (| "E" |),
        [
          Value.Integer 1,
          Value.Integer 2,
          Value.Integer 3
        ]
      |)
 in
    Value.Tuple []
  | _ => M.impossible "invalid number of parameters"
  end.