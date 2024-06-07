(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Contract *)
Module C.
  Definition g (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
         in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition h (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
         in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition test_function (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.call (|
          M.get_name (| "assert" |),
          [
            M.bin_op (|
              "&&",
              M.bin_op (|
                "&&",
                M.bin_op (|
                  "==",
                  M.member_access (|
                    M.member_access (|
                      M.get_name (| "this" |),
                      "g"
                    |),
                    "address"
                  |),
                  M.member_access (|
                    M.member_access (|
                      M.get_name (| "this" |),
                      "g"
                    |),
                    "address"
                  |)
                |),
                M.bin_op (|
                  "==",
                  M.member_access (|
                    FunctionCallOptions M.member_access (|
                      M.get_name (| "this" |),
                      "g"
                    |) [gas, ] Value.Integer 42
,
                    "address"
                  |),
                  M.member_access (|
                    M.member_access (|
                      M.get_name (| "this" |),
                      "g"
                    |),
                    "address"
                  |)
                |)
              |),
              M.bin_op (|
                "==",
                M.member_access (|
                  FunctionCallOptions M.member_access (|
                    M.get_name (| "this" |),
                    "g"
                  |) [gas, ] Value.Integer 42
,
                  "selector"
                |),
                M.member_access (|
                  M.member_access (|
                    M.get_name (| "this" |),
                    "g"
                  |),
                  "selector"
                |)
              |)
            |)
          ]
        |) in
      let _ :=
        M.call (|
          M.get_name (| "assert" |),
          [
            M.bin_op (|
              "&&",
              M.bin_op (|
                "&&",
                M.bin_op (|
                  "==",
                  M.member_access (|
                    M.member_access (|
                      M.get_name (| "this" |),
                      "h"
                    |),
                    "address"
                  |),
                  M.member_access (|
                    M.member_access (|
                      M.get_name (| "this" |),
                      "h"
                    |),
                    "address"
                  |)
                |),
                M.bin_op (|
                  "==",
                  M.member_access (|
                    FunctionCallOptions M.member_access (|
                      M.get_name (| "this" |),
                      "h"
                    |) [gas, ] Value.Integer 42
,
                    "address"
                  |),
                  M.member_access (|
                    M.member_access (|
                      M.get_name (| "this" |),
                      "h"
                    |),
                    "address"
                  |)
                |)
              |),
              M.bin_op (|
                "==",
                M.member_access (|
                  FunctionCallOptions M.member_access (|
                    M.get_name (| "this" |),
                    "h"
                  |) [gas, ] Value.Integer 42
,
                  "selector"
                |),
                M.member_access (|
                  M.member_access (|
                    M.get_name (| "this" |),
                    "h"
                  |),
                  "selector"
                |)
              |)
            |)
          ]
        |) in
      let _ :=
        M.call (|
          M.get_name (| "assert" |),
          [
            M.bin_op (|
              "&&",
              M.bin_op (|
                "==",
                M.member_access (|
                  FunctionCallOptions M.member_access (|
                    M.get_name (| "this" |),
                    "h"
                  |) [gas, value, ] Value.Integer 42, Value.Integer 5
,
                  "address"
                |),
                M.member_access (|
                  M.member_access (|
                    M.get_name (| "this" |),
                    "h"
                  |),
                  "address"
                |)
              |),
              M.bin_op (|
                "==",
                M.member_access (|
                  FunctionCallOptions M.member_access (|
                    M.get_name (| "this" |),
                    "h"
                  |) [gas, value, ] Value.Integer 42, Value.Integer 5
,
                  "selector"
                |),
                M.member_access (|
                  M.member_access (|
                    M.get_name (| "this" |),
                    "h"
                  |),
                  "selector"
                |)
              |)
            |)
          ]
        |) in
      let _ :=
        M.return_ (|
          Value.Bool true
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.
