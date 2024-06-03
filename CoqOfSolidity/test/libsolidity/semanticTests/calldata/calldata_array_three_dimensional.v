(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Pragma abicoderv2 *)

(* Contract *)
Module C.
  Definition f (α : list Value.t) : M :=
    match α with
    | [x, i, j, k] =>
      let _ :=
        M.assign (|
          "=",
          M.get_name (| "a" |),
          M.member_access (|
            M.get_name (| "x" |),
            "length"
          |)
        |) in
      let _ :=
        M.assign (|
          "=",
          M.get_name (| "b" |),
          M.member_access (|
            M.index_access (|
              M.get_name (| "x" |),
              Some (M.get_name (| "i" |))
            |),
            "length"
          |)
        |) in
      let _ :=
        M.assign (|
          "=",
          M.get_name (| "c" |),
          M.member_access (|
            M.index_access (|
              M.index_access (|
                M.get_name (| "x" |),
                Some (M.get_name (| "i" |))
              |),
              Some (M.get_name (| "j" |))
            |),
            "length"
          |)
        |) in
      let _ :=
        M.assign (|
          "=",
          M.get_name (| "d" |),
          M.index_access (|
            M.index_access (|
              M.index_access (|
                M.get_name (| "x" |),
                Some (M.get_name (| "i" |))
              |),
              Some (M.get_name (| "j" |))
            |),
            Some (M.get_name (| "k" |))
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.
