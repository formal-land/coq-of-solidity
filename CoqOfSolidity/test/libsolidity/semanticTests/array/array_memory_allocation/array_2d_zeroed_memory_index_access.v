(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Contract *)
Module C.
  Definition test1 : Value.t :=
    undefined.

  Definition test2 : Value.t :=
    undefined.

  Definition test3 : Value.t :=
    undefined.

  Definition test4 : Value.t :=
    undefined.

  Definition test5 : Value.t :=
    undefined.

  Definition test6 : Value.t :=
    undefined.

  Definition test7 : Value.t :=
    undefined.

  Definition map : Value.t :=
    undefined.

  Definition set (α : list Value.t) : M :=
    match α with
    | [s, n, m, a, b] =>
      let _ :=
        M.assign (|
          "=",
          M.index_access (|
            M.get_name (| "map" |),
            Some (M.get_name (| "s" |))
          |),
          Value.Integer 0
        |) in
      let _ :=
        M.define (|
          [ "x" ],
          M.call (|
            NewExpression Ty.array (Ty.array (Ty.path "uint") None) None
,
            [
              M.get_name (| "n" |)
            ]
          |)
        |) in
      let _ :=
        M.for_ (|
          M.define (|
            [ "i" ],
            Value.Integer 0
          |),
          M.bin_op (|
            "<",
            M.get_name (| "i" |),
            M.get_name (| "n" |)
          |),
          M.un_op (|
            true,
            "++",
            M.get_name (| "i" |)
          |),
          M.assign (|
            "=",
            M.index_access (|
              M.get_name (| "x" |),
              Some (M.get_name (| "i" |))
            |),
            M.call (|
              NewExpression Ty.array (Ty.path "uint") None
,
              [
                M.get_name (| "m" |)
              ]
            |)
          |)
        |) in
      let _ :=
        M.return_ (|
          M.index_access (|
            M.index_access (|
              M.get_name (| "x" |),
              Some (M.get_name (| "a" |))
            |),
            Some (M.get_name (| "b" |))
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.
