(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Contract *)
Module C.
  Definition f (α : list Value.t) : M :=
    match α with
    | [n] =>
      let _ :=
        M.define (|
          [ "a" ],
          M.call (|
            NewExpression Ty.array (Ty.array (Ty.array (Ty.path "uint") None) None) None
,
            [
              Value.Integer 2
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
            Value.Integer 2
          |),
          M.un_op (|
            true,
            "++",
            M.get_name (| "i" |)
          |),
          let _ :=
            M.assign (|
              "=",
              M.index_access (|
                M.get_name (| "a" |),
                Some (M.get_name (| "i" |))
              |),
              M.call (|
                NewExpression Ty.array (Ty.array (Ty.path "uint") None) None
,
                [
                  Value.Integer 3
                ]
              |)
            |) in
          let _ :=
            M.for_ (|
              M.define (|
                [ "j" ],
                Value.Integer 0
              |),
              M.bin_op (|
                "<",
                M.get_name (| "j" |),
                Value.Integer 3
              |),
              M.un_op (|
                true,
                "++",
                M.get_name (| "j" |)
              |),
              M.assign (|
                "=",
                M.index_access (|
                  M.index_access (|
                    M.get_name (| "a" |),
                    Some (M.get_name (| "i" |))
                  |),
                  Some (M.get_name (| "j" |))
                |),
                M.call (|
                  NewExpression Ty.array (Ty.path "uint") None
,
                  [
                    Value.Integer 4
                  ]
                |)
              |)
            |) in
          Value.Tuple []
        |) in
      let _ :=
        M.assign (|
          "=",
          M.index_access (|
            M.index_access (|
              M.index_access (|
                M.get_name (| "a" |),
                Some (Value.Integer 1)
              |),
              Some (Value.Integer 1)
            |),
            Some (Value.Integer 1)
          |),
          M.get_name (| "n" |)
        |) in
      let _ :=
        M.define (|
          [ "b" ],
          M.index_access (|
            M.get_name (| "a" |),
            Some (Value.Integer 1)
          |)
        |) in
      let _ :=
        M.define (|
          [ "c" ],
          M.index_access (|
            M.get_name (| "b" |),
            Some (Value.Integer 1)
          |)
        |) in
      let _ :=
        M.return_ (|
          M.index_access (|
            M.get_name (| "c" |),
            Some (Value.Integer 1)
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.
