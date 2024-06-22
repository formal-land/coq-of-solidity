(* Generated by solc *)
Require Import CoqOfSolidity.CoqOfSolidity.

Module B4.
  Definition name : string := "B4_22".

  Definition code : M.t BlockUnit.t :=
    M.scope (
      do* ltac:(M.monadic (
        M.function (|
          "allocate_unbounded",
          [],
          ["memPtr"],
          M.scope (
            do* ltac:(M.monadic (
              M.assign (|
                ["memPtr"],
                Some (M.call (|
                  "mload",
                  [
                    [Literal.number 64]
                  ]
                |))
              |)
            )) in
            M.pure BlockUnit.Tt
          )
        |)
      )) in
      do* ltac:(M.monadic (
        M.function (|
          "revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb",
          [],
          [],
          M.scope (
            do* ltac:(M.monadic (
              M.expr_stmt (|
                M.call (|
                  "revert",
                  [
                    [Literal.number 0];
                    [Literal.number 0]
                  ]
                |)
              |)
            )) in
            M.pure BlockUnit.Tt
          )
        |)
      )) in
      do* ltac:(M.monadic (
        M.scope (
          do* ltac:(M.monadic (
            M.expr_stmt (|
              M.call (|
                "mstore",
                [
                  [Literal.number 64];
                  M.call (|
                    "memoryguard",
                    [
                      [Literal.number 0x80]
                    ]
                  |)
                ]
              |)
            |)
          )) in
          do* ltac:(M.monadic (
            M.if_ (|
              M.call (|
                "callvalue",
                []
              |),
              M.scope (
                do* ltac:(M.monadic (
                  M.expr_stmt (|
                    M.call (|
                      "revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb",
                      []
                    |)
                  |)
                )) in
                M.pure BlockUnit.Tt
              )
            |)
          )) in
          do* ltac:(M.monadic (
            M.declare (|
              ["_1"],
              Some (M.call (|
                "allocate_unbounded",
                []
              |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.expr_stmt (|
              M.call (|
                "codecopy",
                [
                  M.get_var (| "_1" |);
                  M.call (|
                    "dataoffset",
                    [
                      [Literal.string 0x42345f32325f6465706c6f796564000000000000000000000000000000000000]
                    ]
                  |);
                  M.call (|
                    "datasize",
                    [
                      [Literal.string 0x42345f32325f6465706c6f796564000000000000000000000000000000000000]
                    ]
                  |)
                ]
              |)
            |)
          )) in
          do* ltac:(M.monadic (
            M.expr_stmt (|
              M.call (|
                "return",
                [
                  M.get_var (| "_1" |);
                  M.call (|
                    "datasize",
                    [
                      [Literal.string 0x42345f32325f6465706c6f796564000000000000000000000000000000000000]
                    ]
                  |)
                ]
              |)
            |)
          )) in
          M.pure BlockUnit.Tt
        )
      )) in
      M.pure BlockUnit.Tt
    ).

  Module deployed.
    Definition name : string := "B4_22_deployed".

    Definition code : M.t BlockUnit.t :=
      M.scope (
        do* ltac:(M.monadic (
          M.function (|
            "revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74",
            [],
            [],
            M.scope (
              do* ltac:(M.monadic (
                M.expr_stmt (|
                  M.call (|
                    "revert",
                    [
                      [Literal.number 0];
                      [Literal.number 0]
                    ]
                  |)
                |)
              )) in
              M.pure BlockUnit.Tt
            )
          |)
        )) in
        do* ltac:(M.monadic (
          M.scope (
            do* ltac:(M.monadic (
              M.expr_stmt (|
                M.call (|
                  "mstore",
                  [
                    [Literal.number 64];
                    M.call (|
                      "memoryguard",
                      [
                        [Literal.number 0x80]
                      ]
                    |)
                  ]
                |)
              |)
            )) in
            do* ltac:(M.monadic (
              M.expr_stmt (|
                M.call (|
                  "revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74",
                  []
                |)
              |)
            )) in
            M.pure BlockUnit.Tt
          )
        )) in
        M.pure BlockUnit.Tt
      ).

    Definition data : string :=
      "a26469706673582212209a83c89d4663f6cb039428959c4e9cdcf01cb31d76949c7044ec7a9d8f10a0eb64736f6c634300081b0033".
  End deployed.
End B4.
