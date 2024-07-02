(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

Module test.
  Definition code : Code.t := {|
    Code.name := "test_22";
    Code.hex_name := 0x746573745f323200000000000000000000000000000000000000000000000000;
    Code.functions :=
      [
        
      ];
    Code.body :=
      M.scope (
        do! ltac:(M.monadic (
          M.scope (
            do! ltac:(M.monadic (
              M.declare (|
                ["_1"],
                Some (M.call_function (|
                  "memoryguard",
                  [
                    [Literal.number 0x80]
                  ]
                |))
              |)
            )) in
            do! ltac:(M.monadic (
              M.expr_stmt (|
                M.call_function (|
                  "mstore",
                  [
                    [Literal.number 64];
                    M.get_var (| "_1" |)
                  ]
                |)
              |)
            )) in
            do! ltac:(M.monadic (
              M.if_ (|
                M.call_function (|
                  "callvalue",
                  []
                |),
                M.scope (
                  do! ltac:(M.monadic (
                    M.expr_stmt (|
                      M.call_function (|
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
            do! ltac:(M.monadic (
              M.declare (|
                ["_2"],
                Some (M.call_function (|
                  "datasize",
                  [
                    [Literal.string 0x746573745f32325f6465706c6f79656400000000000000000000000000000000]
                  ]
                |))
              |)
            )) in
            do! ltac:(M.monadic (
              M.expr_stmt (|
                M.call_function (|
                  "codecopy",
                  [
                    M.get_var (| "_1" |);
                    M.call_function (|
                      "dataoffset",
                      [
                        [Literal.string 0x746573745f32325f6465706c6f79656400000000000000000000000000000000]
                      ]
                    |);
                    M.get_var (| "_2" |)
                  ]
                |)
              |)
            )) in
            do! ltac:(M.monadic (
              M.expr_stmt (|
                M.call_function (|
                  "return",
                  [
                    M.get_var (| "_1" |);
                    M.get_var (| "_2" |)
                  ]
                |)
              |)
            )) in
            M.pure BlockUnit.Tt
          )
        )) in
        M.pure BlockUnit.Tt
      );
  |}.

  Module deployed.
    Definition code : Code.t := {|
      Code.name := "test_22_deployed";
      Code.hex_name := 0x746573745f32325f6465706c6f79656400000000000000000000000000000000;
      Code.functions :=
        [
          
        ];
      Code.body :=
        M.scope (
          do! ltac:(M.monadic (
            M.scope (
              do! ltac:(M.monadic (
                M.expr_stmt (|
                  M.call_function (|
                    "mstore",
                    [
                      [Literal.number 64];
                      M.call_function (|
                        "memoryguard",
                        [
                          [Literal.number 0x80]
                        ]
                      |)
                    ]
                  |)
                |)
              )) in
              do! ltac:(M.monadic (
                M.if_ (|
                  M.call_function (|
                    "iszero",
                    [
                      M.call_function (|
                        "lt",
                        [
                          M.call_function (|
                            "calldatasize",
                            []
                          |);
                          [Literal.number 4]
                        ]
                      |)
                    ]
                  |),
                  M.scope (
                    do! ltac:(M.monadic (
                      M.if_ (|
                        M.call_function (|
                          "eq",
                          [
                            [Literal.number 0x26121ff0];
                            M.call_function (|
                              "shr",
                              [
                                [Literal.number 224];
                                M.call_function (|
                                  "calldataload",
                                  [
                                    [Literal.number 0]
                                  ]
                                |)
                              ]
                            |)
                          ]
                        |),
                        M.scope (
                          do! ltac:(M.monadic (
                            M.if_ (|
                              M.call_function (|
                                "callvalue",
                                []
                              |),
                              M.scope (
                                do! ltac:(M.monadic (
                                  M.expr_stmt (|
                                    M.call_function (|
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
                          do! ltac:(M.monadic (
                            M.if_ (|
                              M.call_function (|
                                "slt",
                                [
                                  M.call_function (|
                                    "add",
                                    [
                                      M.call_function (|
                                        "calldatasize",
                                        []
                                      |);
                                      M.call_function (|
                                        "not",
                                        [
                                          [Literal.number 3]
                                        ]
                                      |)
                                    ]
                                  |);
                                  [Literal.number 0]
                                ]
                              |),
                              M.scope (
                                do! ltac:(M.monadic (
                                  M.expr_stmt (|
                                    M.call_function (|
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
                          do! ltac:(M.monadic (
                            M.declare (|
                              ["var_ret"],
                              Some ([Literal.number 0])
                            |)
                          )) in
                          do! ltac:(M.monadic (
                            M.assign (|
                              ["var_ret"],
                              Some ([Literal.number 0x01])
                            |)
                          )) in
                          do! ltac:(M.monadic (
                            do!
                              M.scope (
                                M.pure BlockUnit.Tt
                              ) in
                            ltac:(M.monadic (
                              M.for_ (|
                                ltac:(M.monadic (
                                  [Literal.number 0x01]
                                )),
                                M.scope (
                                  M.pure BlockUnit.Tt
                                ),
                                M.scope (
                                  do! ltac:(M.monadic (
                                    M.declare (|
                                      ["sum"],
                                      Some (M.call_function (|
                                        "add",
                                        [
                                          M.get_var (| "var_ret" |);
                                          [Literal.number 0x01]
                                        ]
                                      |))
                                    |)
                                  )) in
                                  do! ltac:(M.monadic (
                                    M.if_ (|
                                      M.call_function (|
                                        "gt",
                                        [
                                          M.get_var (| "var_ret" |);
                                          M.get_var (| "sum" |)
                                        ]
                                      |),
                                      M.scope (
                                        do! ltac:(M.monadic (
                                          M.expr_stmt (|
                                            M.call_function (|
                                              "mstore",
                                              [
                                                [Literal.number 0];
                                                M.call_function (|
                                                  "shl",
                                                  [
                                                    [Literal.number 224];
                                                    [Literal.number 0x4e487b71]
                                                  ]
                                                |)
                                              ]
                                            |)
                                          |)
                                        )) in
                                        do! ltac:(M.monadic (
                                          M.expr_stmt (|
                                            M.call_function (|
                                              "mstore",
                                              [
                                                [Literal.number 4];
                                                [Literal.number 0x11]
                                              ]
                                            |)
                                          |)
                                        )) in
                                        do! ltac:(M.monadic (
                                          M.expr_stmt (|
                                            M.call_function (|
                                              "revert",
                                              [
                                                [Literal.number 0];
                                                [Literal.number 0x24]
                                              ]
                                            |)
                                          |)
                                        )) in
                                        M.pure BlockUnit.Tt
                                      )
                                    |)
                                  )) in
                                  do! ltac:(M.monadic (
                                    M.assign (|
                                      ["var_ret"],
                                      Some (M.get_var (| "sum" |))
                                    |)
                                  )) in
                                  do! ltac:(M.monadic (
                                    M.if_ (|
                                      M.call_function (|
                                        "iszero",
                                        [
                                          M.call_function (|
                                            "lt",
                                            [
                                              M.get_var (| "sum" |);
                                              [Literal.number 0x0a]
                                            ]
                                          |)
                                        ]
                                      |),
                                      M.scope (
                                        do! ltac:(M.monadic (
                                          M.break (||)
                                        )) in
                                        M.pure BlockUnit.Tt
                                      )
                                    |)
                                  )) in
                                  M.pure BlockUnit.Tt
                                )
                              |)
                            ))
                          )) in
                          do! ltac:(M.monadic (
                            M.declare (|
                              ["memPos"],
                              Some (M.call_function (|
                                "mload",
                                [
                                  [Literal.number 64]
                                ]
                              |))
                            |)
                          )) in
                          do! ltac:(M.monadic (
                            M.expr_stmt (|
                              M.call_function (|
                                "mstore",
                                [
                                  M.get_var (| "memPos" |);
                                  M.get_var (| "var_ret" |)
                                ]
                              |)
                            |)
                          )) in
                          do! ltac:(M.monadic (
                            M.expr_stmt (|
                              M.call_function (|
                                "return",
                                [
                                  M.get_var (| "memPos" |);
                                  [Literal.number 32]
                                ]
                              |)
                            |)
                          )) in
                          M.pure BlockUnit.Tt
                        )
                      |)
                    )) in
                    M.pure BlockUnit.Tt
                  )
                |)
              )) in
              do! ltac:(M.monadic (
                M.expr_stmt (|
                  M.call_function (|
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
          )) in
          M.pure BlockUnit.Tt
        );
    |}.
  End deployed.
End test.

Import Ltac2.

Definition codes : list Code.t :=
  ltac2:(
    let codes := Code.get_codes () in
    exact $codes
  ).
