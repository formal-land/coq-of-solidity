(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

Module C.
  Definition code : Code.t := {|
    Code.name := "C_34";
    Code.hex_name := 0x435f333400000000000000000000000000000000000000000000000000000000;
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
                    [Literal.string 0x435f33345f6465706c6f79656400000000000000000000000000000000000000]
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
                        [Literal.string 0x435f33345f6465706c6f79656400000000000000000000000000000000000000]
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
      Code.name := "C_34_deployed";
      Code.hex_name := 0x435f33345f6465706c6f79656400000000000000000000000000000000000000;
      Code.functions :=
        [
          Code.Function.make (
            "fun_f",
            ["var_x"],
            ["var"],
            M.scope (
              do! ltac:(M.monadic (
                M.declare (|
                  ["var_1"],
                  Some ([Literal.number 0])
                |)
              )) in
              do! ltac:(M.monadic (
                M.assign (|
                  ["var"],
                  Some ([Literal.number 0])
                |)
              )) in
              do! ltac:(M.monadic (
                M.if_ (|
                  M.call_function (|
                    "iszero",
                    [
                      M.call_function (|
                        "extcodesize",
                        [
                          M.call_function (|
                            "address",
                            []
                          |)
                        ]
                      |)
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
                  ["_1"],
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
                      M.get_var (| "_1" |);
                      M.call_function (|
                        "shl",
                        [
                          [Literal.number 224];
                          [Literal.number 0xd48092f7]
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
                      M.call_function (|
                        "add",
                        [
                          M.get_var (| "_1" |);
                          [Literal.number 4]
                        ]
                      |);
                      M.call_function (|
                        "iszero",
                        [
                          M.call_function (|
                            "iszero",
                            [
                              M.get_var (| "var_x" |)
                            ]
                          |)
                        ]
                      |)
                    ]
                  |)
                |)
              )) in
              do! ltac:(M.monadic (
                M.declare (|
                  ["trySuccessCondition"],
                  Some (M.call_function (|
                    "staticcall",
                    [
                      [Literal.number 0x1f40];
                      M.call_function (|
                        "address",
                        []
                      |);
                      M.get_var (| "_1" |);
                      [Literal.number 36];
                      M.get_var (| "_1" |);
                      [Literal.number 0]
                    ]
                  |))
                |)
              )) in
              do! ltac:(M.monadic (
                M.if_ (|
                  M.get_var (| "trySuccessCondition" |),
                  M.scope (
                    do! ltac:(M.monadic (
                      M.if_ (|
                        M.call_function (|
                          "gt",
                          [
                            M.get_var (| "_1" |);
                            [Literal.number 0xffffffffffffffff]
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
                                  [Literal.number 0x41]
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
                                  [Literal.number 36]
                                ]
                              |)
                            |)
                          )) in
                          M.pure BlockUnit.Tt
                        )
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
                      M.assign (|
                        ["var_1"],
                        Some ([Literal.number 0])
                      |)
                    )) in
                    M.pure BlockUnit.Tt
                  )
                |)
              )) in
              do! ltac:(M.monadic (
                M.switch (|
                  M.call_function (|
                    "iszero",
                    [
                      M.get_var (| "trySuccessCondition" |)
                    ]
                  |),
                  [
                    (
                      Some (Literal.number 0),
                      M.scope (
                        do! ltac:(M.monadic (
                          M.assign (|
                            ["var"],
                            Some ([Literal.number 0x01])
                          |)
                        )) in
                        do! ltac:(M.monadic (
                          M.leave (||)
                        )) in
                        M.pure BlockUnit.Tt
                      )
                    );
                    (
                      None,
                      M.scope (
                        do! ltac:(M.monadic (
                          M.assign (|
                            ["var"],
                            Some ([Literal.number 0x02])
                          |)
                        )) in
                        do! ltac:(M.monadic (
                          M.leave (||)
                        )) in
                        M.pure BlockUnit.Tt
                      )
                    )
                  ]
                |)
              )) in
              M.pure BlockUnit.Tt
            )
          )
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
                      M.switch (|
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
                        |),
                        [
                          (
                            Some (Literal.number 0x98c3a6c1),
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
                                      [Literal.number 32]
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
                                  ["value"],
                                  Some (M.call_function (|
                                    "calldataload",
                                    [
                                      [Literal.number 4]
                                    ]
                                  |))
                                |)
                              )) in
                              do! ltac:(M.monadic (
                                M.if_ (|
                                  M.call_function (|
                                    "iszero",
                                    [
                                      M.call_function (|
                                        "eq",
                                        [
                                          M.get_var (| "value" |);
                                          M.call_function (|
                                            "iszero",
                                            [
                                              M.call_function (|
                                                "iszero",
                                                [
                                                  M.get_var (| "value" |)
                                                ]
                                              |)
                                            ]
                                          |)
                                        ]
                                      |)
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
                                  ["ret"],
                                  Some (M.call_function (|
                                    "fun_f",
                                    [
                                      M.get_var (| "value" |)
                                    ]
                                  |))
                                |)
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
                                      M.get_var (| "ret" |)
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
                          );
                          (
                            Some (Literal.number 0xd48092f7),
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
                                      [Literal.number 32]
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
                                  ["value_1"],
                                  Some (M.call_function (|
                                    "calldataload",
                                    [
                                      [Literal.number 4]
                                    ]
                                  |))
                                |)
                              )) in
                              do! ltac:(M.monadic (
                                M.declare (|
                                  ["_1"],
                                  Some (M.call_function (|
                                    "iszero",
                                    [
                                      M.get_var (| "value_1" |)
                                    ]
                                  |))
                                |)
                              )) in
                              do! ltac:(M.monadic (
                                M.if_ (|
                                  M.call_function (|
                                    "iszero",
                                    [
                                      M.call_function (|
                                        "eq",
                                        [
                                          M.get_var (| "value_1" |);
                                          M.call_function (|
                                            "iszero",
                                            [
                                              M.get_var (| "_1" |)
                                            ]
                                          |)
                                        ]
                                      |)
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
                                M.if_ (|
                                  M.get_var (| "_1" |),
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
                                            [Literal.number 0x01]
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
                                M.expr_stmt (|
                                  M.call_function (|
                                    "return",
                                    [
                                      [Literal.number 0];
                                      [Literal.number 0]
                                    ]
                                  |)
                                |)
                              )) in
                              M.pure BlockUnit.Tt
                            )
                          )
                        ]
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
End C.

Import Ltac2.

Definition codes : list Code.t :=
  ltac2:(
    let codes := Code.get_codes () in
    exact $codes
  ).
