(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

Module C.
  Definition code : Code.t := {|
    Code.name := "C_49";
    Code.hex_name := 0x435f343900000000000000000000000000000000000000000000000000000000;
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
                    [Literal.string 0x435f34395f6465706c6f79656400000000000000000000000000000000000000]
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
                        [Literal.string 0x435f34395f6465706c6f79656400000000000000000000000000000000000000]
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
      Code.name := "C_49_deployed";
      Code.hex_name := 0x435f34395f6465706c6f79656400000000000000000000000000000000000000;
      Code.functions :=
        [
          Code.Function.make (
            "external_fun_f",
            [],
            [],
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
                M.declare (|
                  ["value0"],
                  Some ([Literal.number 0])
                |)
              )) in
              do! ltac:(M.monadic (
                M.declare (|
                  ["value1"],
                  Some ([Literal.number 0])
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
                      [Literal.number 64]
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
                M.assign (|
                  ["value0"],
                  Some (M.call_function (|
                    "calldataload",
                    [
                      [Literal.number 4]
                    ]
                  |))
                |)
              )) in
              do! ltac:(M.monadic (
                M.assign (|
                  ["value1"],
                  Some (M.call_function (|
                    "calldataload",
                    [
                      [Literal.number 36]
                    ]
                  |))
                |)
              )) in
              do! ltac:(M.monadic (
                M.declare (|
                  ["r"],
                  Some ([Literal.number 0])
                |)
              )) in
              do! ltac:(M.monadic (
                M.if_ (|
                  M.call_function (|
                    "iszero",
                    [
                      M.get_var (| "value1" |)
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
                            [Literal.number 0x12]
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
                M.assign (|
                  ["r"],
                  Some (M.call_function (|
                    "div",
                    [
                      M.get_var (| "value0" |);
                      M.get_var (| "value1" |)
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
                      M.get_var (| "r" |)
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
                            Some (Literal.number 0x13d1aa2e),
                            M.scope (
                              do! ltac:(M.monadic (
                                M.expr_stmt (|
                                  M.call_function (|
                                    "external_fun_f",
                                    []
                                  |)
                                |)
                              )) in
                              M.pure BlockUnit.Tt
                            )
                          );
                          (
                            Some (Literal.number 0x459026f5),
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
                                      [Literal.number 64]
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
                                M.declare (|
                                  ["_1"],
                                  Some (M.call_function (|
                                    "signextend",
                                    [
                                      [Literal.number 0];
                                      M.get_var (| "value" |)
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
                                          M.get_var (| "_1" |)
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
                                  ["value_1"],
                                  Some (M.call_function (|
                                    "calldataload",
                                    [
                                      [Literal.number 36]
                                    ]
                                  |))
                                |)
                              )) in
                              do! ltac:(M.monadic (
                                M.declare (|
                                  ["_2"],
                                  Some (M.call_function (|
                                    "signextend",
                                    [
                                      [Literal.number 0];
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
                                          M.get_var (| "_2" |)
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
                                  M.call_function (|
                                    "iszero",
                                    [
                                      M.get_var (| "_2" |)
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
                                            [Literal.number 0x12]
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
                                M.if_ (|
                                  M.call_function (|
                                    "and",
                                    [
                                      M.call_function (|
                                        "eq",
                                        [
                                          M.get_var (| "_1" |);
                                          M.call_function (|
                                            "not",
                                            [
                                              [Literal.number 127]
                                            ]
                                          |)
                                        ]
                                      |);
                                      M.call_function (|
                                        "eq",
                                        [
                                          M.get_var (| "_2" |);
                                          M.call_function (|
                                            "not",
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
                                      M.call_function (|
                                        "signextend",
                                        [
                                          [Literal.number 0];
                                          M.call_function (|
                                            "sdiv",
                                            [
                                              M.get_var (| "_1" |);
                                              M.get_var (| "_2" |)
                                            ]
                                          |)
                                        ]
                                      |)
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
                            Some (Literal.number 0xa61510ae),
                            M.scope (
                              do! ltac:(M.monadic (
                                M.expr_stmt (|
                                  M.call_function (|
                                    "external_fun_f",
                                    []
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
