(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

Module B.
  Definition code : Code.t := {|
    Code.name := "B_78";
    Code.hex_name := 0x425f373800000000000000000000000000000000000000000000000000000000;
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
                    [Literal.string 0x425f37385f6465706c6f79656400000000000000000000000000000000000000]
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
                        [Literal.string 0x425f37385f6465706c6f79656400000000000000000000000000000000000000]
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
      Code.name := "B_78_deployed";
      Code.hex_name := 0x425f37385f6465706c6f79656400000000000000000000000000000000000000;
      Code.functions :=
        [
          Code.Function.make (
            "abi_decode_array_uint256_dyn",
            ["dataEnd"],
            ["value0"],
            M.scope (
              do! ltac:(M.monadic (
                M.if_ (|
                  M.call_function (|
                    "slt",
                    [
                      M.call_function (|
                        "add",
                        [
                          M.get_var (| "dataEnd" |);
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
                  ["offset"],
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
                    "gt",
                    [
                      M.get_var (| "offset" |);
                      [Literal.number 0xffffffffffffffff]
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
                      M.call_function (|
                        "slt",
                        [
                          M.call_function (|
                            "add",
                            [
                              M.get_var (| "offset" |);
                              [Literal.number 35]
                            ]
                          |);
                          M.get_var (| "dataEnd" |)
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
                  ["length"],
                  Some (M.call_function (|
                    "calldataload",
                    [
                      M.call_function (|
                        "add",
                        [
                          [Literal.number 4];
                          M.get_var (| "offset" |)
                        ]
                      |)
                    ]
                  |))
                |)
              )) in
              do! ltac:(M.monadic (
                M.if_ (|
                  M.call_function (|
                    "gt",
                    [
                      M.get_var (| "length" |);
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
                M.declare (|
                  ["_1"],
                  Some (M.call_function (|
                    "shl",
                    [
                      [Literal.number 5];
                      M.get_var (| "length" |)
                    ]
                  |))
                |)
              )) in
              do! ltac:(M.monadic (
                M.declare (|
                  ["memPtr"],
                  Some (M.call_function (|
                    "mload",
                    [
                      [Literal.number 64]
                    ]
                  |))
                |)
              )) in
              do! ltac:(M.monadic (
                M.declare (|
                  ["newFreePtr"],
                  Some (M.call_function (|
                    "add",
                    [
                      M.get_var (| "memPtr" |);
                      M.call_function (|
                        "and",
                        [
                          M.call_function (|
                            "add",
                            [
                              M.get_var (| "_1" |);
                              [Literal.number 63]
                            ]
                          |);
                          M.call_function (|
                            "not",
                            [
                              [Literal.number 31]
                            ]
                          |)
                        ]
                      |)
                    ]
                  |))
                |)
              )) in
              do! ltac:(M.monadic (
                M.if_ (|
                  M.call_function (|
                    "or",
                    [
                      M.call_function (|
                        "gt",
                        [
                          M.get_var (| "newFreePtr" |);
                          [Literal.number 0xffffffffffffffff]
                        ]
                      |);
                      M.call_function (|
                        "lt",
                        [
                          M.get_var (| "newFreePtr" |);
                          M.get_var (| "memPtr" |)
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
                      M.get_var (| "newFreePtr" |)
                    ]
                  |)
                |)
              )) in
              do! ltac:(M.monadic (
                M.declare (|
                  ["dst"],
                  Some (M.get_var (| "memPtr" |))
                |)
              )) in
              do! ltac:(M.monadic (
                M.expr_stmt (|
                  M.call_function (|
                    "mstore",
                    [
                      M.get_var (| "memPtr" |);
                      M.get_var (| "length" |)
                    ]
                  |)
                |)
              )) in
              do! ltac:(M.monadic (
                M.assign (|
                  ["dst"],
                  Some (M.call_function (|
                    "add",
                    [
                      M.get_var (| "memPtr" |);
                      [Literal.number 32]
                    ]
                  |))
                |)
              )) in
              do! ltac:(M.monadic (
                M.declare (|
                  ["srcEnd"],
                  Some (M.call_function (|
                    "add",
                    [
                      M.call_function (|
                        "add",
                        [
                          M.get_var (| "offset" |);
                          M.get_var (| "_1" |)
                        ]
                      |);
                      [Literal.number 36]
                    ]
                  |))
                |)
              )) in
              do! ltac:(M.monadic (
                M.if_ (|
                  M.call_function (|
                    "gt",
                    [
                      M.get_var (| "srcEnd" |);
                      M.get_var (| "dataEnd" |)
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
                  ["src"],
                  Some (M.call_function (|
                    "add",
                    [
                      M.get_var (| "offset" |);
                      [Literal.number 36]
                    ]
                  |))
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
                      M.call_function (|
                        "lt",
                        [
                          M.get_var (| "src" |);
                          M.get_var (| "srcEnd" |)
                        ]
                      |)
                    )),
                    M.scope (
                      do! ltac:(M.monadic (
                        M.assign (|
                          ["src"],
                          Some (M.call_function (|
                            "add",
                            [
                              M.get_var (| "src" |);
                              [Literal.number 32]
                            ]
                          |))
                        |)
                      )) in
                      M.pure BlockUnit.Tt
                    ),
                    M.scope (
                      do! ltac:(M.monadic (
                        M.expr_stmt (|
                          M.call_function (|
                            "mstore",
                            [
                              M.get_var (| "dst" |);
                              M.call_function (|
                                "calldataload",
                                [
                                  M.get_var (| "src" |)
                                ]
                              |)
                            ]
                          |)
                        |)
                      )) in
                      do! ltac:(M.monadic (
                        M.assign (|
                          ["dst"],
                          Some (M.call_function (|
                            "add",
                            [
                              M.get_var (| "dst" |);
                              [Literal.number 32]
                            ]
                          |))
                        |)
                      )) in
                      M.pure BlockUnit.Tt
                    )
                  |)
                ))
              )) in
              do! ltac:(M.monadic (
                M.assign (|
                  ["value0"],
                  Some (M.get_var (| "memPtr" |))
                |)
              )) in
              M.pure BlockUnit.Tt
            )
          );
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
                M.expr_stmt (|
                  M.call_function (|
                    "pop",
                    [
                      M.call_function (|
                        "abi_decode_array_uint256_dyn",
                        [
                          M.call_function (|
                            "calldatasize",
                            []
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
                      [Literal.number 0];
                      [Literal.number 0]
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
                            Some (Literal.number 0x01d0e2b5),
                            M.scope (
                              do! ltac:(M.monadic (
                                M.expr_stmt (|
                                  M.call_function (|
                                    "pop",
                                    [
                                      M.call_function (|
                                        "abi_decode_array_uint256_dyn",
                                        [
                                          M.call_function (|
                                            "calldatasize",
                                            []
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
                                      [Literal.number 0];
                                      [Literal.number 0]
                                    ]
                                  |)
                                |)
                              )) in
                              M.pure BlockUnit.Tt
                            )
                          );
                          (
                            Some (Literal.number 0x40dcbb08),
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
                                M.expr_stmt (|
                                  M.call_function (|
                                    "pop",
                                    [
                                      M.call_function (|
                                        "abi_decode_array_uint256_dyn",
                                        [
                                          M.call_function (|
                                            "calldatasize",
                                            []
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
                                    "sstore",
                                    [
                                      [Literal.number 0];
                                      [Literal.number 0x2a]
                                    ]
                                  |)
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
                          );
                          (
                            Some (Literal.number 0x7bc5bbbf),
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
                            Some (Literal.number 0xbaf71609),
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
End B.

Import Ltac2.

Definition codes : list Code.t :=
  ltac2:(
    let codes := Code.get_codes () in
    exact $codes
  ).
