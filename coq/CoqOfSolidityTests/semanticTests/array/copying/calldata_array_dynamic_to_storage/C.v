(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

Module C.
  Definition code : Code.t := {|
    Code.name := "C_22";
    Code.hex_name := 0x435f323200000000000000000000000000000000000000000000000000000000;
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
                    [Literal.string 0x435f32325f6465706c6f79656400000000000000000000000000000000000000]
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
                        [Literal.string 0x435f32325f6465706c6f79656400000000000000000000000000000000000000]
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
      Code.name := "C_22_deployed";
      Code.hex_name := 0x435f32325f6465706c6f79656400000000000000000000000000000000000000;
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
                            [Literal.number 0x7bc5bbbf];
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
                                      M.call_function (|
                                        "calldatasize",
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
                            M.declare (|
                              ["_2"],
                              Some (M.call_function (|
                                "gt",
                                [
                                  M.get_var (| "length" |);
                                  [Literal.number 0xffffffffffffffff]
                                ]
                              |))
                            |)
                          )) in
                          do! ltac:(M.monadic (
                            M.if_ (|
                              M.get_var (| "_2" |),
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
                                "gt",
                                [
                                  M.call_function (|
                                    "add",
                                    [
                                      M.call_function (|
                                        "add",
                                        [
                                          M.get_var (| "offset" |);
                                          M.call_function (|
                                            "shl",
                                            [
                                              [Literal.number 5];
                                              M.get_var (| "length" |)
                                            ]
                                          |)
                                        ]
                                      |);
                                      [Literal.number 36]
                                    ]
                                  |);
                                  M.call_function (|
                                    "calldatasize",
                                    []
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
                            M.assign (|
                              ["_2"],
                              Some ([Literal.number 0])
                            |)
                          )) in
                          do! ltac:(M.monadic (
                            M.if_ (|
                              M.call_function (|
                                "gt",
                                [
                                  M.get_var (| "length" |);
                                  [Literal.number 18446744073709551616]
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
                              ["oldLen"],
                              Some (M.call_function (|
                                "sload",
                                [
                                  [Literal.number 0]
                                ]
                              |))
                            |)
                          )) in
                          do! ltac:(M.monadic (
                            M.expr_stmt (|
                              M.call_function (|
                                "sstore",
                                [
                                  [Literal.number 0];
                                  M.get_var (| "length" |)
                                ]
                              |)
                            |)
                          )) in
                          do! ltac:(M.monadic (
                            M.if_ (|
                              M.call_function (|
                                "lt",
                                [
                                  M.get_var (| "length" |);
                                  M.get_var (| "oldLen" |)
                                ]
                              |),
                              M.scope (
                                do! ltac:(M.monadic (
                                  M.declare (|
                                    ["_3"],
                                    Some (M.call_function (|
                                      "add",
                                      [
                                        [Literal.number 18569430475105882587588266137607568536673111973893317399460219858819262702947];
                                        M.get_var (| "oldLen" |)
                                      ]
                                    |))
                                  |)
                                )) in
                                do! ltac:(M.monadic (
                                  M.declare (|
                                    ["start"],
                                    Some (M.call_function (|
                                      "add",
                                      [
                                        [Literal.number 18569430475105882587588266137607568536673111973893317399460219858819262702947];
                                        M.get_var (| "length" |)
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
                                            M.get_var (| "start" |);
                                            M.get_var (| "_3" |)
                                          ]
                                        |)
                                      )),
                                      M.scope (
                                        do! ltac:(M.monadic (
                                          M.assign (|
                                            ["start"],
                                            Some (M.call_function (|
                                              "add",
                                              [
                                                M.get_var (| "start" |);
                                                [Literal.number 1]
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
                                              "sstore",
                                              [
                                                M.get_var (| "start" |);
                                                [Literal.number 0]
                                              ]
                                            |)
                                          |)
                                        )) in
                                        M.pure BlockUnit.Tt
                                      )
                                    |)
                                  ))
                                )) in
                                M.pure BlockUnit.Tt
                              )
                            |)
                          )) in
                          do! ltac:(M.monadic (
                            M.declare (|
                              ["srcPtr"],
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
                            M.declare (|
                              ["i"],
                              Some ([Literal.number 0])
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
                                      M.get_var (| "i" |);
                                      M.get_var (| "length" |)
                                    ]
                                  |)
                                )),
                                M.scope (
                                  do! ltac:(M.monadic (
                                    M.assign (|
                                      ["i"],
                                      Some (M.call_function (|
                                        "add",
                                        [
                                          M.get_var (| "i" |);
                                          [Literal.number 1]
                                        ]
                                      |))
                                    |)
                                  )) in
                                  M.pure BlockUnit.Tt
                                ),
                                M.scope (
                                  do! ltac:(M.monadic (
                                    M.declare (|
                                      ["value"],
                                      Some (M.call_function (|
                                        "calldataload",
                                        [
                                          M.get_var (| "srcPtr" |)
                                        ]
                                      |))
                                    |)
                                  )) in
                                  do! ltac:(M.monadic (
                                    M.assign (|
                                      ["srcPtr"],
                                      Some (M.call_function (|
                                        "add",
                                        [
                                          M.get_var (| "srcPtr" |);
                                          [Literal.number 32]
                                        ]
                                      |))
                                    |)
                                  )) in
                                  do! ltac:(M.monadic (
                                    M.expr_stmt (|
                                      M.call_function (|
                                        "sstore",
                                        [
                                          M.call_function (|
                                            "add",
                                            [
                                              [Literal.number 18569430475105882587588266137607568536673111973893317399460219858819262702947];
                                              M.get_var (| "i" |)
                                            ]
                                          |);
                                          M.get_var (| "value" |)
                                        ]
                                      |)
                                    |)
                                  )) in
                                  M.pure BlockUnit.Tt
                                )
                              |)
                            ))
                          )) in
                          do! ltac:(M.monadic (
                            M.if_ (|
                              M.call_function (|
                                "iszero",
                                [
                                  M.call_function (|
                                    "sload",
                                    [
                                      [Literal.number 0]
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
                                        [Literal.number 0x32]
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
                                  [Literal.number 0];
                                  [Literal.number 0]
                                ]
                              |)
                            |)
                          )) in
                          do! ltac:(M.monadic (
                            M.expr_stmt (|
                              M.call_function (|
                                "mstore",
                                [
                                  M.get_var (| "_1" |);
                                  M.call_function (|
                                    "sload",
                                    [
                                      [Literal.number 18569430475105882587588266137607568536673111973893317399460219858819262702947]
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
                                  M.get_var (| "_1" |);
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
End C.

Import Ltac2.

Definition codes : list Code.t :=
  ltac2:(
    let codes := Code.get_codes () in
    exact $codes
  ).
