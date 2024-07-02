(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

Module c.
  Definition code : Code.t := {|
    Code.name := "c_22";
    Code.hex_name := 0x635f323200000000000000000000000000000000000000000000000000000000;
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
                    [Literal.string 0x635f32325f6465706c6f79656400000000000000000000000000000000000000]
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
                        [Literal.string 0x635f32325f6465706c6f79656400000000000000000000000000000000000000]
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
      Code.name := "c_22_deployed";
      Code.hex_name := 0x635f32325f6465706c6f79656400000000000000000000000000000000000000;
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
                            [Literal.number 0xf8a8fd6d];
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
                              ["data"],
                              Some (M.call_function (|
                                "sload",
                                [
                                  [Literal.number 0x03]
                                ]
                              |))
                            |)
                          )) in
                          do! ltac:(M.monadic (
                            M.declare (|
                              ["length"],
                              Some ([Literal.number 0])
                            |)
                          )) in
                          do! ltac:(M.monadic (
                            M.assign (|
                              ["length"],
                              Some (M.call_function (|
                                "shr",
                                [
                                  [Literal.number 1];
                                  M.get_var (| "data" |)
                                ]
                              |))
                            |)
                          )) in
                          do! ltac:(M.monadic (
                            M.declare (|
                              ["outOfPlaceEncoding"],
                              Some (M.call_function (|
                                "and",
                                [
                                  M.get_var (| "data" |);
                                  [Literal.number 1]
                                ]
                              |))
                            |)
                          )) in
                          do! ltac:(M.monadic (
                            M.if_ (|
                              M.call_function (|
                                "iszero",
                                [
                                  M.get_var (| "outOfPlaceEncoding" |)
                                ]
                              |),
                              M.scope (
                                do! ltac:(M.monadic (
                                  M.assign (|
                                    ["length"],
                                    Some (M.call_function (|
                                      "and",
                                      [
                                        M.get_var (| "length" |);
                                        [Literal.number 0x7f]
                                      ]
                                    |))
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
                                "lt",
                                [
                                  M.get_var (| "length" |);
                                  [Literal.number 32]
                                ]
                              |))
                            |)
                          )) in
                          do! ltac:(M.monadic (
                            M.if_ (|
                              M.call_function (|
                                "eq",
                                [
                                  M.get_var (| "outOfPlaceEncoding" |);
                                  M.get_var (| "_1" |)
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
                                        [Literal.number 0x22]
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
                            M.if_ (|
                              M.call_function (|
                                "iszero",
                                [
                                  M.get_var (| "length" |)
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
                                        [Literal.number 0x31]
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
                            M.switch (|
                              M.get_var (| "length" |),
                              [
                                (
                                  Some (Literal.number 32),
                                  M.scope (
                                    do! ltac:(M.monadic (
                                      M.expr_stmt (|
                                        M.call_function (|
                                          "mstore",
                                          [
                                            [Literal.number 0];
                                            [Literal.number 0x03]
                                          ]
                                        |)
                                      |)
                                    )) in
                                    do! ltac:(M.monadic (
                                      M.declare (|
                                        ["_2"],
                                        Some (M.call_function (|
                                          "sload",
                                          [
                                            [Literal.number 87903029871075914254377627908054574944891091886930582284385770809450030037083]
                                          ]
                                        |))
                                      |)
                                    )) in
                                    do! ltac:(M.monadic (
                                      M.declare (|
                                        ["used"],
                                        Some ([Literal.number 0])
                                      |)
                                    )) in
                                    do! ltac:(M.monadic (
                                      M.assign (|
                                        ["used"],
                                        Some (M.call_function (|
                                          "or",
                                          [
                                            M.call_function (|
                                              "and",
                                              [
                                                M.get_var (| "_2" |);
                                                M.call_function (|
                                                  "not",
                                                  [
                                                    [Literal.number 255]
                                                  ]
                                                |)
                                              ]
                                            |);
                                            [Literal.number 62]
                                          ]
                                        |))
                                      |)
                                    )) in
                                    do! ltac:(M.monadic (
                                      M.expr_stmt (|
                                        M.call_function (|
                                          "sstore",
                                          [
                                            [Literal.number 0x03];
                                            M.get_var (| "used" |)
                                          ]
                                        |)
                                      |)
                                    )) in
                                    do! ltac:(M.monadic (
                                      M.expr_stmt (|
                                        M.call_function (|
                                          "sstore",
                                          [
                                            [Literal.number 87903029871075914254377627908054574944891091886930582284385770809450030037083];
                                            [Literal.number 0]
                                          ]
                                        |)
                                      |)
                                    )) in
                                    M.pure BlockUnit.Tt
                                  )
                                );
                                (
                                  None,
                                  M.scope (
                                    do! ltac:(M.monadic (
                                      M.declare (|
                                        ["newLen"],
                                        Some (M.call_function (|
                                          "add",
                                          [
                                            M.get_var (| "length" |);
                                            M.call_function (|
                                              "not",
                                              [
                                                [Literal.number 0]
                                              ]
                                            |)
                                          ]
                                        |))
                                      |)
                                    )) in
                                    do! ltac:(M.monadic (
                                      M.switch (|
                                        M.get_var (| "_1" |),
                                        [
                                          (
                                            Some (Literal.number 1),
                                            M.scope (
                                              do! ltac:(M.monadic (
                                                M.declare (|
                                                  ["used_1"],
                                                  Some ([Literal.number 0])
                                                |)
                                              )) in
                                              do! ltac:(M.monadic (
                                                M.assign (|
                                                  ["used_1"],
                                                  Some (M.call_function (|
                                                    "or",
                                                    [
                                                      M.call_function (|
                                                        "and",
                                                        [
                                                          M.get_var (| "data" |);
                                                          M.call_function (|
                                                            "not",
                                                            [
                                                              M.call_function (|
                                                                "shr",
                                                                [
                                                                  M.call_function (|
                                                                    "shl",
                                                                    [
                                                                      [Literal.number 0x03];
                                                                      M.get_var (| "newLen" |)
                                                                    ]
                                                                  |);
                                                                  M.call_function (|
                                                                    "not",
                                                                    [
                                                                      [Literal.number 0]
                                                                    ]
                                                                  |)
                                                                ]
                                                              |)
                                                            ]
                                                          |)
                                                        ]
                                                      |);
                                                      M.call_function (|
                                                        "shl",
                                                        [
                                                          [Literal.number 1];
                                                          M.get_var (| "newLen" |)
                                                        ]
                                                      |)
                                                    ]
                                                  |))
                                                |)
                                              )) in
                                              do! ltac:(M.monadic (
                                                M.expr_stmt (|
                                                  M.call_function (|
                                                    "sstore",
                                                    [
                                                      [Literal.number 0x03];
                                                      M.get_var (| "used_1" |)
                                                    ]
                                                  |)
                                                |)
                                              )) in
                                              M.pure BlockUnit.Tt
                                            )
                                          );
                                          (
                                            None,
                                            M.scope (
                                              do! ltac:(M.monadic (
                                                M.expr_stmt (|
                                                  M.call_function (|
                                                    "mstore",
                                                    [
                                                      [Literal.number 0];
                                                      [Literal.number 0x03]
                                                    ]
                                                  |)
                                                |)
                                              )) in
                                              do! ltac:(M.monadic (
                                                M.declare (|
                                                  ["slot"],
                                                  Some (M.call_function (|
                                                    "add",
                                                    [
                                                      [Literal.number 87903029871075914254377627908054574944891091886930582284385770809450030037083];
                                                      M.call_function (|
                                                        "shr",
                                                        [
                                                          [Literal.number 5];
                                                          M.get_var (| "newLen" |)
                                                        ]
                                                      |)
                                                    ]
                                                  |))
                                                |)
                                              )) in
                                              do! ltac:(M.monadic (
                                                M.declare (|
                                                  ["_3"],
                                                  Some (M.call_function (|
                                                    "sload",
                                                    [
                                                      M.get_var (| "slot" |)
                                                    ]
                                                  |))
                                                |)
                                              )) in
                                              do! ltac:(M.monadic (
                                                M.expr_stmt (|
                                                  M.call_function (|
                                                    "sstore",
                                                    [
                                                      M.get_var (| "slot" |);
                                                      M.call_function (|
                                                        "and",
                                                        [
                                                          M.get_var (| "_3" |);
                                                          M.call_function (|
                                                            "not",
                                                            [
                                                              M.call_function (|
                                                                "shl",
                                                                [
                                                                  M.call_function (|
                                                                    "shl",
                                                                    [
                                                                      [Literal.number 0x03];
                                                                      M.call_function (|
                                                                        "sub",
                                                                        [
                                                                          [Literal.number 31];
                                                                          M.call_function (|
                                                                            "and",
                                                                            [
                                                                              M.get_var (| "newLen" |);
                                                                              [Literal.number 31]
                                                                            ]
                                                                          |)
                                                                        ]
                                                                      |)
                                                                    ]
                                                                  |);
                                                                  [Literal.number 255]
                                                                ]
                                                              |)
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
                                                    "sstore",
                                                    [
                                                      [Literal.number 0x03];
                                                      M.call_function (|
                                                        "add",
                                                        [
                                                          M.get_var (| "data" |);
                                                          M.call_function (|
                                                            "not",
                                                            [
                                                              [Literal.number 1]
                                                            ]
                                                          |)
                                                        ]
                                                      |)
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
                                )
                              ]
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
                                  [Literal.number 1]
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
End c.

Import Ltac2.

Definition codes : list Code.t :=
  ltac2:(
    let codes := Code.get_codes () in
    exact $codes
  ).
