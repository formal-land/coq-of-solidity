(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

Module C.
  Definition code : Code.t := {|
    Code.name := "C_30";
    Code.hex_name := 0x435f333000000000000000000000000000000000000000000000000000000000;
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
                    [Literal.string 0x435f33305f6465706c6f79656400000000000000000000000000000000000000]
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
                        [Literal.string 0x435f33305f6465706c6f79656400000000000000000000000000000000000000]
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
      Code.name := "C_30_deployed";
      Code.hex_name := 0x435f33305f6465706c6f79656400000000000000000000000000000000000000;
      Code.functions :=
        [
          Code.Function.make (
            "finalize_allocation",
            ["memPtr"; "size"],
            [],
            M.scope (
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
                              M.get_var (| "size" |);
                              [Literal.number 31]
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
                    "mstore",
                    [
                      [Literal.number 64];
                      M.get_var (| "newFreePtr" |)
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
                              ["size"],
                              Some ([Literal.number 0])
                            |)
                          )) in
                          do! ltac:(M.monadic (
                            M.declare (|
                              ["_1"],
                              Some ([Literal.number 0])
                            |)
                          )) in
                          do! ltac:(M.monadic (
                            M.assign (|
                              ["_1"],
                              Some ([Literal.number 0])
                            |)
                          )) in
                          do! ltac:(M.monadic (
                            M.assign (|
                              ["size"],
                              Some ([Literal.number 96])
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
                            M.expr_stmt (|
                              M.call_function (|
                                "finalize_allocation",
                                [
                                  M.get_var (| "memPtr" |);
                                  [Literal.number 96]
                                ]
                              |)
                            |)
                          )) in
                          do! ltac:(M.monadic (
                            M.declare (|
                              ["size_1"],
                              Some ([Literal.number 0])
                            |)
                          )) in
                          do! ltac:(M.monadic (
                            M.declare (|
                              ["_2"],
                              Some ([Literal.number 0])
                            |)
                          )) in
                          do! ltac:(M.monadic (
                            M.assign (|
                              ["_2"],
                              Some ([Literal.number 0])
                            |)
                          )) in
                          do! ltac:(M.monadic (
                            M.assign (|
                              ["size_1"],
                              Some ([Literal.number 96])
                            |)
                          )) in
                          do! ltac:(M.monadic (
                            M.expr_stmt (|
                              M.call_function (|
                                "calldatacopy",
                                [
                                  M.get_var (| "memPtr" |);
                                  M.call_function (|
                                    "calldatasize",
                                    []
                                  |);
                                  [Literal.number 96]
                                ]
                              |)
                            |)
                          )) in
                          do! ltac:(M.monadic (
                            M.declare (|
                              ["expr_mpos"],
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
                                  M.call_function (|
                                    "add",
                                    [
                                      M.get_var (| "expr_mpos" |);
                                      [Literal.number 0x20]
                                    ]
                                  |);
                                  M.call_function (|
                                    "shl",
                                    [
                                      [Literal.number 64];
                                      M.call_function (|
                                        "or",
                                        [
                                          M.call_function (|
                                            "shl",
                                            [
                                              [Literal.number 0x20];
                                              M.call_function (|
                                                "address",
                                                []
                                              |)
                                            ]
                                          |);
                                          [Literal.number 0x26121ff0]
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
                              ["pos"],
                              Some (M.call_function (|
                                "add",
                                [
                                  M.get_var (| "expr_mpos" |);
                                  [Literal.number 56]
                                ]
                              |))
                            |)
                          )) in
                          do! ltac:(M.monadic (
                            M.assign (|
                              ["pos"],
                              Some (M.get_var (| "pos" |))
                            |)
                          )) in
                          do! ltac:(M.monadic (
                            M.declare (|
                              ["srcPtr"],
                              Some (M.get_var (| "memPtr" |))
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
                                      [Literal.number 3]
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
                                    M.expr_stmt (|
                                      M.call_function (|
                                        "mstore",
                                        [
                                          M.get_var (| "pos" |);
                                          M.call_function (|
                                            "mload",
                                            [
                                              M.get_var (| "srcPtr" |)
                                            ]
                                          |)
                                        ]
                                      |)
                                    |)
                                  )) in
                                  do! ltac:(M.monadic (
                                    M.assign (|
                                      ["pos"],
                                      Some (M.call_function (|
                                        "add",
                                        [
                                          M.get_var (| "pos" |);
                                          [Literal.number 0x20]
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
                                          [Literal.number 0x20]
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
                            M.declare (|
                              ["pos_1"],
                              Some (M.call_function (|
                                "add",
                                [
                                  M.get_var (| "expr_mpos" |);
                                  [Literal.number 152]
                                ]
                              |))
                            |)
                          )) in
                          do! ltac:(M.monadic (
                            M.assign (|
                              ["pos_1"],
                              Some (M.get_var (| "pos_1" |))
                            |)
                          )) in
                          do! ltac:(M.monadic (
                            M.declare (|
                              ["srcPtr_1"],
                              Some ([Literal.number 0])
                            |)
                          )) in
                          do! ltac:(M.monadic (
                            M.declare (|
                              ["i_1"],
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
                                      M.get_var (| "i_1" |);
                                      [Literal.number 3]
                                    ]
                                  |)
                                )),
                                M.scope (
                                  do! ltac:(M.monadic (
                                    M.assign (|
                                      ["i_1"],
                                      Some (M.call_function (|
                                        "add",
                                        [
                                          M.get_var (| "i_1" |);
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
                                        "mstore",
                                        [
                                          M.get_var (| "pos_1" |);
                                          M.call_function (|
                                            "sload",
                                            [
                                              M.get_var (| "srcPtr_1" |)
                                            ]
                                          |)
                                        ]
                                      |)
                                    |)
                                  )) in
                                  do! ltac:(M.monadic (
                                    M.assign (|
                                      ["pos_1"],
                                      Some (M.call_function (|
                                        "add",
                                        [
                                          M.get_var (| "pos_1" |);
                                          [Literal.number 0x20]
                                        ]
                                      |))
                                    |)
                                  )) in
                                  do! ltac:(M.monadic (
                                    M.assign (|
                                      ["srcPtr_1"],
                                      Some (M.call_function (|
                                        "add",
                                        [
                                          M.get_var (| "srcPtr_1" |);
                                          [Literal.number 1]
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
                            M.expr_stmt (|
                              M.call_function (|
                                "mstore",
                                [
                                  M.get_var (| "expr_mpos" |);
                                  [Literal.number 216]
                                ]
                              |)
                            |)
                          )) in
                          do! ltac:(M.monadic (
                            M.expr_stmt (|
                              M.call_function (|
                                "finalize_allocation",
                                [
                                  M.get_var (| "expr_mpos" |);
                                  [Literal.number 248]
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
