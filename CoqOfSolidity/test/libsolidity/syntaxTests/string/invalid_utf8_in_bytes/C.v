(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

Module C.
  Definition code : Code.t := {|
    Code.name := "C_10";
    Code.hex_name := 0x435f313000000000000000000000000000000000000000000000000000000000;
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
                  "sload",
                  [
                    [Literal.number 0x00]
                  ]
                |))
              |)
            )) in
            do! ltac:(M.monadic (
              M.declare (|
                ["length"],
                Some ([Literal.number 0x00])
              |)
            )) in
            do! ltac:(M.monadic (
              M.assign (|
                ["length"],
                Some (M.call_function (|
                  "shr",
                  [
                    [Literal.number 1];
                    M.get_var (| "_2" |)
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
                    M.get_var (| "_2" |);
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
              M.if_ (|
                M.call_function (|
                  "eq",
                  [
                    M.get_var (| "outOfPlaceEncoding" |);
                    M.call_function (|
                      "lt",
                      [
                        M.get_var (| "length" |);
                        [Literal.number 32]
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
                          [Literal.number 0x00];
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
                          [Literal.number 0x00];
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
                  "gt",
                  [
                    M.get_var (| "length" |);
                    [Literal.number 31]
                  ]
                |),
                M.scope (
                  do! ltac:(M.monadic (
                    M.expr_stmt (|
                      M.call_function (|
                        "mstore",
                        [
                          [Literal.number 0x00];
                          [Literal.number 0x00]
                        ]
                      |)
                    |)
                  )) in
                  do! ltac:(M.monadic (
                    M.declare (|
                      ["data"],
                      Some (M.call_function (|
                        "keccak256",
                        [
                          [Literal.number 0x00];
                          [Literal.number 32]
                        ]
                      |))
                    |)
                  )) in
                  do! ltac:(M.monadic (
                    M.declare (|
                      ["_3"],
                      Some (M.call_function (|
                        "add",
                        [
                          M.get_var (| "data" |);
                          M.call_function (|
                            "shr",
                            [
                              [Literal.number 5];
                              M.call_function (|
                                "add",
                                [
                                  M.get_var (| "length" |);
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
                    M.declare (|
                      ["start"],
                      Some (M.get_var (| "data" |))
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
                                  [Literal.number 0x00]
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
              M.expr_stmt (|
                M.call_function (|
                  "sstore",
                  [
                    [Literal.number 0x00];
                    M.call_function (|
                      "add",
                      [
                        M.call_function (|
                          "shl",
                          [
                            [Literal.number 253];
                            [Literal.number 5]
                          ]
                        |);
                        [Literal.number 4]
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
                    [Literal.number 1];
                    M.call_function (|
                      "shl",
                      [
                        [Literal.number 253];
                        [Literal.number 5]
                      ]
                    |)
                  ]
                |)
              |)
            )) in
            do! ltac:(M.monadic (
              M.declare (|
                ["_4"],
                Some (M.call_function (|
                  "sload",
                  [
                    [Literal.number 2]
                  ]
                |))
              |)
            )) in
            do! ltac:(M.monadic (
              M.declare (|
                ["length_1"],
                Some ([Literal.number 0x00])
              |)
            )) in
            do! ltac:(M.monadic (
              M.assign (|
                ["length_1"],
                Some (M.call_function (|
                  "shr",
                  [
                    [Literal.number 1];
                    M.get_var (| "_4" |)
                  ]
                |))
              |)
            )) in
            do! ltac:(M.monadic (
              M.declare (|
                ["outOfPlaceEncoding_1"],
                Some (M.call_function (|
                  "and",
                  [
                    M.get_var (| "_4" |);
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
                    M.get_var (| "outOfPlaceEncoding_1" |)
                  ]
                |),
                M.scope (
                  do! ltac:(M.monadic (
                    M.assign (|
                      ["length_1"],
                      Some (M.call_function (|
                        "and",
                        [
                          M.get_var (| "length_1" |);
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
              M.if_ (|
                M.call_function (|
                  "eq",
                  [
                    M.get_var (| "outOfPlaceEncoding_1" |);
                    M.call_function (|
                      "lt",
                      [
                        M.get_var (| "length_1" |);
                        [Literal.number 32]
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
                          [Literal.number 0x00];
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
                          [Literal.number 0x00];
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
                  "gt",
                  [
                    M.get_var (| "length_1" |);
                    [Literal.number 31]
                  ]
                |),
                M.scope (
                  do! ltac:(M.monadic (
                    M.expr_stmt (|
                      M.call_function (|
                        "mstore",
                        [
                          [Literal.number 0x00];
                          [Literal.number 2]
                        ]
                      |)
                    |)
                  )) in
                  do! ltac:(M.monadic (
                    M.declare (|
                      ["data_1"],
                      Some (M.call_function (|
                        "keccak256",
                        [
                          [Literal.number 0x00];
                          [Literal.number 32]
                        ]
                      |))
                    |)
                  )) in
                  do! ltac:(M.monadic (
                    M.declare (|
                      ["_5"],
                      Some (M.call_function (|
                        "add",
                        [
                          M.get_var (| "data_1" |);
                          M.call_function (|
                            "shr",
                            [
                              [Literal.number 5];
                              M.call_function (|
                                "add",
                                [
                                  M.get_var (| "length_1" |);
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
                    M.declare (|
                      ["start_1"],
                      Some (M.get_var (| "data_1" |))
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
                              M.get_var (| "start_1" |);
                              M.get_var (| "_5" |)
                            ]
                          |)
                        )),
                        M.scope (
                          do! ltac:(M.monadic (
                            M.assign (|
                              ["start_1"],
                              Some (M.call_function (|
                                "add",
                                [
                                  M.get_var (| "start_1" |);
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
                                  M.get_var (| "start_1" |);
                                  [Literal.number 0x00]
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
              M.expr_stmt (|
                M.call_function (|
                  "sstore",
                  [
                    [Literal.number 2];
                    M.call_function (|
                      "add",
                      [
                        M.call_function (|
                          "shl",
                          [
                            [Literal.number 253];
                            [Literal.number 5]
                          ]
                        |);
                        [Literal.number 4]
                      ]
                    |)
                  ]
                |)
              |)
            )) in
            do! ltac:(M.monadic (
              M.declare (|
                ["_6"],
                Some (M.call_function (|
                  "datasize",
                  [
                    [Literal.string 0x435f31305f6465706c6f79656400000000000000000000000000000000000000]
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
                        [Literal.string 0x435f31305f6465706c6f79656400000000000000000000000000000000000000]
                      ]
                    |);
                    M.get_var (| "_6" |)
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
                    M.get_var (| "_6" |)
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
      Code.name := "C_10_deployed";
      Code.hex_name := 0x435f31305f6465706c6f79656400000000000000000000000000000000000000;
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
