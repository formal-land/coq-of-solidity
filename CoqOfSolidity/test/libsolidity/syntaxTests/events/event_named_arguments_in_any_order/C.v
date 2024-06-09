(* Generated by solc *)
Require Import CoqOfSolidity.CoqOfSolidity.

Module C_49.
  Definition code : M.t unit := ltac:(M.monadic (
    let _ :=
      let _ :=
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
        |) in
      let _ :=
        M.if_ (|
          M.call (|
            "callvalue",
            []
          |),
          ltac:(M.monadic (
            let _ :=
              M.call (|
                "revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb",
                []
              |) in
            tt
          ))
        |) in
      let _ :=
        M.assign (|
          ["_1"],
          Some (M.call (|
            "allocate_unbounded",
            []
          |))
        |) in
      let _ :=
        M.call (|
          "codecopy",
          [
            M.get (| "_1" |);
            M.call (|
              "dataoffset",
              [
                [Literal.string "435f34395f6465706c6f796564"]
              ]
            |);
            M.call (|
              "datasize",
              [
                [Literal.string "435f34395f6465706c6f796564"]
              ]
            |)
          ]
        |) in
      let _ :=
        M.call (|
          "return",
          [
            M.get (| "_1" |);
            M.call (|
              "datasize",
              [
                [Literal.string "435f34395f6465706c6f796564"]
              ]
            |)
          ]
        |) in
      tt in
    let _ :=
      M.function (|
        "allocate_unbounded",
        [],
        ["memPtr"],
        ltac:(M.monadic (
          let _ :=
            M.declare (|
              ["memPtr"],
              M.call (|
                "mload",
                [
                  [Literal.number 64]
                ]
              |)
            |) in
          tt
        ))
      |) in
    let _ :=
      M.function (|
        "revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb",
        [],
        [],
        ltac:(M.monadic (
          let _ :=
            M.call (|
              "revert",
              [
                [Literal.number 0];
                [Literal.number 0]
              ]
            |) in
          tt
        ))
      |) in
    tt
  )).

  Module C_49_deployed.
    Definition code : M.t unit := ltac:(M.monadic (
      let _ :=
        let _ :=
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
          |) in
        let _ :=
          M.if_ (|
            M.call (|
              "iszero",
              [
                M.call (|
                  "lt",
                  [
                    M.call (|
                      "calldatasize",
                      []
                    |);
                    [Literal.number 4]
                  ]
                |)
              ]
            |),
            ltac:(M.monadic (
              let _ :=
                M.assign (|
                  ["selector"],
                  Some (M.call (|
                    "shift_right_unsigned",
                    [
                      M.call (|
                        "calldataload",
                        [
                          [Literal.number 0]
                        ]
                      |)
                    ]
                  |))
                |) in
              let _ :=
                M.switch (|
                  M.get (| "selector" |),
                  [
                    (
                      Some (Literal.number 0x28b5e32b),
                      ltac:(M.monadic (
                        let _ :=
                          M.call (|
                            "external_fun_call",
                            []
                          |) in
                        tt
                      ))              );
                    (
                      None,
                      ltac:(M.monadic (
                        tt
                      ))              )            ]
                |) in
              tt
            ))
          |) in
        let _ :=
          M.call (|
            "revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74",
            []
          |) in
        tt in
      let _ :=
        M.function (|
          "shift_right_unsigned",
          ["value"],
          ["newValue"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["newValue"],
                M.call (|
                  "shr",
                  [
                    [Literal.number 224];
                    M.get (| "value" |)
                  ]
                |)
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "allocate_unbounded",
          [],
          ["memPtr"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["memPtr"],
                M.call (|
                  "mload",
                  [
                    [Literal.number 64]
                  ]
                |)
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb",
          [],
          [],
          ltac:(M.monadic (
            let _ :=
              M.call (|
                "revert",
                [
                  [Literal.number 0];
                  [Literal.number 0]
                ]
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b",
          [],
          [],
          ltac:(M.monadic (
            let _ :=
              M.call (|
                "revert",
                [
                  [Literal.number 0];
                  [Literal.number 0]
                ]
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "abi_decode",
          ["headStart"; "dataEnd"],
          [],
          ltac:(M.monadic (
            let _ :=
              M.if_ (|
                M.call (|
                  "slt",
                  [
                    M.call (|
                      "sub",
                      [
                        M.get (| "dataEnd" |);
                        M.get (| "headStart" |)
                      ]
                    |);
                    [Literal.number 0]
                  ]
                |),
                ltac:(M.monadic (
                  let _ :=
                    M.call (|
                      "revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b",
                      []
                    |) in
                  tt
                ))
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "abi_encode_tuple",
          ["headStart"],
          ["tail"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["tail"],
                M.call (|
                  "add",
                  [
                    M.get (| "headStart" |);
                    [Literal.number 0]
                  ]
                |)
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "external_fun_call",
          [],
          [],
          ltac:(M.monadic (
            let _ :=
              M.if_ (|
                M.call (|
                  "callvalue",
                  []
                |),
                ltac:(M.monadic (
                  let _ :=
                    M.call (|
                      "revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb",
                      []
                    |) in
                  tt
                ))
              |) in
            let _ :=
              M.call (|
                "abi_decode",
                [
                  [Literal.number 4];
                  M.call (|
                    "calldatasize",
                    []
                  |)
                ]
              |) in
            let _ :=
              M.call (|
                "fun_call",
                []
              |) in
            let _ :=
              M.assign (|
                ["memPos"],
                Some (M.call (|
                  "allocate_unbounded",
                  []
                |))
              |) in
            let _ :=
              M.assign (|
                ["memEnd"],
                Some (M.call (|
                  "abi_encode_tuple",
                  [
                    M.get (| "memPos" |)
                  ]
                |))
              |) in
            let _ :=
              M.call (|
                "return",
                [
                  M.get (| "memPos" |);
                  M.call (|
                    "sub",
                    [
                      M.get (| "memEnd" |);
                      M.get (| "memPos" |)
                    ]
                  |)
                ]
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74",
          [],
          [],
          ltac:(M.monadic (
            let _ :=
              M.call (|
                "revert",
                [
                  [Literal.number 0];
                  [Literal.number 0]
                ]
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "cleanup_rational_by",
          ["value"],
          ["cleaned"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["cleaned"],
                M.get (| "value" |)
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "cleanup_uint256",
          ["value"],
          ["cleaned"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["cleaned"],
                M.get (| "value" |)
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "identity",
          ["value"],
          ["ret"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["ret"],
                M.get (| "value" |)
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "convert_rational_by_to_uint256",
          ["value"],
          ["converted"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["converted"],
                M.call (|
                  "cleanup_uint256",
                  [
                    M.call (|
                      "identity",
                      [
                        M.call (|
                          "cleanup_rational_by",
                          [
                            M.get (| "value" |)
                          ]
                        |)
                      ]
                    |)
                  ]
                |)
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "abi_encode_rational_by",
          ["value"; "pos"],
          [],
          ltac:(M.monadic (
            let _ :=
              M.call (|
                "mstore",
                [
                  M.get (| "pos" |);
                  M.call (|
                    "convert_rational_by_to_uint256",
                    [
                      M.get (| "value" |)
                    ]
                  |)
                ]
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "array_storeLengthForEncoding_string",
          ["pos"; "length"],
          ["updated_pos"],
          ltac:(M.monadic (
            let _ :=
              M.call (|
                "mstore",
                [
                  M.get (| "pos" |);
                  M.get (| "length" |)
                ]
              |) in
            let _ :=
              M.declare (|
                ["updated_pos"],
                M.call (|
                  "add",
                  [
                    M.get (| "pos" |);
                    [Literal.number 0x20]
                  ]
                |)
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "store_literal_in_memory_4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45",
          ["memPtr"],
          [],
          ltac:(M.monadic (
            let _ :=
              M.call (|
                "mstore",
                [
                  M.call (|
                    "add",
                    [
                      M.get (| "memPtr" |);
                      [Literal.number 0]
                    ]
                  |);
                  [Literal.string "616263"]
                ]
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "abi_encode_stringliteral_4e03",
          ["pos"],
          ["end"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["pos"],
                M.call (|
                  "array_storeLengthForEncoding_string",
                  [
                    M.get (| "pos" |);
                    [Literal.number 3]
                  ]
                |)
              |) in
            let _ :=
              M.call (|
                "store_literal_in_memory_4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45",
                [
                  M.get (| "pos" |)
                ]
              |) in
            let _ :=
              M.declare (|
                ["end"],
                M.call (|
                  "add",
                  [
                    M.get (| "pos" |);
                    [Literal.number 32]
                  ]
                |)
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "cleanup_bool",
          ["value"],
          ["cleaned"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["cleaned"],
                M.call (|
                  "iszero",
                  [
                    M.call (|
                      "iszero",
                      [
                        M.get (| "value" |)
                      ]
                    |)
                  ]
                |)
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "abi_encode_bool",
          ["value"; "pos"],
          [],
          ltac:(M.monadic (
            let _ :=
              M.call (|
                "mstore",
                [
                  M.get (| "pos" |);
                  M.call (|
                    "cleanup_bool",
                    [
                      M.get (| "value" |)
                    ]
                  |)
                ]
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "abi_encode_rational_by_stringliteral_4e03_bool",
          ["headStart"; "value0"; "value1"],
          ["tail"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["tail"],
                M.call (|
                  "add",
                  [
                    M.get (| "headStart" |);
                    [Literal.number 96]
                  ]
                |)
              |) in
            let _ :=
              M.call (|
                "abi_encode_rational_by",
                [
                  M.get (| "value0" |);
                  M.call (|
                    "add",
                    [
                      M.get (| "headStart" |);
                      [Literal.number 0]
                    ]
                  |)
                ]
              |) in
            let _ :=
              M.call (|
                "mstore",
                [
                  M.call (|
                    "add",
                    [
                      M.get (| "headStart" |);
                      [Literal.number 32]
                    ]
                  |);
                  M.call (|
                    "sub",
                    [
                      M.get (| "tail" |);
                      M.get (| "headStart" |)
                    ]
                  |)
                ]
              |) in
            let _ :=
              M.declare (|
                ["tail"],
                M.call (|
                  "abi_encode_stringliteral_4e03",
                  [
                    M.get (| "tail" |)
                  ]
                |)
              |) in
            let _ :=
              M.call (|
                "abi_encode_bool",
                [
                  M.get (| "value1" |);
                  M.call (|
                    "add",
                    [
                      M.get (| "headStart" |);
                      [Literal.number 64]
                    ]
                  |)
                ]
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "fun_call",
          [],
          [],
          ltac:(M.monadic (
            let _ :=
              M.assign (|
                ["expr"],
                Some ([Literal.number 0x01])
              |) in
            let _ :=
              M.assign (|
                ["expr_1"],
                Some ([Literal.number 0x01])
              |) in
            let _ :=
              M.assign (|
                ["_1"],
                Some ([Literal.number 0x0a6321261f8fd3728190e424705d7ec968fc4090923bd99f78033e386f8ef78c])
              |) in
            let _ :=
              M.assign (|
                ["_2"],
                Some (M.call (|
                  "allocate_unbounded",
                  []
                |))
              |) in
            let _ :=
              M.assign (|
                ["_3"],
                Some (M.call (|
                  "abi_encode_rational_by_stringliteral_4e03_bool",
                  [
                    M.get (| "_2" |);
                    M.get (| "expr" |);
                    M.get (| "expr_1" |)
                  ]
                |))
              |) in
            let _ :=
              M.call (|
                "log1",
                [
                  M.get (| "_2" |);
                  M.call (|
                    "sub",
                    [
                      M.get (| "_3" |);
                      M.get (| "_2" |)
                    ]
                  |);
                  M.get (| "_1" |)
                ]
              |) in
            let _ :=
              M.assign (|
                ["expr_2"],
                Some ([Literal.number 0x01])
              |) in
            let _ :=
              M.assign (|
                ["expr_3"],
                Some ([Literal.number 0x01])
              |) in
            let _ :=
              M.assign (|
                ["_4"],
                Some ([Literal.number 0x0a6321261f8fd3728190e424705d7ec968fc4090923bd99f78033e386f8ef78c])
              |) in
            let _ :=
              M.assign (|
                ["_5"],
                Some (M.call (|
                  "allocate_unbounded",
                  []
                |))
              |) in
            let _ :=
              M.assign (|
                ["_6"],
                Some (M.call (|
                  "abi_encode_rational_by_stringliteral_4e03_bool",
                  [
                    M.get (| "_5" |);
                    M.get (| "expr_3" |);
                    M.get (| "expr_2" |)
                  ]
                |))
              |) in
            let _ :=
              M.call (|
                "log1",
                [
                  M.get (| "_5" |);
                  M.call (|
                    "sub",
                    [
                      M.get (| "_6" |);
                      M.get (| "_5" |)
                    ]
                  |);
                  M.get (| "_4" |)
                ]
              |) in
            let _ :=
              M.assign (|
                ["expr_4"],
                Some ([Literal.number 0x01])
              |) in
            let _ :=
              M.assign (|
                ["expr_5"],
                Some ([Literal.number 0x01])
              |) in
            let _ :=
              M.assign (|
                ["_7"],
                Some ([Literal.number 0x0a6321261f8fd3728190e424705d7ec968fc4090923bd99f78033e386f8ef78c])
              |) in
            let _ :=
              M.assign (|
                ["_8"],
                Some (M.call (|
                  "allocate_unbounded",
                  []
                |))
              |) in
            let _ :=
              M.assign (|
                ["_9"],
                Some (M.call (|
                  "abi_encode_rational_by_stringliteral_4e03_bool",
                  [
                    M.get (| "_8" |);
                    M.get (| "expr_4" |);
                    M.get (| "expr_5" |)
                  ]
                |))
              |) in
            let _ :=
              M.call (|
                "log1",
                [
                  M.get (| "_8" |);
                  M.call (|
                    "sub",
                    [
                      M.get (| "_9" |);
                      M.get (| "_8" |)
                    ]
                  |);
                  M.get (| "_7" |)
                ]
              |) in
            let _ :=
              M.assign (|
                ["expr_6"],
                Some ([Literal.number 0x01])
              |) in
            let _ :=
              M.assign (|
                ["expr_7"],
                Some ([Literal.number 0x01])
              |) in
            let _ :=
              M.assign (|
                ["_10"],
                Some ([Literal.number 0x0a6321261f8fd3728190e424705d7ec968fc4090923bd99f78033e386f8ef78c])
              |) in
            let _ :=
              M.assign (|
                ["_11"],
                Some (M.call (|
                  "allocate_unbounded",
                  []
                |))
              |) in
            let _ :=
              M.assign (|
                ["_12"],
                Some (M.call (|
                  "abi_encode_rational_by_stringliteral_4e03_bool",
                  [
                    M.get (| "_11" |);
                    M.get (| "expr_7" |);
                    M.get (| "expr_6" |)
                  ]
                |))
              |) in
            let _ :=
              M.call (|
                "log1",
                [
                  M.get (| "_11" |);
                  M.call (|
                    "sub",
                    [
                      M.get (| "_12" |);
                      M.get (| "_11" |)
                    ]
                  |);
                  M.get (| "_10" |)
                ]
              |) in
            let _ :=
              M.assign (|
                ["expr_8"],
                Some ([Literal.number 0x01])
              |) in
            let _ :=
              M.assign (|
                ["expr_9"],
                Some ([Literal.number 0x01])
              |) in
            let _ :=
              M.assign (|
                ["_13"],
                Some ([Literal.number 0x0a6321261f8fd3728190e424705d7ec968fc4090923bd99f78033e386f8ef78c])
              |) in
            let _ :=
              M.assign (|
                ["_14"],
                Some (M.call (|
                  "allocate_unbounded",
                  []
                |))
              |) in
            let _ :=
              M.assign (|
                ["_15"],
                Some (M.call (|
                  "abi_encode_rational_by_stringliteral_4e03_bool",
                  [
                    M.get (| "_14" |);
                    M.get (| "expr_8" |);
                    M.get (| "expr_9" |)
                  ]
                |))
              |) in
            let _ :=
              M.call (|
                "log1",
                [
                  M.get (| "_14" |);
                  M.call (|
                    "sub",
                    [
                      M.get (| "_15" |);
                      M.get (| "_14" |)
                    ]
                  |);
                  M.get (| "_13" |)
                ]
              |) in
            let _ :=
              M.assign (|
                ["expr_10"],
                Some ([Literal.number 0x01])
              |) in
            let _ :=
              M.assign (|
                ["expr_11"],
                Some ([Literal.number 0x01])
              |) in
            let _ :=
              M.assign (|
                ["_16"],
                Some ([Literal.number 0x0a6321261f8fd3728190e424705d7ec968fc4090923bd99f78033e386f8ef78c])
              |) in
            let _ :=
              M.assign (|
                ["_17"],
                Some (M.call (|
                  "allocate_unbounded",
                  []
                |))
              |) in
            let _ :=
              M.assign (|
                ["_18"],
                Some (M.call (|
                  "abi_encode_rational_by_stringliteral_4e03_bool",
                  [
                    M.get (| "_17" |);
                    M.get (| "expr_11" |);
                    M.get (| "expr_10" |)
                  ]
                |))
              |) in
            let _ :=
              M.call (|
                "log1",
                [
                  M.get (| "_17" |);
                  M.call (|
                    "sub",
                    [
                      M.get (| "_18" |);
                      M.get (| "_17" |)
                    ]
                  |);
                  M.get (| "_16" |)
                ]
              |) in
            tt
          ))
        |) in
      tt
    )).

    Definition data : string :=
      "a264697066735822122090d9407cebc3a99214110e7820ec20d44c1e68b010814eff7de0389d6ab1948964736f6c634300081b0033".
  End C_49_deployed.
End C_49.
