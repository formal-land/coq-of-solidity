(* Generated by solc *)
Require Import CoqOfSolidity.CoqOfSolidity.

Module C_45.
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
                [Literal.string "435f34355f6465706c6f796564"]
              ]
            |);
            M.call (|
              "datasize",
              [
                [Literal.string "435f34355f6465706c6f796564"]
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
                [Literal.string "435f34355f6465706c6f796564"]
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

  Module C_45_deployed.
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
                      Some (Literal.number 0x26121ff0),
                      ltac:(M.monadic (
                        let _ :=
                          M.call (|
                            "external_fun_f",
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
          "external_fun_f",
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
                "fun_f",
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
          "zero_value_for_split_uint256",
          [],
          ["ret"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["ret"],
                [Literal.number 0]
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "revert_error_0cc013b6b3b6beabea4e3a74a6d380f0df81852ca99887912475e1f66b2a2c20",
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
          "round_up_to_mul_of",
          ["value"],
          ["result"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["result"],
                M.call (|
                  "and",
                  [
                    M.call (|
                      "add",
                      [
                        M.get (| "value" |);
                        [Literal.number 31]
                      ]
                    |);
                    M.call (|
                      "not",
                      [
                        [Literal.number 31]
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
          "panic_error_0x41",
          [],
          [],
          ltac:(M.monadic (
            let _ :=
              M.call (|
                "mstore",
                [
                  [Literal.number 0];
                  M.call (|
                    "shl",
                    [
                      [Literal.number 224];
                      [Literal.number 0x4e487b71]
                    ]
                  |)
                ]
              |) in
            let _ :=
              M.call (|
                "mstore",
                [
                  [Literal.number 4];
                  [Literal.number 0x41]
                ]
              |) in
            let _ :=
              M.call (|
                "revert",
                [
                  [Literal.number 0];
                  [Literal.number 0x24]
                ]
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "finalize_allocation",
          ["memPtr"; "size"],
          [],
          ltac:(M.monadic (
            let _ :=
              M.assign (|
                ["newFreePtr"],
                Some (M.call (|
                  "add",
                  [
                    M.get (| "memPtr" |);
                    M.call (|
                      "round_up_to_mul_of",
                      [
                        M.get (| "size" |)
                      ]
                    |)
                  ]
                |))
              |) in
            let _ :=
              M.if_ (|
                M.call (|
                  "or",
                  [
                    M.call (|
                      "gt",
                      [
                        M.get (| "newFreePtr" |);
                        [Literal.number 0xffffffffffffffff]
                      ]
                    |);
                    M.call (|
                      "lt",
                      [
                        M.get (| "newFreePtr" |);
                        M.get (| "memPtr" |)
                      ]
                    |)
                  ]
                |),
                ltac:(M.monadic (
                  let _ :=
                    M.call (|
                      "panic_error_0x41",
                      []
                    |) in
                  tt
                ))
              |) in
            let _ :=
              M.call (|
                "mstore",
                [
                  [Literal.number 64];
                  M.get (| "newFreePtr" |)
                ]
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "shift_left",
          ["value"],
          ["newValue"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["newValue"],
                M.call (|
                  "shl",
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
          "abi_decode_fromMemory",
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
          "abi_encode_uint256_to_uint256_library",
          ["value"; "pos"],
          [],
          ltac:(M.monadic (
            let _ :=
              M.call (|
                "mstore",
                [
                  M.get (| "pos" |);
                  M.call (|
                    "cleanup_uint256",
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
          "abi_encode_uint256",
          ["headStart"; "value0"],
          ["tail"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["tail"],
                M.call (|
                  "add",
                  [
                    M.get (| "headStart" |);
                    [Literal.number 32]
                  ]
                |)
              |) in
            let _ :=
              M.call (|
                "abi_encode_uint256_to_uint256_library",
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
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "revert_forward",
          [],
          [],
          ltac:(M.monadic (
            let _ :=
              M.assign (|
                ["pos"],
                Some (M.call (|
                  "allocate_unbounded",
                  []
                |))
              |) in
            let _ :=
              M.call (|
                "returndatacopy",
                [
                  M.get (| "pos" |);
                  [Literal.number 0];
                  M.call (|
                    "returndatasize",
                    []
                  |)
                ]
              |) in
            let _ :=
              M.call (|
                "revert",
                [
                  M.get (| "pos" |);
                  M.call (|
                    "returndatasize",
                    []
                  |)
                ]
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "fun_f",
          [],
          [],
          ltac:(M.monadic (
            let _ :=
              M.assign (|
                ["var_x"],
                None
              |) in
            let _ :=
              M.assign (|
                ["zero_uint256"],
                Some (M.call (|
                  "zero_value_for_split_uint256",
                  []
                |))
              |) in
            let _ :=
              M.declare (|
                ["var_x"],
                M.get (| "zero_uint256" |)
              |) in
            let _ :=
              M.assign (|
                ["_1"],
                Some (M.get (| "var_x" |))
              |) in
            let _ :=
              M.assign (|
                ["expr"],
                Some (M.get (| "_1" |))
              |) in
            let _ :=
              M.assign (|
                ["expr_self"],
                Some (M.get (| "expr" |))
              |) in
            let _ :=
              M.assign (|
                ["expr_address"],
                Some (M.call (|
                  "linkersymbol",
                  [
                    [Literal.string "2f686f6d652f6775696c6c61756d652f4465736b746f702f536f6c69646974792f736f6c69646974792f746573742f6c6962736f6c69646974792f73796e74617854657374732f7573696e672f6c6962726172795f696e736964655f636f6e74726163742e736f6c3a4c"]
                  ]
                |))
              |) in
            let _ :=
              M.assign (|
                ["expr_30_functionSelector"],
                Some ([Literal.number 1132043946])
              |) in
            let _ :=
              M.if_ (|
                M.call (|
                  "iszero",
                  [
                    M.call (|
                      "extcodesize",
                      [
                        M.get (| "expr_address" |)
                      ]
                    |)
                  ]
                |),
                ltac:(M.monadic (
                  let _ :=
                    M.call (|
                      "revert_error_0cc013b6b3b6beabea4e3a74a6d380f0df81852ca99887912475e1f66b2a2c20",
                      []
                    |) in
                  tt
                ))
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
              M.call (|
                "mstore",
                [
                  M.get (| "_2" |);
                  M.call (|
                    "shift_left",
                    [
                      M.get (| "expr_30_functionSelector" |)
                    ]
                  |)
                ]
              |) in
            let _ :=
              M.assign (|
                ["_3"],
                Some (M.call (|
                  "abi_encode_uint256",
                  [
                    M.call (|
                      "add",
                      [
                        M.get (| "_2" |);
                        [Literal.number 4]
                      ]
                    |);
                    M.get (| "expr_self" |)
                  ]
                |))
              |) in
            let _ :=
              M.assign (|
                ["_4"],
                Some (M.call (|
                  "delegatecall",
                  [
                    M.call (|
                      "gas",
                      []
                    |);
                    M.get (| "expr_address" |);
                    M.get (| "_2" |);
                    M.call (|
                      "sub",
                      [
                        M.get (| "_3" |);
                        M.get (| "_2" |)
                      ]
                    |);
                    M.get (| "_2" |);
                    [Literal.number 0]
                  ]
                |))
              |) in
            let _ :=
              M.if_ (|
                M.call (|
                  "iszero",
                  [
                    M.get (| "_4" |)
                  ]
                |),
                ltac:(M.monadic (
                  let _ :=
                    M.call (|
                      "revert_forward",
                      []
                    |) in
                  tt
                ))
              |) in
            let _ :=
              M.if_ (|
                M.get (| "_4" |),
                ltac:(M.monadic (
                  let _ :=
                    M.assign (|
                      ["_5"],
                      Some ([Literal.number 0])
                    |) in
                  let _ :=
                    M.if_ (|
                      M.call (|
                        "gt",
                        [
                          M.get (| "_5" |);
                          M.call (|
                            "returndatasize",
                            []
                          |)
                        ]
                      |),
                      ltac:(M.monadic (
                        let _ :=
                          M.declare (|
                            ["_5"],
                            M.call (|
                              "returndatasize",
                              []
                            |)
                          |) in
                        tt
                      ))
                    |) in
                  let _ :=
                    M.call (|
                      "finalize_allocation",
                      [
                        M.get (| "_2" |);
                        M.get (| "_5" |)
                      ]
                    |) in
                  let _ :=
                    M.call (|
                      "abi_decode_fromMemory",
                      [
                        M.get (| "_2" |);
                        M.call (|
                          "add",
                          [
                            M.get (| "_2" |);
                            M.get (| "_5" |)
                          ]
                        |)
                      ]
                    |) in
                  tt
                ))
              |) in
            let _ :=
              M.assign (|
                ["_6"],
                Some (M.get (| "var_x" |))
              |) in
            let _ :=
              M.assign (|
                ["expr_1"],
                Some (M.get (| "_6" |))
              |) in
            let _ :=
              M.assign (|
                ["expr_35_self"],
                Some (M.get (| "expr_1" |))
              |) in
            let _ :=
              M.assign (|
                ["expr_35_address"],
                Some (M.call (|
                  "linkersymbol",
                  [
                    [Literal.string "2f686f6d652f6775696c6c61756d652f4465736b746f702f536f6c69646974792f736f6c69646974792f746573742f6c6962736f6c69646974792f73796e74617854657374732f7573696e672f6c6962726172795f696e736964655f636f6e74726163742e736f6c3a4c"]
                  ]
                |))
              |) in
            let _ :=
              M.assign (|
                ["expr_functionSelector"],
                Some ([Literal.number 810055633])
              |) in
            let _ :=
              M.if_ (|
                M.call (|
                  "iszero",
                  [
                    M.call (|
                      "extcodesize",
                      [
                        M.get (| "expr_35_address" |)
                      ]
                    |)
                  ]
                |),
                ltac:(M.monadic (
                  let _ :=
                    M.call (|
                      "revert_error_0cc013b6b3b6beabea4e3a74a6d380f0df81852ca99887912475e1f66b2a2c20",
                      []
                    |) in
                  tt
                ))
              |) in
            let _ :=
              M.assign (|
                ["_7"],
                Some (M.call (|
                  "allocate_unbounded",
                  []
                |))
              |) in
            let _ :=
              M.call (|
                "mstore",
                [
                  M.get (| "_7" |);
                  M.call (|
                    "shift_left",
                    [
                      M.get (| "expr_functionSelector" |)
                    ]
                  |)
                ]
              |) in
            let _ :=
              M.assign (|
                ["_8"],
                Some (M.call (|
                  "abi_encode_uint256",
                  [
                    M.call (|
                      "add",
                      [
                        M.get (| "_7" |);
                        [Literal.number 4]
                      ]
                    |);
                    M.get (| "expr_35_self" |)
                  ]
                |))
              |) in
            let _ :=
              M.assign (|
                ["_9"],
                Some (M.call (|
                  "delegatecall",
                  [
                    M.call (|
                      "gas",
                      []
                    |);
                    M.get (| "expr_35_address" |);
                    M.get (| "_7" |);
                    M.call (|
                      "sub",
                      [
                        M.get (| "_8" |);
                        M.get (| "_7" |)
                      ]
                    |);
                    M.get (| "_7" |);
                    [Literal.number 0]
                  ]
                |))
              |) in
            let _ :=
              M.if_ (|
                M.call (|
                  "iszero",
                  [
                    M.get (| "_9" |)
                  ]
                |),
                ltac:(M.monadic (
                  let _ :=
                    M.call (|
                      "revert_forward",
                      []
                    |) in
                  tt
                ))
              |) in
            let _ :=
              M.if_ (|
                M.get (| "_9" |),
                ltac:(M.monadic (
                  let _ :=
                    M.assign (|
                      ["_10"],
                      Some ([Literal.number 0])
                    |) in
                  let _ :=
                    M.if_ (|
                      M.call (|
                        "gt",
                        [
                          M.get (| "_10" |);
                          M.call (|
                            "returndatasize",
                            []
                          |)
                        ]
                      |),
                      ltac:(M.monadic (
                        let _ :=
                          M.declare (|
                            ["_10"],
                            M.call (|
                              "returndatasize",
                              []
                            |)
                          |) in
                        tt
                      ))
                    |) in
                  let _ :=
                    M.call (|
                      "finalize_allocation",
                      [
                        M.get (| "_7" |);
                        M.get (| "_10" |)
                      ]
                    |) in
                  let _ :=
                    M.call (|
                      "abi_decode_fromMemory",
                      [
                        M.get (| "_7" |);
                        M.call (|
                          "add",
                          [
                            M.get (| "_7" |);
                            M.get (| "_10" |)
                          ]
                        |)
                      ]
                    |) in
                  tt
                ))
              |) in
            tt
          ))
        |) in
      tt
    )).

    Definition data : string :=
      "a2646970667358221220802045fe353f5480cc10f679598df186b735b48b573b0c2c71c2af0859ac460d64736f6c634300081b0033".
  End C_45_deployed.
End C_45.
