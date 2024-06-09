(* Generated by solc *)
Require Import CoqOfSolidity.CoqOfSolidity.

Module C_16.
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
                [Literal.string "435f31365f6465706c6f796564"]
              ]
            |);
            M.call (|
              "datasize",
              [
                [Literal.string "435f31365f6465706c6f796564"]
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
                [Literal.string "435f31365f6465706c6f796564"]
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

  Module C_16_deployed.
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
          "cleanup_uint160",
          ["value"],
          ["cleaned"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["cleaned"],
                M.call (|
                  "and",
                  [
                    M.get (| "value" |);
                    M.call (|
                      "sub",
                      [
                        M.call (|
                          "shl",
                          [
                            [Literal.number 160];
                            [Literal.number 1]
                          ]
                        |);
                        [Literal.number 1]
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
          "convert_uint160_to_uint160",
          ["value"],
          ["converted"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["converted"],
                M.call (|
                  "cleanup_uint160",
                  [
                    M.call (|
                      "identity",
                      [
                        M.call (|
                          "cleanup_uint160",
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
          "convert_uint160_to_address",
          ["value"],
          ["converted"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["converted"],
                M.call (|
                  "convert_uint160_to_uint160",
                  [
                    M.get (| "value" |)
                  ]
                |)
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "convert_contract_C_to_address",
          ["value"],
          ["converted"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["converted"],
                M.call (|
                  "convert_uint160_to_address",
                  [
                    M.get (| "value" |)
                  ]
                |)
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
          "return_data_selector",
          [],
          ["sig"],
          ltac:(M.monadic (
            let _ :=
              M.if_ (|
                M.call (|
                  "gt",
                  [
                    M.call (|
                      "returndatasize",
                      []
                    |);
                    [Literal.number 3]
                  ]
                |),
                ltac:(M.monadic (
                  let _ :=
                    M.call (|
                      "returndatacopy",
                      [
                        [Literal.number 0];
                        [Literal.number 0];
                        [Literal.number 4]
                      ]
                    |) in
                  let _ :=
                    M.declare (|
                      ["sig"],
                      M.call (|
                        "shift_right_unsigned",
                        [
                          M.call (|
                            "mload",
                            [
                              [Literal.number 0]
                            ]
                          |)
                        ]
                      |)
                    |) in
                  tt
                ))
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "try_decode_error_message",
          [],
          ["ret"],
          ltac:(M.monadic (
            let _ :=
              M.if_ (|
                M.call (|
                  "lt",
                  [
                    M.call (|
                      "returndatasize",
                      []
                    |);
                    [Literal.number 0x44]
                  ]
                |),
                ltac:(M.monadic (
                  let _ :=
                    M.leave (||) in
                  tt
                ))
              |) in
            let _ :=
              M.assign (|
                ["data"],
                Some (M.call (|
                  "allocate_unbounded",
                  []
                |))
              |) in
            let _ :=
              M.call (|
                "returndatacopy",
                [
                  M.get (| "data" |);
                  [Literal.number 4];
                  M.call (|
                    "sub",
                    [
                      M.call (|
                        "returndatasize",
                        []
                      |);
                      [Literal.number 4]
                    ]
                  |)
                ]
              |) in
            let _ :=
              M.assign (|
                ["offset"],
                Some (M.call (|
                  "mload",
                  [
                    M.get (| "data" |)
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
                        M.get (| "offset" |);
                        [Literal.number 0xffffffffffffffff]
                      ]
                    |);
                    M.call (|
                      "gt",
                      [
                        M.call (|
                          "add",
                          [
                            M.get (| "offset" |);
                            [Literal.number 0x24]
                          ]
                        |);
                        M.call (|
                          "returndatasize",
                          []
                        |)
                      ]
                    |)
                  ]
                |),
                ltac:(M.monadic (
                  let _ :=
                    M.leave (||) in
                  tt
                ))
              |) in
            let _ :=
              M.assign (|
                ["msg"],
                Some (M.call (|
                  "add",
                  [
                    M.get (| "data" |);
                    M.get (| "offset" |)
                  ]
                |))
              |) in
            let _ :=
              M.assign (|
                ["length"],
                Some (M.call (|
                  "mload",
                  [
                    M.get (| "msg" |)
                  ]
                |))
              |) in
            let _ :=
              M.if_ (|
                M.call (|
                  "gt",
                  [
                    M.get (| "length" |);
                    [Literal.number 0xffffffffffffffff]
                  ]
                |),
                ltac:(M.monadic (
                  let _ :=
                    M.leave (||) in
                  tt
                ))
              |) in
            let _ :=
              M.assign (|
                ["end"],
                Some (M.call (|
                  "add",
                  [
                    M.call (|
                      "add",
                      [
                        M.get (| "msg" |);
                        [Literal.number 0x20]
                      ]
                    |);
                    M.get (| "length" |)
                  ]
                |))
              |) in
            let _ :=
              M.if_ (|
                M.call (|
                  "gt",
                  [
                    M.get (| "end" |);
                    M.call (|
                      "add",
                      [
                        M.get (| "data" |);
                        M.call (|
                          "sub",
                          [
                            M.call (|
                              "returndatasize",
                              []
                            |);
                            [Literal.number 4]
                          ]
                        |)
                      ]
                    |)
                  ]
                |),
                ltac:(M.monadic (
                  let _ :=
                    M.leave (||) in
                  tt
                ))
              |) in
            let _ :=
              M.call (|
                "finalize_allocation",
                [
                  M.get (| "data" |);
                  M.call (|
                    "add",
                    [
                      M.get (| "offset" |);
                      M.call (|
                        "add",
                        [
                          [Literal.number 0x20];
                          M.get (| "length" |)
                        ]
                      |)
                    ]
                  |)
                ]
              |) in
            let _ :=
              M.declare (|
                ["ret"],
                M.get (| "msg" |)
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
                ["expr_3_address"],
                Some (M.call (|
                  "address",
                  []
                |))
              |) in
            let _ :=
              M.assign (|
                ["expr_address"],
                Some (M.call (|
                  "convert_contract_C_to_address",
                  [
                    M.get (| "expr_3_address" |)
                  ]
                |))
              |) in
            let _ :=
              M.assign (|
                ["expr_functionSelector"],
                Some ([Literal.number 0x26121ff0])
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
                ["_1"],
                Some (M.call (|
                  "allocate_unbounded",
                  []
                |))
              |) in
            let _ :=
              M.call (|
                "mstore",
                [
                  M.get (| "_1" |);
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
                ["_2"],
                Some (M.call (|
                  "abi_encode_tuple",
                  [
                    M.call (|
                      "add",
                      [
                        M.get (| "_1" |);
                        [Literal.number 4]
                      ]
                    |)
                  ]
                |))
              |) in
            let _ :=
              M.assign (|
                ["trySuccessCondition"],
                Some (M.call (|
                  "call",
                  [
                    M.call (|
                      "gas",
                      []
                    |);
                    M.get (| "expr_address" |);
                    [Literal.number 0];
                    M.get (| "_1" |);
                    M.call (|
                      "sub",
                      [
                        M.get (| "_2" |);
                        M.get (| "_1" |)
                      ]
                    |);
                    M.get (| "_1" |);
                    [Literal.number 0]
                  ]
                |))
              |) in
            let _ :=
              M.if_ (|
                M.get (| "trySuccessCondition" |),
                ltac:(M.monadic (
                  let _ :=
                    M.assign (|
                      ["_3"],
                      Some ([Literal.number 0])
                    |) in
                  let _ :=
                    M.if_ (|
                      M.call (|
                        "gt",
                        [
                          M.get (| "_3" |);
                          M.call (|
                            "returndatasize",
                            []
                          |)
                        ]
                      |),
                      ltac:(M.monadic (
                        let _ :=
                          M.declare (|
                            ["_3"],
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
                        M.get (| "_1" |);
                        M.get (| "_3" |)
                      ]
                    |) in
                  let _ :=
                    M.call (|
                      "abi_decode_fromMemory",
                      [
                        M.get (| "_1" |);
                        M.call (|
                          "add",
                          [
                            M.get (| "_1" |);
                            M.get (| "_3" |)
                          ]
                        |)
                      ]
                    |) in
                  tt
                ))
              |) in
            let _ :=
              M.switch (|
                M.call (|
                  "iszero",
                  [
                    M.get (| "trySuccessCondition" |)
                  ]
                |),
                [
                  (
                    Some (Literal.number 0),
                    ltac:(M.monadic (
                      tt
                    ))            );
                  (
                    None,
                    ltac:(M.monadic (
                      let _ :=
                        M.assign (|
                          ["_4"],
                          Some ([Literal.number 1])
                        |) in
                      let _ :=
                        M.switch (|
                          M.call (|
                            "return_data_selector",
                            []
                          |),
                          [
                            (
                              Some (Literal.number 147028384),
                              ltac:(M.monadic (
                                let _ :=
                                  M.assign (|
                                    ["_5"],
                                    Some (M.call (|
                                      "try_decode_error_message",
                                      []
                                    |))
                                  |) in
                                let _ :=
                                  M.if_ (|
                                    M.get (| "_5" |),
                                    ltac:(M.monadic (
                                      let _ :=
                                        M.declare (|
                                          ["_4"],
                                          [Literal.number 0]
                                        |) in
                                      tt
                                    ))
                                  |) in
                                tt
                              ))                      )                    ]
                        |) in
                      let _ :=
                        M.if_ (|
                          M.get (| "_4" |),
                          ltac:(M.monadic (
                            let _ :=
                              M.call (|
                                "revert_forward",
                                []
                              |) in
                            tt
                          ))
                        |) in
                      tt
                    ))            )          ]
              |) in
            tt
          ))
        |) in
      tt
    )).

    Definition data : string :=
      "a2646970667358221220091b152510393c2f1952b8d6be24da1946ed87d29464fc6c432457b6fba1fd8364736f6c634300081b0033".
  End C_16_deployed.
End C_16.
