(* Generated by solc *)
Require Import CoqOfSolidity.CoqOfSolidity.

Module C_39.
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
                [Literal.string "435f33395f6465706c6f796564"]
              ]
            |);
            M.call (|
              "datasize",
              [
                [Literal.string "435f33395f6465706c6f796564"]
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
                [Literal.string "435f33395f6465706c6f796564"]
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

  Module C_39_deployed.
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
                      Some (Literal.number 0xe931873f),
                      ltac:(M.monadic (
                        let _ :=
                          M.call (|
                            "external_fun_pushEmpty",
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
          "validator_revert_uint256",
          ["value"],
          [],
          ltac:(M.monadic (
            let _ :=
              M.if_ (|
                M.call (|
                  "iszero",
                  [
                    M.call (|
                      "eq",
                      [
                        M.get (| "value" |);
                        M.call (|
                          "cleanup_uint256",
                          [
                            M.get (| "value" |)
                          ]
                        |)
                      ]
                    |)
                  ]
                |),
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
          ))
        |) in
      let _ :=
        M.function (|
          "abi_decode_uint256",
          ["offset"; "end"],
          ["value"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["value"],
                M.call (|
                  "calldataload",
                  [
                    M.get (| "offset" |)
                  ]
                |)
              |) in
            let _ :=
              M.call (|
                "validator_revert_uint256",
                [
                  M.get (| "value" |)
                ]
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "abi_decode_tuple_uint256",
          ["headStart"; "dataEnd"],
          ["value0"],
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
                    [Literal.number 32]
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
            let _ :=
              M.assign (|
                ["offset"],
                Some ([Literal.number 0])
              |) in
            let _ :=
              M.declare (|
                ["value0"],
                M.call (|
                  "abi_decode_uint256",
                  [
                    M.call (|
                      "add",
                      [
                        M.get (| "headStart" |);
                        M.get (| "offset" |)
                      ]
                    |);
                    M.get (| "dataEnd" |)
                  ]
                |)
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
          "external_fun_pushEmpty",
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
              M.assign (|
                ["param"],
                Some (M.call (|
                  "abi_decode_tuple_uint256",
                  [
                    [Literal.number 4];
                    M.call (|
                      "calldatasize",
                      []
                    |)
                  ]
                |))
              |) in
            let _ :=
              M.call (|
                "fun_pushEmpty",
                [
                  M.get (| "param" |)
                ]
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
          "array_length_array_uint256_dyn_storage",
          ["value"],
          ["length"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["length"],
                M.call (|
                  "sload",
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
          "convert_array_array_uint256_dyn_storage_to_array_uint256_dyn_ptr",
          ["value"],
          ["converted"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["converted"],
                M.get (| "value" |)
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
          "array_length_array_uint256_dyn_storage_ptr",
          ["value"],
          ["length"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["length"],
                M.call (|
                  "sload",
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
          "panic_error_0x32",
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
                  [Literal.number 0x32]
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
          "array_dataslot_array_uint256_dyn_storage_ptr",
          ["ptr"],
          ["data"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["data"],
                M.get (| "ptr" |)
              |) in
            let _ :=
              M.call (|
                "mstore",
                [
                  [Literal.number 0];
                  M.get (| "ptr" |)
                ]
              |) in
            let _ :=
              M.declare (|
                ["data"],
                M.call (|
                  "keccak256",
                  [
                    [Literal.number 0];
                    [Literal.number 0x20]
                  ]
                |)
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "storage_array_index_access_uint256_dyn_ptr",
          ["array"; "index"],
          ["slot";
      "offset"],
          ltac:(M.monadic (
            let _ :=
              M.assign (|
                ["arrayLength"],
                Some (M.call (|
                  "array_length_array_uint256_dyn_storage_ptr",
                  [
                    M.get (| "array" |)
                  ]
                |))
              |) in
            let _ :=
              M.if_ (|
                M.call (|
                  "iszero",
                  [
                    M.call (|
                      "lt",
                      [
                        M.get (| "index" |);
                        M.get (| "arrayLength" |)
                      ]
                    |)
                  ]
                |),
                ltac:(M.monadic (
                  let _ :=
                    M.call (|
                      "panic_error_0x32",
                      []
                    |) in
                  tt
                ))
              |) in
            let _ :=
              M.assign (|
                ["dataArea"],
                Some (M.call (|
                  "array_dataslot_array_uint256_dyn_storage_ptr",
                  [
                    M.get (| "array" |)
                  ]
                |))
              |) in
            let _ :=
              M.declare (|
                ["slot"],
                M.call (|
                  "add",
                  [
                    M.get (| "dataArea" |);
                    M.call (|
                      "mul",
                      [
                        M.get (| "index" |);
                        [Literal.number 1]
                      ]
                    |)
                  ]
                |)
              |) in
            let _ :=
              M.declare (|
                ["offset"],
                [Literal.number 0]
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "array_push_zero_array_uint256_dyn_storage_ptr",
          ["array"],
          ["slot";
      "offset"],
          ltac:(M.monadic (
            let _ :=
              M.assign (|
                ["oldLen"],
                Some (M.call (|
                  "array_length_array_uint256_dyn_storage_ptr",
                  [
                    M.get (| "array" |)
                  ]
                |))
              |) in
            let _ :=
              M.if_ (|
                M.call (|
                  "iszero",
                  [
                    M.call (|
                      "lt",
                      [
                        M.get (| "oldLen" |);
                        [Literal.number 18446744073709551616]
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
                "sstore",
                [
                  M.get (| "array" |);
                  M.call (|
                    "add",
                    [
                      M.get (| "oldLen" |);
                      [Literal.number 1]
                    ]
                  |)
                ]
              |) in
            let _ :=
              M.declare (|
                ["slot"; "offset"],
                M.call (|
                  "storage_array_index_access_uint256_dyn_ptr",
                  [
                    M.get (| "array" |);
                    M.get (| "oldLen" |)
                  ]
                |)
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "shift_right_unsigned_dynamic",
          ["bits"; "value"],
          ["newValue"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["newValue"],
                M.call (|
                  "shr",
                  [
                    M.get (| "bits" |);
                    M.get (| "value" |)
                  ]
                |)
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "cleanup_from_storage_uint256",
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
          "extract_from_storage_value_dynamict_uint256",
          ["slot_value"; "offset"],
          ["value"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["value"],
                M.call (|
                  "cleanup_from_storage_uint256",
                  [
                    M.call (|
                      "shift_right_unsigned_dynamic",
                      [
                        M.call (|
                          "mul",
                          [
                            M.get (| "offset" |);
                            [Literal.number 8]
                          ]
                        |);
                        M.get (| "slot_value" |)
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
          "read_from_storage_split_dynamic_uint256",
          ["slot"; "offset"],
          ["value"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["value"],
                M.call (|
                  "extract_from_storage_value_dynamict_uint256",
                  [
                    M.call (|
                      "sload",
                      [
                        M.get (| "slot" |)
                      ]
                    |);
                    M.get (| "offset" |)
                  ]
                |)
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
          "increment_wrapping_uint256",
          ["value"],
          ["ret"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["ret"],
                M.call (|
                  "cleanup_uint256",
                  [
                    M.call (|
                      "add",
                      [
                        M.get (| "value" |);
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
          "array_dataslot_array_uint256_dyn_storage",
          ["ptr"],
          ["data"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["data"],
                M.get (| "ptr" |)
              |) in
            let _ :=
              M.call (|
                "mstore",
                [
                  [Literal.number 0];
                  M.get (| "ptr" |)
                ]
              |) in
            let _ :=
              M.declare (|
                ["data"],
                M.call (|
                  "keccak256",
                  [
                    [Literal.number 0];
                    [Literal.number 0x20]
                  ]
                |)
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "storage_array_index_access_uint256_dyn",
          ["array"; "index"],
          ["slot";
      "offset"],
          ltac:(M.monadic (
            let _ :=
              M.assign (|
                ["arrayLength"],
                Some (M.call (|
                  "array_length_array_uint256_dyn_storage",
                  [
                    M.get (| "array" |)
                  ]
                |))
              |) in
            let _ :=
              M.if_ (|
                M.call (|
                  "iszero",
                  [
                    M.call (|
                      "lt",
                      [
                        M.get (| "index" |);
                        M.get (| "arrayLength" |)
                      ]
                    |)
                  ]
                |),
                ltac:(M.monadic (
                  let _ :=
                    M.call (|
                      "panic_error_0x32",
                      []
                    |) in
                  tt
                ))
              |) in
            let _ :=
              M.assign (|
                ["dataArea"],
                Some (M.call (|
                  "array_dataslot_array_uint256_dyn_storage",
                  [
                    M.get (| "array" |)
                  ]
                |))
              |) in
            let _ :=
              M.declare (|
                ["slot"],
                M.call (|
                  "add",
                  [
                    M.get (| "dataArea" |);
                    M.call (|
                      "mul",
                      [
                        M.get (| "index" |);
                        [Literal.number 1]
                      ]
                    |)
                  ]
                |)
              |) in
            let _ :=
              M.declare (|
                ["offset"],
                [Literal.number 0]
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "require_helper",
          ["condition"],
          [],
          ltac:(M.monadic (
            let _ :=
              M.if_ (|
                M.call (|
                  "iszero",
                  [
                    M.get (| "condition" |)
                  ]
                |),
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
          ))
        |) in
      let _ :=
        M.function (|
          "fun_pushEmpty",
          ["var_len"],
          [],
          ltac:(M.monadic (
            let _ :=
              let _ :=
                tt in
              M.for_ (|
                [Literal.number 1],
                ltac:(M.monadic (
                  tt
                )),
                ltac:(M.monadic (
                  let _ :=
                    M.assign (|
                      ["_1_slot"],
                      Some ([Literal.number 0x00])
                    |) in
                  let _ :=
                    M.assign (|
                      ["expr_slot"],
                      Some (M.get (| "_1_slot" |))
                    |) in
                  let _ :=
                    M.assign (|
                      ["expr"],
                      Some (M.call (|
                        "array_length_array_uint256_dyn_storage",
                        [
                          M.get (| "expr_slot" |)
                        ]
                      |))
                    |) in
                  let _ :=
                    M.assign (|
                      ["_1"],
                      Some (M.get (| "var_len" |))
                    |) in
                  let _ :=
                    M.assign (|
                      ["expr_1"],
                      Some (M.get (| "_1" |))
                    |) in
                  let _ :=
                    M.assign (|
                      ["expr_2"],
                      Some (M.call (|
                        "lt",
                        [
                          M.call (|
                            "cleanup_uint256",
                            [
                              M.get (| "expr" |)
                            ]
                          |);
                          M.call (|
                            "cleanup_uint256",
                            [
                              M.get (| "expr_1" |)
                            ]
                          |)
                        ]
                      |))
                    |) in
                  let _ :=
                    M.if_ (|
                      M.call (|
                        "iszero",
                        [
                          M.get (| "expr_2" |)
                        ]
                      |),
                      ltac:(M.monadic (
                        let _ :=
                          M.break (||) in
                        tt
                      ))
                    |) in
                  let _ :=
                    M.assign (|
                      ["_slot"],
                      Some ([Literal.number 0x00])
                    |) in
                  let _ :=
                    M.assign (|
                      ["expr_12_slot"],
                      Some (M.get (| "_slot" |))
                    |) in
                  let _ :=
                    M.assign (|
                      ["expr_self_slot"],
                      Some (M.call (|
                        "convert_array_array_uint256_dyn_storage_to_array_uint256_dyn_ptr",
                        [
                          M.get (| "expr_12_slot" |)
                        ]
                      |))
                    |) in
                  let _ :=
                    M.assign (|
                      ["_2"; "_3"],
                      Some (M.call (|
                        "array_push_zero_array_uint256_dyn_storage_ptr",
                        [
                          M.get (| "expr_self_slot" |)
                        ]
                      |))
                    |) in
                  tt
                ))
              |) in
            let _ :=
              M.assign (|
                ["expr_3"],
                Some ([Literal.number 0x00])
              |) in
            let _ :=
              M.assign (|
                ["var_i"],
                Some (M.call (|
                  "convert_rational_by_to_uint256",
                  [
                    M.get (| "expr_3" |)
                  ]
                |))
              |) in
            let _ :=
              let _ :=
                tt in
              M.for_ (|
                [Literal.number 1],
                ltac:(M.monadic (
                  let _ :=
                    M.assign (|
                      ["_4"],
                      Some (M.get (| "var_i" |))
                    |) in
                  let _ :=
                    M.assign (|
                      ["_5"],
                      Some (M.call (|
                        "increment_wrapping_uint256",
                        [
                          M.get (| "_4" |)
                        ]
                      |))
                    |) in
                  let _ :=
                    M.declare (|
                      ["var_i"],
                      M.get (| "_5" |)
                    |) in
                  tt
                )),
                ltac:(M.monadic (
                  let _ :=
                    M.assign (|
                      ["_6"],
                      Some (M.get (| "var_i" |))
                    |) in
                  let _ :=
                    M.assign (|
                      ["expr_4"],
                      Some (M.get (| "_6" |))
                    |) in
                  let _ :=
                    M.assign (|
                      ["_7"],
                      Some (M.get (| "var_len" |))
                    |) in
                  let _ :=
                    M.assign (|
                      ["expr_5"],
                      Some (M.get (| "_7" |))
                    |) in
                  let _ :=
                    M.assign (|
                      ["expr_6"],
                      Some (M.call (|
                        "lt",
                        [
                          M.call (|
                            "cleanup_uint256",
                            [
                              M.get (| "expr_4" |)
                            ]
                          |);
                          M.call (|
                            "cleanup_uint256",
                            [
                              M.get (| "expr_5" |)
                            ]
                          |)
                        ]
                      |))
                    |) in
                  let _ :=
                    M.if_ (|
                      M.call (|
                        "iszero",
                        [
                          M.get (| "expr_6" |)
                        ]
                      |),
                      ltac:(M.monadic (
                        let _ :=
                          M.break (||) in
                        tt
                      ))
                    |) in
                  let _ :=
                    M.assign (|
                      ["_11_slot"],
                      Some ([Literal.number 0x00])
                    |) in
                  let _ :=
                    M.assign (|
                      ["expr_29_slot"],
                      Some (M.get (| "_11_slot" |))
                    |) in
                  let _ :=
                    M.assign (|
                      ["_8"],
                      Some (M.get (| "var_i" |))
                    |) in
                  let _ :=
                    M.assign (|
                      ["expr_7"],
                      Some (M.get (| "_8" |))
                    |) in
                  let _ :=
                    M.assign (|
                      ["_9"; "_10"],
                      Some (M.call (|
                        "storage_array_index_access_uint256_dyn",
                        [
                          M.get (| "expr_29_slot" |);
                          M.get (| "expr_7" |)
                        ]
                      |))
                    |) in
                  let _ :=
                    M.assign (|
                      ["_11"],
                      Some (M.call (|
                        "read_from_storage_split_dynamic_uint256",
                        [
                          M.get (| "_9" |);
                          M.get (| "_10" |)
                        ]
                      |))
                    |) in
                  let _ :=
                    M.assign (|
                      ["expr_8"],
                      Some (M.get (| "_11" |))
                    |) in
                  let _ :=
                    M.assign (|
                      ["expr_9"],
                      Some ([Literal.number 0x00])
                    |) in
                  let _ :=
                    M.assign (|
                      ["expr_10"],
                      Some (M.call (|
                        "eq",
                        [
                          M.call (|
                            "cleanup_uint256",
                            [
                              M.get (| "expr_8" |)
                            ]
                          |);
                          M.call (|
                            "convert_rational_by_to_uint256",
                            [
                              M.get (| "expr_9" |)
                            ]
                          |)
                        ]
                      |))
                    |) in
                  let _ :=
                    M.call (|
                      "require_helper",
                      [
                        M.get (| "expr_10" |)
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
      "a26469706673582212206845fc15c7db094f82f3bc9062c5995dedae2b08e16a02a2a664b779b54cbf7b64736f6c634300081b0033".
  End C_39_deployed.
End C_39.
