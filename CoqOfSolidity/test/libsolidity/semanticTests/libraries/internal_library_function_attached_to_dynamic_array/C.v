(* Generated by solc *)
Require Import CoqOfSolidity.CoqOfSolidity.

Module C_55.
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
                [Literal.string "435f35355f6465706c6f796564"]
              ]
            |);
            M.call (|
              "datasize",
              [
                [Literal.string "435f35355f6465706c6f796564"]
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
                [Literal.string "435f35355f6465706c6f796564"]
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

  Module C_55_deployed.
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
                      Some (Literal.number 0x5dd0a830),
                      ltac:(M.monadic (
                        let _ :=
                          M.call (|
                            "external_fun_secondItem",
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
          "abi_encode_uint256_to_uint256",
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
                "abi_encode_uint256_to_uint256",
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
          "external_fun_secondItem",
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
              M.assign (|
                ["ret"],
                Some (M.call (|
                  "fun_secondItem",
                  []
                |))
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
                  "abi_encode_uint256",
                  [
                    M.get (| "memPos" |);
                    M.get (| "ret" |)
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
          "cleanup_rational_by_1",
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
          "convert_rational_2_by_1_to_uint256",
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
                          "cleanup_rational_by_1",
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
          "allocate_memory",
          ["size"],
          ["memPtr"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["memPtr"],
                M.call (|
                  "allocate_unbounded",
                  []
                |)
              |) in
            let _ :=
              M.call (|
                "finalize_allocation",
                [
                  M.get (| "memPtr" |);
                  M.get (| "size" |)
                ]
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "array_allocation_size_array_uint256_dyn",
          ["length"],
          ["size"],
          ltac:(M.monadic (
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
                    M.call (|
                      "panic_error_0x41",
                      []
                    |) in
                  tt
                ))
              |) in
            let _ :=
              M.declare (|
                ["size"],
                M.call (|
                  "mul",
                  [
                    M.get (| "length" |);
                    [Literal.number 0x20]
                  ]
                |)
              |) in
            let _ :=
              M.declare (|
                ["size"],
                M.call (|
                  "add",
                  [
                    M.get (| "size" |);
                    [Literal.number 0x20]
                  ]
                |)
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "allocate_memory_array_array_uint256_dyn",
          ["length"],
          ["memPtr"],
          ltac:(M.monadic (
            let _ :=
              M.assign (|
                ["allocSize"],
                Some (M.call (|
                  "array_allocation_size_array_uint256_dyn",
                  [
                    M.get (| "length" |)
                  ]
                |))
              |) in
            let _ :=
              M.declare (|
                ["memPtr"],
                M.call (|
                  "allocate_memory",
                  [
                    M.get (| "allocSize" |)
                  ]
                |)
              |) in
            let _ :=
              M.call (|
                "mstore",
                [
                  M.get (| "memPtr" |);
                  M.get (| "length" |)
                ]
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "zero_memory_chunk_uint256",
          ["dataStart"; "dataSizeInBytes"],
          [],
          ltac:(M.monadic (
            let _ :=
              M.call (|
                "calldatacopy",
                [
                  M.get (| "dataStart" |);
                  M.call (|
                    "calldatasize",
                    []
                  |);
                  M.get (| "dataSizeInBytes" |)
                ]
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "allocate_and_zero_memory_array_array_uint256_dyn",
          ["length"],
          ["memPtr"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["memPtr"],
                M.call (|
                  "allocate_memory_array_array_uint256_dyn",
                  [
                    M.get (| "length" |)
                  ]
                |)
              |) in
            let _ :=
              M.assign (|
                ["dataStart"],
                Some (M.get (| "memPtr" |))
              |) in
            let _ :=
              M.assign (|
                ["dataSize"],
                Some (M.call (|
                  "array_allocation_size_array_uint256_dyn",
                  [
                    M.get (| "length" |)
                  ]
                |))
              |) in
            let _ :=
              M.declare (|
                ["dataStart"],
                M.call (|
                  "add",
                  [
                    M.get (| "dataStart" |);
                    [Literal.number 32]
                  ]
                |)
              |) in
            let _ :=
              M.declare (|
                ["dataSize"],
                M.call (|
                  "sub",
                  [
                    M.get (| "dataSize" |);
                    [Literal.number 32]
                  ]
                |)
              |) in
            let _ :=
              M.call (|
                "zero_memory_chunk_uint256",
                [
                  M.get (| "dataStart" |);
                  M.get (| "dataSize" |)
                ]
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "cleanup_rational_17_by",
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
                          "cleanup_rational_17_by",
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
          "array_length_array_uint256_dyn",
          ["value"],
          ["length"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["length"],
                M.call (|
                  "mload",
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
          "memory_array_index_access_uint256_dyn",
          ["baseRef"; "index"],
          ["addr"],
          ltac:(M.monadic (
            let _ :=
              M.if_ (|
                M.call (|
                  "iszero",
                  [
                    M.call (|
                      "lt",
                      [
                        M.get (| "index" |);
                        M.call (|
                          "array_length_array_uint256_dyn",
                          [
                            M.get (| "baseRef" |)
                          ]
                        |)
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
                ["offset"],
                Some (M.call (|
                  "mul",
                  [
                    M.get (| "index" |);
                    [Literal.number 32]
                  ]
                |))
              |) in
            let _ :=
              M.declare (|
                ["offset"],
                M.call (|
                  "add",
                  [
                    M.get (| "offset" |);
                    [Literal.number 32]
                  ]
                |)
              |) in
            let _ :=
              M.declare (|
                ["addr"],
                M.call (|
                  "add",
                  [
                    M.get (| "baseRef" |);
                    M.get (| "offset" |)
                  ]
                |)
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "cleanup_t_rational_by",
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
          "convert_rational_0_by_1_to_uint256",
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
                          "cleanup_t_rational_by",
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
          "write_to_memory_uint256",
          ["memPtr"; "value"],
          [],
          ltac:(M.monadic (
            let _ :=
              M.call (|
                "mstore",
                [
                  M.get (| "memPtr" |);
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
          "cleanup_t_rational_by_1",
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
          "convert_t_rational_by_to_t_uint256",
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
                          "cleanup_t_rational_by_1",
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
          "convert_rational_1_by_1_to_uint256",
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
          "fun_secondItem",
          [],
          ["var_"],
          ltac:(M.monadic (
            let _ :=
              M.assign (|
                ["zero_t_uint256"],
                Some (M.call (|
                  "zero_value_for_split_uint256",
                  []
                |))
              |) in
            let _ :=
              M.declare (|
                ["var_"],
                M.get (| "zero_t_uint256" |)
              |) in
            let _ :=
              M.assign (|
                ["expr"],
                Some ([Literal.number 0x02])
              |) in
            let _ :=
              M.assign (|
                ["_1"],
                Some (M.call (|
                  "convert_rational_2_by_1_to_uint256",
                  [
                    M.get (| "expr" |)
                  ]
                |))
              |) in
            let _ :=
              M.assign (|
                ["expr_34_mpos"],
                Some (M.call (|
                  "allocate_and_zero_memory_array_array_uint256_dyn",
                  [
                    M.get (| "_1" |)
                  ]
                |))
              |) in
            let _ :=
              M.assign (|
                ["var_input_mpos"],
                Some (M.get (| "expr_34_mpos" |))
              |) in
            let _ :=
              M.assign (|
                ["expr_1"],
                Some ([Literal.number 0x11])
              |) in
            let _ :=
              M.assign (|
                ["_2"],
                Some (M.call (|
                  "convert_rational_by_to_uint256",
                  [
                    M.get (| "expr_1" |)
                  ]
                |))
              |) in
            let _ :=
              M.assign (|
                ["_4_mpos"],
                Some (M.get (| "var_input_mpos" |))
              |) in
            let _ :=
              M.assign (|
                ["expr_mpos"],
                Some (M.get (| "_4_mpos" |))
              |) in
            let _ :=
              M.assign (|
                ["expr_2"],
                Some ([Literal.number 0x00])
              |) in
            let _ :=
              M.assign (|
                ["_3"],
                Some (M.get (| "_2" |))
              |) in
            let _ :=
              M.call (|
                "write_to_memory_uint256",
                [
                  M.call (|
                    "memory_array_index_access_uint256_dyn",
                    [
                      M.get (| "expr_mpos" |);
                      M.call (|
                        "convert_rational_0_by_1_to_uint256",
                        [
                          M.get (| "expr_2" |)
                        ]
                      |)
                    ]
                  |);
                  M.get (| "_3" |)
                ]
              |) in
            let _ :=
              M.assign (|
                ["expr_3"],
                Some ([Literal.number 0x22])
              |) in
            let _ :=
              M.assign (|
                ["_4"],
                Some (M.call (|
                  "convert_t_rational_by_to_t_uint256",
                  [
                    M.get (| "expr_3" |)
                  ]
                |))
              |) in
            let _ :=
              M.assign (|
                ["_mpos"],
                Some (M.get (| "var_input_mpos" |))
              |) in
            let _ :=
              M.assign (|
                ["expr_42_mpos"],
                Some (M.get (| "_mpos" |))
              |) in
            let _ :=
              M.assign (|
                ["expr_4"],
                Some ([Literal.number 0x01])
              |) in
            let _ :=
              M.assign (|
                ["_5"],
                Some (M.get (| "_4" |))
              |) in
            let _ :=
              M.call (|
                "write_to_memory_uint256",
                [
                  M.call (|
                    "memory_array_index_access_uint256_dyn",
                    [
                      M.get (| "expr_42_mpos" |);
                      M.call (|
                        "convert_rational_1_by_1_to_uint256",
                        [
                          M.get (| "expr_4" |)
                        ]
                      |)
                    ]
                  |);
                  M.get (| "_5" |)
                ]
              |) in
            let _ :=
              M.assign (|
                ["_9_mpos"],
                Some (M.get (| "var_input_mpos" |))
              |) in
            let _ :=
              M.assign (|
                ["expr_48_mpos"],
                Some (M.get (| "_9_mpos" |))
              |) in
            let _ :=
              M.assign (|
                ["expr_self_mpos"],
                Some (M.get (| "expr_48_mpos" |))
              |) in
            let _ :=
              M.assign (|
                ["expr_5"],
                Some ([Literal.number 0x01])
              |) in
            let _ :=
              M.assign (|
                ["_6"],
                Some (M.call (|
                  "convert_rational_1_by_1_to_uint256",
                  [
                    M.get (| "expr_5" |)
                  ]
                |))
              |) in
            let _ :=
              M.assign (|
                ["expr_6"],
                Some (M.call (|
                  "fun_at",
                  [
                    M.get (| "expr_self_mpos" |);
                    M.get (| "_6" |)
                  ]
                |))
              |) in
            let _ :=
              M.declare (|
                ["var_"],
                M.get (| "expr_6" |)
              |) in
            let _ :=
              M.leave (||) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "read_from_memoryt_uint256",
          ["ptr"],
          ["returnValue"],
          ltac:(M.monadic (
            let _ :=
              M.assign (|
                ["value"],
                Some (M.call (|
                  "cleanup_uint256",
                  [
                    M.call (|
                      "mload",
                      [
                        M.get (| "ptr" |)
                      ]
                    |)
                  ]
                |))
              |) in
            let _ :=
              M.declare (|
                ["returnValue"],
                M.get (| "value" |)
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "fun_at",
          ["var_a_mpos"; "var_i"],
          ["var"],
          ltac:(M.monadic (
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
                ["var"],
                M.get (| "zero_uint256" |)
              |) in
            let _ :=
              M.assign (|
                ["_12_mpos"],
                Some (M.get (| "var_a_mpos" |))
              |) in
            let _ :=
              M.assign (|
                ["expr_10_mpos"],
                Some (M.get (| "_12_mpos" |))
              |) in
            let _ :=
              M.assign (|
                ["_1"],
                Some (M.get (| "var_i" |))
              |) in
            let _ :=
              M.assign (|
                ["expr"],
                Some (M.get (| "_1" |))
              |) in
            let _ :=
              M.assign (|
                ["_2"],
                Some (M.call (|
                  "read_from_memoryt_uint256",
                  [
                    M.call (|
                      "memory_array_index_access_uint256_dyn",
                      [
                        M.get (| "expr_10_mpos" |);
                        M.get (| "expr" |)
                      ]
                    |)
                  ]
                |))
              |) in
            let _ :=
              M.assign (|
                ["expr_1"],
                Some (M.get (| "_2" |))
              |) in
            let _ :=
              M.declare (|
                ["var"],
                M.get (| "expr_1" |)
              |) in
            let _ :=
              M.leave (||) in
            tt
          ))
        |) in
      tt
    )).

    Definition data : string :=
      "a26469706673582212207f06d07db145250e298b89c5f2c8b370a2d298fdf6adaec70344b38d40e09a9f64736f6c634300081b0033".
  End C_55_deployed.
End C_55.
