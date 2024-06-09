(* Generated by solc *)
Require Import CoqOfSolidity.CoqOfSolidity.

Module C_70.
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
                [Literal.string "435f37305f6465706c6f796564"]
              ]
            |);
            M.call (|
              "datasize",
              [
                [Literal.string "435f37305f6465706c6f796564"]
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
                [Literal.string "435f37305f6465706c6f796564"]
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

  Module C_70_deployed.
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
                      Some (Literal.number 0xb3de648b),
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
                "fun_f",
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
          "array_allocation_size_array_array_struct_S_dyn_dyn",
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
          "allocate_memory_array_array_array_struct_S_dyn_dyn",
          ["length"],
          ["memPtr"],
          ltac:(M.monadic (
            let _ :=
              M.assign (|
                ["allocSize"],
                Some (M.call (|
                  "array_allocation_size_array_array_struct_S_dyn_dyn",
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
          "zero_value_for_array_struct_S_dyn",
          [],
          ["ret"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["ret"],
                [Literal.number 96]
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "zero_complex_memory_array_array_array_struct_S_dyn_dyn",
          ["dataStart"; "dataSizeInBytes"],
          [],
          ltac:(M.monadic (
            let _ :=
              M.assign (|
                ["i"],
                Some ([Literal.number 0])
              |) in
            let _ :=
              let _ :=
                tt in
              M.for_ (|
                M.call (|
                  "lt",
                  [
                    M.get (| "i" |);
                    M.get (| "dataSizeInBytes" |)
                  ]
                |),
                ltac:(M.monadic (
                  let _ :=
                    M.declare (|
                      ["i"],
                      M.call (|
                        "add",
                        [
                          M.get (| "i" |);
                          [Literal.number 32]
                        ]
                      |)
                    |) in
                  tt
                )),
                ltac:(M.monadic (
                  let _ :=
                    M.call (|
                      "mstore",
                      [
                        M.call (|
                          "add",
                          [
                            M.get (| "dataStart" |);
                            M.get (| "i" |)
                          ]
                        |);
                        M.call (|
                          "zero_value_for_array_struct_S_dyn",
                          []
                        |)
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
          "allocate_and_zero_memory_array_array_array_struct_S_dyn_dyn",
          ["length"],
          ["memPtr"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["memPtr"],
                M.call (|
                  "allocate_memory_array_array_array_struct_S_dyn_dyn",
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
                  "array_allocation_size_array_array_struct_S_dyn_dyn",
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
                "zero_complex_memory_array_array_array_struct_S_dyn_dyn",
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
          "array_allocation_size_bytes",
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
                  "round_up_to_mul_of",
                  [
                    M.get (| "length" |)
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
          "allocate_memory_array_bytes",
          ["length"],
          ["memPtr"],
          ltac:(M.monadic (
            let _ :=
              M.assign (|
                ["allocSize"],
                Some (M.call (|
                  "array_allocation_size_bytes",
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
          "zero_memory_chunk_bytes1",
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
          "allocate_and_zero_memory_array_bytes",
          ["length"],
          ["memPtr"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["memPtr"],
                M.call (|
                  "allocate_memory_array_bytes",
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
                  "array_allocation_size_bytes",
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
                "zero_memory_chunk_bytes1",
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
          "fun_f",
          ["var_size"],
          [],
          ltac:(M.monadic (
            let _ :=
              M.assign (|
                ["expr"],
                Some ([Literal.number 0x0a])
              |) in
            let _ :=
              M.assign (|
                ["_1"],
                Some (M.call (|
                  "convert_rational_by_to_uint256",
                  [
                    M.get (| "expr" |)
                  ]
                |))
              |) in
            let _ :=
              M.call (|
                "pop",
                [
                  M.call (|
                    "allocate_and_zero_memory_array_array_array_struct_S_dyn_dyn",
                    [
                      M.get (| "_1" |)
                    ]
                  |)
                ]
              |) in
            let _ :=
              M.assign (|
                ["expr_1"],
                Some ([Literal.number 0x14])
              |) in
            let _ :=
              M.assign (|
                ["_2"],
                Some (M.call (|
                  "convert_t_rational_by_to_t_uint256",
                  [
                    M.get (| "expr_1" |)
                  ]
                |))
              |) in
            let _ :=
              M.call (|
                "pop",
                [
                  M.call (|
                    "allocate_and_zero_memory_array_array_uint256_dyn",
                    [
                      M.get (| "_2" |)
                    ]
                  |)
                ]
              |) in
            let _ :=
              M.assign (|
                ["_3"],
                Some (M.get (| "var_size" |))
              |) in
            let _ :=
              M.assign (|
                ["expr_2"],
                Some (M.get (| "_3" |))
              |) in
            let _ :=
              M.call (|
                "pop",
                [
                  M.call (|
                    "allocate_and_zero_memory_array_bytes",
                    [
                      M.get (| "expr_2" |)
                    ]
                  |)
                ]
              |) in
            tt
          ))
        |) in
      tt
    )).

    Definition data : string :=
      "a2646970667358221220bec78c25dbae84ce7057d0ae821711762fc2d0c55df3a9997f93c7ebcf6b2f8064736f6c634300081b0033".
  End C_70_deployed.
End C_70.
