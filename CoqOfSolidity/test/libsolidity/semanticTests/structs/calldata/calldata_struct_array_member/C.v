(* Generated by solc *)
Require Import CoqOfSolidity.CoqOfSolidity.

Module C_50.
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
                [Literal.string "435f35305f6465706c6f796564"]
              ]
            |);
            M.call (|
              "datasize",
              [
                [Literal.string "435f35305f6465706c6f796564"]
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
                [Literal.string "435f35305f6465706c6f796564"]
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

  Module C_50_deployed.
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
                      Some (Literal.number 0x29e884ee),
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
          "revert_error_21fe6b43b4db61d76a176e95bf1a6b9ede4c301f93a4246f41fecb96e160861d",
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
          "abi_decode_struct_S_calldata",
          ["offset"; "end"],
          ["value"],
          ltac:(M.monadic (
            let _ :=
              M.if_ (|
                M.call (|
                  "slt",
                  [
                    M.call (|
                      "sub",
                      [
                        M.get (| "end" |);
                        M.get (| "offset" |)
                      ]
                    |);
                    [Literal.number 128]
                  ]
                |),
                ltac:(M.monadic (
                  let _ :=
                    M.call (|
                      "revert_error_21fe6b43b4db61d76a176e95bf1a6b9ede4c301f93a4246f41fecb96e160861d",
                      []
                    |) in
                  tt
                ))
              |) in
            let _ :=
              M.declare (|
                ["value"],
                M.get (| "offset" |)
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "abi_decode_struct_S_calldata_ptr",
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
                    [Literal.number 128]
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
                  "abi_decode_struct_S_calldata",
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
          "abi_encode_uint256",
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
          "abi_encode_uint256_uint256_uint256_uint256",
          ["headStart"; "value0"; "value1"; "value2"; "value3"],
          ["tail"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["tail"],
                M.call (|
                  "add",
                  [
                    M.get (| "headStart" |);
                    [Literal.number 128]
                  ]
                |)
              |) in
            let _ :=
              M.call (|
                "abi_encode_uint256",
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
                "abi_encode_uint256",
                [
                  M.get (| "value1" |);
                  M.call (|
                    "add",
                    [
                      M.get (| "headStart" |);
                      [Literal.number 32]
                    ]
                  |)
                ]
              |) in
            let _ :=
              M.call (|
                "abi_encode_uint256",
                [
                  M.get (| "value2" |);
                  M.call (|
                    "add",
                    [
                      M.get (| "headStart" |);
                      [Literal.number 64]
                    ]
                  |)
                ]
              |) in
            let _ :=
              M.call (|
                "abi_encode_uint256",
                [
                  M.get (| "value3" |);
                  M.call (|
                    "add",
                    [
                      M.get (| "headStart" |);
                      [Literal.number 96]
                    ]
                  |)
                ]
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
                  "abi_decode_struct_S_calldata_ptr",
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
              M.assign (|
                ["ret"; "ret_1"; "ret_2"; "ret_3"],
                Some (M.call (|
                  "fun_f",
                  [
                    M.get (| "param" |)
                  ]
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
                  "abi_encode_uint256_uint256_uint256_uint256",
                  [
                    M.get (| "memPos" |);
                    M.get (| "ret" |);
                    M.get (| "ret_1" |);
                    M.get (| "ret_2" |);
                    M.get (| "ret_3" |)
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
          "read_from_calldatat_uint256",
          ["ptr"],
          ["returnValue"],
          ltac:(M.monadic (
            let _ :=
              M.assign (|
                ["value"],
                Some (M.call (|
                  "calldataload",
                  [
                    M.get (| "ptr" |)
                  ]
                |))
              |) in
            let _ :=
              M.call (|
                "validator_revert_uint256",
                [
                  M.get (| "value" |)
                ]
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
          "calldata_array_index_access_uint256_calldata",
          ["base_ref"; "index"],
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
                        [Literal.number 0x02]
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
              M.declare (|
                ["addr"],
                M.call (|
                  "add",
                  [
                    M.get (| "base_ref" |);
                    M.call (|
                      "mul",
                      [
                        M.get (| "index" |);
                        [Literal.number 32]
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
          "fun_f",
          ["var_s_offset"],
          ["var_a";
      "var_b0";
      "var_b1";
      "var_c"],
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
                ["var_a"],
                M.get (| "zero_t_uint256" |)
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
                ["var_b0"],
                M.get (| "zero_uint256" |)
              |) in
            let _ :=
              M.assign (|
                ["zero_uint256_1"],
                Some (M.call (|
                  "zero_value_for_split_uint256",
                  []
                |))
              |) in
            let _ :=
              M.declare (|
                ["var_b1"],
                M.get (| "zero_uint256_1" |)
              |) in
            let _ :=
              M.assign (|
                ["zero_uint256_2"],
                Some (M.call (|
                  "zero_value_for_split_uint256",
                  []
                |))
              |) in
            let _ :=
              M.declare (|
                ["var_c"],
                M.get (| "zero_uint256_2" |)
              |) in
            let _ :=
              M.assign (|
                ["_5_offset"],
                Some (M.get (| "var_s_offset" |))
              |) in
            let _ :=
              M.assign (|
                ["expr_25_offset"],
                Some (M.get (| "_5_offset" |))
              |) in
            let _ :=
              M.assign (|
                ["_1"],
                Some (M.call (|
                  "add",
                  [
                    M.get (| "expr_25_offset" |);
                    [Literal.number 0]
                  ]
                |))
              |) in
            let _ :=
              M.assign (|
                ["expr"],
                Some (M.call (|
                  "read_from_calldatat_uint256",
                  [
                    M.get (| "_1" |)
                  ]
                |))
              |) in
            let _ :=
              M.declare (|
                ["var_a"],
                M.get (| "expr" |)
              |) in
            let _ :=
              M.assign (|
                ["_7_offset"],
                Some (M.get (| "var_s_offset" |))
              |) in
            let _ :=
              M.assign (|
                ["expr_offset"],
                Some (M.get (| "_7_offset" |))
              |) in
            let _ :=
              M.assign (|
                ["_2"],
                Some (M.call (|
                  "add",
                  [
                    M.get (| "expr_offset" |);
                    [Literal.number 32]
                  ]
                |))
              |) in
            let _ :=
              M.assign (|
                ["expr_31_offset"],
                Some (M.get (| "_2" |))
              |) in
            let _ :=
              M.assign (|
                ["expr_1"],
                Some ([Literal.number 0x00])
              |) in
            let _ :=
              M.assign (|
                ["expr_2"],
                Some (M.call (|
                  "read_from_calldatat_uint256",
                  [
                    M.call (|
                      "calldata_array_index_access_uint256_calldata",
                      [
                        M.get (| "expr_31_offset" |);
                        M.call (|
                          "convert_t_rational_by_to_t_uint256",
                          [
                            M.get (| "expr_1" |)
                          ]
                        |)
                      ]
                    |)
                  ]
                |))
              |) in
            let _ :=
              M.declare (|
                ["var_b0"],
                M.get (| "expr_2" |)
              |) in
            let _ :=
              M.assign (|
                ["_offset"],
                Some (M.get (| "var_s_offset" |))
              |) in
            let _ :=
              M.assign (|
                ["expr_37_offset"],
                Some (M.get (| "_offset" |))
              |) in
            let _ :=
              M.assign (|
                ["_3"],
                Some (M.call (|
                  "add",
                  [
                    M.get (| "expr_37_offset" |);
                    [Literal.number 32]
                  ]
                |))
              |) in
            let _ :=
              M.assign (|
                ["expr_38_offset"],
                Some (M.get (| "_3" |))
              |) in
            let _ :=
              M.assign (|
                ["expr_3"],
                Some ([Literal.number 0x01])
              |) in
            let _ :=
              M.assign (|
                ["expr_4"],
                Some (M.call (|
                  "read_from_calldatat_uint256",
                  [
                    M.call (|
                      "calldata_array_index_access_uint256_calldata",
                      [
                        M.get (| "expr_38_offset" |);
                        M.call (|
                          "convert_rational_by_to_uint256",
                          [
                            M.get (| "expr_3" |)
                          ]
                        |)
                      ]
                    |)
                  ]
                |))
              |) in
            let _ :=
              M.declare (|
                ["var_b1"],
                M.get (| "expr_4" |)
              |) in
            let _ :=
              M.assign (|
                ["_11_offset"],
                Some (M.get (| "var_s_offset" |))
              |) in
            let _ :=
              M.assign (|
                ["expr_44_offset"],
                Some (M.get (| "_11_offset" |))
              |) in
            let _ :=
              M.assign (|
                ["_4"],
                Some (M.call (|
                  "add",
                  [
                    M.get (| "expr_44_offset" |);
                    [Literal.number 96]
                  ]
                |))
              |) in
            let _ :=
              M.assign (|
                ["expr_5"],
                Some (M.call (|
                  "read_from_calldatat_uint256",
                  [
                    M.get (| "_4" |)
                  ]
                |))
              |) in
            let _ :=
              M.declare (|
                ["var_c"],
                M.get (| "expr_5" |)
              |) in
            tt
          ))
        |) in
      tt
    )).

    Definition data : string :=
      "a264697066735822122074176851619c4dfd157b4eb682277b97e70e259bb0fc8e7af9d6d92204f5251664736f6c634300081b0033".
  End C_50_deployed.
End C_50.
