(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

Module C.
  Definition code : Code.t := {|
    Code.name := "C_21";
    Code.hex_name := 0x435f323100000000000000000000000000000000000000000000000000000000;
    Code.code :=
      M.scope (
        do* ltac:(M.monadic (
          M.function (|
            "allocate_unbounded",
            [],
            ["memPtr"],
            M.scope (
              do* ltac:(M.monadic (
                M.assign (|
                  ["memPtr"],
                  Some (M.call (|
                    "mload",
                    [
                      [Literal.number 64]
                    ]
                  |))
                |)
              )) in
              M.pure BlockUnit.Tt
            )
          |)
        )) in
        do* ltac:(M.monadic (
          M.function (|
            "revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb",
            [],
            [],
            M.scope (
              do* ltac:(M.monadic (
                M.expr_stmt (|
                  M.call (|
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
        do* ltac:(M.monadic (
          M.scope (
            do* ltac:(M.monadic (
              M.expr_stmt (|
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
                |)
              |)
            )) in
            do* ltac:(M.monadic (
              M.if_ (|
                M.call (|
                  "callvalue",
                  []
                |),
                M.scope (
                  do* ltac:(M.monadic (
                    M.expr_stmt (|
                      M.call (|
                        "revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb",
                        []
                      |)
                    |)
                  )) in
                  M.pure BlockUnit.Tt
                )
              |)
            )) in
            do* ltac:(M.monadic (
              M.declare (|
                ["_1"],
                Some (M.call (|
                  "allocate_unbounded",
                  []
                |))
              |)
            )) in
            do* ltac:(M.monadic (
              M.expr_stmt (|
                M.call (|
                  "codecopy",
                  [
                    M.get_var (| "_1" |);
                    M.call (|
                      "dataoffset",
                      [
                        [Literal.string 0x435f32315f6465706c6f79656400000000000000000000000000000000000000]
                      ]
                    |);
                    M.call (|
                      "datasize",
                      [
                        [Literal.string 0x435f32315f6465706c6f79656400000000000000000000000000000000000000]
                      ]
                    |)
                  ]
                |)
              |)
            )) in
            do* ltac:(M.monadic (
              M.expr_stmt (|
                M.call (|
                  "return",
                  [
                    M.get_var (| "_1" |);
                    M.call (|
                      "datasize",
                      [
                        [Literal.string 0x435f32315f6465706c6f79656400000000000000000000000000000000000000]
                      ]
                    |)
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
      Code.name := "C_21_deployed";
      Code.hex_name := 0x435f32315f6465706c6f79656400000000000000000000000000000000000000;
      Code.code :=
        M.scope (
          do* ltac:(M.monadic (
            M.function (|
              "shift_right_unsigned",
              ["value"],
              ["newValue"],
              M.scope (
                do* ltac:(M.monadic (
                  M.assign (|
                    ["newValue"],
                    Some (M.call (|
                      "shr",
                      [
                        [Literal.number 224];
                        M.get_var (| "value" |)
                      ]
                    |))
                  |)
                )) in
                M.pure BlockUnit.Tt
              )
            |)
          )) in
          do* ltac:(M.monadic (
            M.function (|
              "allocate_unbounded",
              [],
              ["memPtr"],
              M.scope (
                do* ltac:(M.monadic (
                  M.assign (|
                    ["memPtr"],
                    Some (M.call (|
                      "mload",
                      [
                        [Literal.number 64]
                      ]
                    |))
                  |)
                )) in
                M.pure BlockUnit.Tt
              )
            |)
          )) in
          do* ltac:(M.monadic (
            M.function (|
              "revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb",
              [],
              [],
              M.scope (
                do* ltac:(M.monadic (
                  M.expr_stmt (|
                    M.call (|
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
          do* ltac:(M.monadic (
            M.function (|
              "revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b",
              [],
              [],
              M.scope (
                do* ltac:(M.monadic (
                  M.expr_stmt (|
                    M.call (|
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
          do* ltac:(M.monadic (
            M.function (|
              "abi_decode",
              ["headStart"; "dataEnd"],
              [],
              M.scope (
                do* ltac:(M.monadic (
                  M.if_ (|
                    M.call (|
                      "slt",
                      [
                        M.call (|
                          "sub",
                          [
                            M.get_var (| "dataEnd" |);
                            M.get_var (| "headStart" |)
                          ]
                        |);
                        [Literal.number 0]
                      ]
                    |),
                    M.scope (
                      do* ltac:(M.monadic (
                        M.expr_stmt (|
                          M.call (|
                            "revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b",
                            []
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
          do* ltac:(M.monadic (
            M.function (|
              "abi_encode_tuple",
              ["headStart"],
              ["tail"],
              M.scope (
                do* ltac:(M.monadic (
                  M.assign (|
                    ["tail"],
                    Some (M.call (|
                      "add",
                      [
                        M.get_var (| "headStart" |);
                        [Literal.number 0]
                      ]
                    |))
                  |)
                )) in
                M.pure BlockUnit.Tt
              )
            |)
          )) in
          do* ltac:(M.monadic (
            M.function (|
              "external_fun_f",
              [],
              [],
              M.scope (
                do* ltac:(M.monadic (
                  M.if_ (|
                    M.call (|
                      "callvalue",
                      []
                    |),
                    M.scope (
                      do* ltac:(M.monadic (
                        M.expr_stmt (|
                          M.call (|
                            "revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb",
                            []
                          |)
                        |)
                      )) in
                      M.pure BlockUnit.Tt
                    )
                  |)
                )) in
                do* ltac:(M.monadic (
                  M.expr_stmt (|
                    M.call (|
                      "abi_decode",
                      [
                        [Literal.number 4];
                        M.call (|
                          "calldatasize",
                          []
                        |)
                      ]
                    |)
                  |)
                )) in
                do* ltac:(M.monadic (
                  M.expr_stmt (|
                    M.call (|
                      "fun_f",
                      []
                    |)
                  |)
                )) in
                do* ltac:(M.monadic (
                  M.declare (|
                    ["memPos"],
                    Some (M.call (|
                      "allocate_unbounded",
                      []
                    |))
                  |)
                )) in
                do* ltac:(M.monadic (
                  M.declare (|
                    ["memEnd"],
                    Some (M.call (|
                      "abi_encode_tuple",
                      [
                        M.get_var (| "memPos" |)
                      ]
                    |))
                  |)
                )) in
                do* ltac:(M.monadic (
                  M.expr_stmt (|
                    M.call (|
                      "return",
                      [
                        M.get_var (| "memPos" |);
                        M.call (|
                          "sub",
                          [
                            M.get_var (| "memEnd" |);
                            M.get_var (| "memPos" |)
                          ]
                        |)
                      ]
                    |)
                  |)
                )) in
                M.pure BlockUnit.Tt
              )
            |)
          )) in
          do* ltac:(M.monadic (
            M.function (|
              "revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74",
              [],
              [],
              M.scope (
                do* ltac:(M.monadic (
                  M.expr_stmt (|
                    M.call (|
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
          do* ltac:(M.monadic (
            M.function (|
              "zero_value_for_split_array_struct_S_dyn",
              [],
              ["ret"],
              M.scope (
                do* ltac:(M.monadic (
                  M.assign (|
                    ["ret"],
                    Some ([Literal.number 96])
                  |)
                )) in
                M.pure BlockUnit.Tt
              )
            |)
          )) in
          do* ltac:(M.monadic (
            M.function (|
              "array_length_array_struct_S_dyn",
              ["value"],
              ["length"],
              M.scope (
                do* ltac:(M.monadic (
                  M.assign (|
                    ["length"],
                    Some (M.call (|
                      "mload",
                      [
                        M.get_var (| "value" |)
                      ]
                    |))
                  |)
                )) in
                M.pure BlockUnit.Tt
              )
            |)
          )) in
          do* ltac:(M.monadic (
            M.function (|
              "array_storeLengthForEncoding_array_struct_S_dyn",
              ["pos"; "length"],
              ["updated_pos"],
              M.scope (
                do* ltac:(M.monadic (
                  M.expr_stmt (|
                    M.call (|
                      "mstore",
                      [
                        M.get_var (| "pos" |);
                        M.get_var (| "length" |)
                      ]
                    |)
                  |)
                )) in
                do* ltac:(M.monadic (
                  M.assign (|
                    ["updated_pos"],
                    Some (M.call (|
                      "add",
                      [
                        M.get_var (| "pos" |);
                        [Literal.number 0x20]
                      ]
                    |))
                  |)
                )) in
                M.pure BlockUnit.Tt
              )
            |)
          )) in
          do* ltac:(M.monadic (
            M.function (|
              "array_dataslot_array_struct_S_dyn",
              ["ptr"],
              ["data"],
              M.scope (
                do* ltac:(M.monadic (
                  M.assign (|
                    ["data"],
                    Some (M.get_var (| "ptr" |))
                  |)
                )) in
                do* ltac:(M.monadic (
                  M.assign (|
                    ["data"],
                    Some (M.call (|
                      "add",
                      [
                        M.get_var (| "ptr" |);
                        [Literal.number 0x20]
                      ]
                    |))
                  |)
                )) in
                M.pure BlockUnit.Tt
              )
            |)
          )) in
          do* ltac:(M.monadic (
            M.function (|
              "cleanup_uint256",
              ["value"],
              ["cleaned"],
              M.scope (
                do* ltac:(M.monadic (
                  M.assign (|
                    ["cleaned"],
                    Some (M.get_var (| "value" |))
                  |)
                )) in
                M.pure BlockUnit.Tt
              )
            |)
          )) in
          do* ltac:(M.monadic (
            M.function (|
              "abi_encode_uint256",
              ["value"; "pos"],
              [],
              M.scope (
                do* ltac:(M.monadic (
                  M.expr_stmt (|
                    M.call (|
                      "mstore",
                      [
                        M.get_var (| "pos" |);
                        M.call (|
                          "cleanup_uint256",
                          [
                            M.get_var (| "value" |)
                          ]
                        |)
                      ]
                    |)
                  |)
                )) in
                M.pure BlockUnit.Tt
              )
            |)
          )) in
          do* ltac:(M.monadic (
            M.function (|
              "abi_encode_struct_S",
              ["value"; "pos"],
              [],
              M.scope (
                do* ltac:(M.monadic (
                  M.declare (|
                    ["memberValue0"],
                    Some (M.call (|
                      "mload",
                      [
                        M.call (|
                          "add",
                          [
                            M.get_var (| "value" |);
                            [Literal.number 0x00]
                          ]
                        |)
                      ]
                    |))
                  |)
                )) in
                do* ltac:(M.monadic (
                  M.expr_stmt (|
                    M.call (|
                      "abi_encode_uint256",
                      [
                        M.get_var (| "memberValue0" |);
                        M.call (|
                          "add",
                          [
                            M.get_var (| "pos" |);
                            [Literal.number 0x00]
                          ]
                        |)
                      ]
                    |)
                  |)
                )) in
                M.pure BlockUnit.Tt
              )
            |)
          )) in
          do* ltac:(M.monadic (
            M.function (|
              "abi_encodeUpdatedPos_struct_S",
              ["value0"; "pos"],
              ["updatedPos"],
              M.scope (
                do* ltac:(M.monadic (
                  M.expr_stmt (|
                    M.call (|
                      "abi_encode_struct_S",
                      [
                        M.get_var (| "value0" |);
                        M.get_var (| "pos" |)
                      ]
                    |)
                  |)
                )) in
                do* ltac:(M.monadic (
                  M.assign (|
                    ["updatedPos"],
                    Some (M.call (|
                      "add",
                      [
                        M.get_var (| "pos" |);
                        [Literal.number 0x20]
                      ]
                    |))
                  |)
                )) in
                M.pure BlockUnit.Tt
              )
            |)
          )) in
          do* ltac:(M.monadic (
            M.function (|
              "array_nextElement_array_struct_S_dyn",
              ["ptr"],
              ["next"],
              M.scope (
                do* ltac:(M.monadic (
                  M.assign (|
                    ["next"],
                    Some (M.call (|
                      "add",
                      [
                        M.get_var (| "ptr" |);
                        [Literal.number 0x20]
                      ]
                    |))
                  |)
                )) in
                M.pure BlockUnit.Tt
              )
            |)
          )) in
          do* ltac:(M.monadic (
            M.function (|
              "abi_encode_array_struct_S_memory_ptr_dyn_memory_ptr",
              ["value"; "pos"],
              ["end"],
              M.scope (
                do* ltac:(M.monadic (
                  M.declare (|
                    ["length"],
                    Some (M.call (|
                      "array_length_array_struct_S_dyn",
                      [
                        M.get_var (| "value" |)
                      ]
                    |))
                  |)
                )) in
                do* ltac:(M.monadic (
                  M.assign (|
                    ["pos"],
                    Some (M.call (|
                      "array_storeLengthForEncoding_array_struct_S_dyn",
                      [
                        M.get_var (| "pos" |);
                        M.get_var (| "length" |)
                      ]
                    |))
                  |)
                )) in
                do* ltac:(M.monadic (
                  M.declare (|
                    ["baseRef"],
                    Some (M.call (|
                      "array_dataslot_array_struct_S_dyn",
                      [
                        M.get_var (| "value" |)
                      ]
                    |))
                  |)
                )) in
                do* ltac:(M.monadic (
                  M.declare (|
                    ["srcPtr"],
                    Some (M.get_var (| "baseRef" |))
                  |)
                )) in
                do* ltac:(M.monadic (
                  M.declare (|
                    ["i"],
                    Some ([Literal.number 0])
                  |)
                )) in
                do* ltac:(M.monadic (
                  do*
                    M.scope (
                      M.pure BlockUnit.Tt
                    ) in
                  ltac:(M.monadic (
                    M.for_ (|
                      ltac:(M.monadic (
                        M.call (|
                          "lt",
                          [
                            M.get_var (| "i" |);
                            M.get_var (| "length" |)
                          ]
                        |)
                      )),
                      M.scope (
                        do* ltac:(M.monadic (
                          M.assign (|
                            ["i"],
                            Some (M.call (|
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
                        do* ltac:(M.monadic (
                          M.declare (|
                            ["elementValue0"],
                            Some (M.call (|
                              "mload",
                              [
                                M.get_var (| "srcPtr" |)
                              ]
                            |))
                          |)
                        )) in
                        do* ltac:(M.monadic (
                          M.assign (|
                            ["pos"],
                            Some (M.call (|
                              "abi_encodeUpdatedPos_struct_S",
                              [
                                M.get_var (| "elementValue0" |);
                                M.get_var (| "pos" |)
                              ]
                            |))
                          |)
                        )) in
                        do* ltac:(M.monadic (
                          M.assign (|
                            ["srcPtr"],
                            Some (M.call (|
                              "array_nextElement_array_struct_S_dyn",
                              [
                                M.get_var (| "srcPtr" |)
                              ]
                            |))
                          |)
                        )) in
                        M.pure BlockUnit.Tt
                      )
                    |)
                  ))
                )) in
                do* ltac:(M.monadic (
                  M.assign (|
                    ["end"],
                    Some (M.get_var (| "pos" |))
                  |)
                )) in
                M.pure BlockUnit.Tt
              )
            |)
          )) in
          do* ltac:(M.monadic (
            M.function (|
              "abi_encode_array_struct_S_dyn",
              ["headStart"; "value0"],
              ["tail"],
              M.scope (
                do* ltac:(M.monadic (
                  M.assign (|
                    ["tail"],
                    Some (M.call (|
                      "add",
                      [
                        M.get_var (| "headStart" |);
                        [Literal.number 32]
                      ]
                    |))
                  |)
                )) in
                do* ltac:(M.monadic (
                  M.expr_stmt (|
                    M.call (|
                      "mstore",
                      [
                        M.call (|
                          "add",
                          [
                            M.get_var (| "headStart" |);
                            [Literal.number 0]
                          ]
                        |);
                        M.call (|
                          "sub",
                          [
                            M.get_var (| "tail" |);
                            M.get_var (| "headStart" |)
                          ]
                        |)
                      ]
                    |)
                  |)
                )) in
                do* ltac:(M.monadic (
                  M.assign (|
                    ["tail"],
                    Some (M.call (|
                      "abi_encode_array_struct_S_memory_ptr_dyn_memory_ptr",
                      [
                        M.get_var (| "value0" |);
                        M.get_var (| "tail" |)
                      ]
                    |))
                  |)
                )) in
                M.pure BlockUnit.Tt
              )
            |)
          )) in
          do* ltac:(M.monadic (
            M.function (|
              "round_up_to_mul_of",
              ["value"],
              ["result"],
              M.scope (
                do* ltac:(M.monadic (
                  M.assign (|
                    ["result"],
                    Some (M.call (|
                      "and",
                      [
                        M.call (|
                          "add",
                          [
                            M.get_var (| "value" |);
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
                    |))
                  |)
                )) in
                M.pure BlockUnit.Tt
              )
            |)
          )) in
          do* ltac:(M.monadic (
            M.function (|
              "panic_error_0x41",
              [],
              [],
              M.scope (
                do* ltac:(M.monadic (
                  M.expr_stmt (|
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
                    |)
                  |)
                )) in
                do* ltac:(M.monadic (
                  M.expr_stmt (|
                    M.call (|
                      "mstore",
                      [
                        [Literal.number 4];
                        [Literal.number 0x41]
                      ]
                    |)
                  |)
                )) in
                do* ltac:(M.monadic (
                  M.expr_stmt (|
                    M.call (|
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
          do* ltac:(M.monadic (
            M.function (|
              "finalize_allocation",
              ["memPtr"; "size"],
              [],
              M.scope (
                do* ltac:(M.monadic (
                  M.declare (|
                    ["newFreePtr"],
                    Some (M.call (|
                      "add",
                      [
                        M.get_var (| "memPtr" |);
                        M.call (|
                          "round_up_to_mul_of",
                          [
                            M.get_var (| "size" |)
                          ]
                        |)
                      ]
                    |))
                  |)
                )) in
                do* ltac:(M.monadic (
                  M.if_ (|
                    M.call (|
                      "or",
                      [
                        M.call (|
                          "gt",
                          [
                            M.get_var (| "newFreePtr" |);
                            [Literal.number 0xffffffffffffffff]
                          ]
                        |);
                        M.call (|
                          "lt",
                          [
                            M.get_var (| "newFreePtr" |);
                            M.get_var (| "memPtr" |)
                          ]
                        |)
                      ]
                    |),
                    M.scope (
                      do* ltac:(M.monadic (
                        M.expr_stmt (|
                          M.call (|
                            "panic_error_0x41",
                            []
                          |)
                        |)
                      )) in
                      M.pure BlockUnit.Tt
                    )
                  |)
                )) in
                do* ltac:(M.monadic (
                  M.expr_stmt (|
                    M.call (|
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
            |)
          )) in
          do* ltac:(M.monadic (
            M.function (|
              "fun_f",
              [],
              [],
              M.scope (
                do* ltac:(M.monadic (
                  M.declare (|
                    ["var_s_mpos"],
                    None
                  |)
                )) in
                do* ltac:(M.monadic (
                  M.declare (|
                    ["zero_array_struct_S_dyn_mpos"],
                    Some (M.call (|
                      "zero_value_for_split_array_struct_S_dyn",
                      []
                    |))
                  |)
                )) in
                do* ltac:(M.monadic (
                  M.assign (|
                    ["var_s_mpos"],
                    Some (M.get_var (| "zero_array_struct_S_dyn_mpos" |))
                  |)
                )) in
                do* ltac:(M.monadic (
                  M.declare (|
                    ["_mpos"],
                    Some (M.get_var (| "var_s_mpos" |))
                  |)
                )) in
                do* ltac:(M.monadic (
                  M.declare (|
                    ["expr_mpos"],
                    Some (M.get_var (| "_mpos" |))
                  |)
                )) in
                do* ltac:(M.monadic (
                  M.declare (|
                    ["expr_17_mpos"],
                    Some (M.call (|
                      "allocate_unbounded",
                      []
                    |))
                  |)
                )) in
                do* ltac:(M.monadic (
                  M.declare (|
                    ["_1"],
                    Some (M.call (|
                      "add",
                      [
                        M.get_var (| "expr_17_mpos" |);
                        [Literal.number 0x20]
                      ]
                    |))
                  |)
                )) in
                do* ltac:(M.monadic (
                  M.declare (|
                    ["_2"],
                    Some (M.call (|
                      "abi_encode_array_struct_S_dyn",
                      [
                        M.get_var (| "_1" |);
                        M.get_var (| "expr_mpos" |)
                      ]
                    |))
                  |)
                )) in
                do* ltac:(M.monadic (
                  M.expr_stmt (|
                    M.call (|
                      "mstore",
                      [
                        M.get_var (| "expr_17_mpos" |);
                        M.call (|
                          "sub",
                          [
                            M.get_var (| "_2" |);
                            M.call (|
                              "add",
                              [
                                M.get_var (| "expr_17_mpos" |);
                                [Literal.number 0x20]
                              ]
                            |)
                          ]
                        |)
                      ]
                    |)
                  |)
                )) in
                do* ltac:(M.monadic (
                  M.expr_stmt (|
                    M.call (|
                      "finalize_allocation",
                      [
                        M.get_var (| "expr_17_mpos" |);
                        M.call (|
                          "sub",
                          [
                            M.get_var (| "_2" |);
                            M.get_var (| "expr_17_mpos" |)
                          ]
                        |)
                      ]
                    |)
                  |)
                )) in
                M.pure BlockUnit.Tt
              )
            |)
          )) in
          do* ltac:(M.monadic (
            M.scope (
              do* ltac:(M.monadic (
                M.expr_stmt (|
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
                  |)
                |)
              )) in
              do* ltac:(M.monadic (
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
                  M.scope (
                    do* ltac:(M.monadic (
                      M.declare (|
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
                      |)
                    )) in
                    do* ltac:(M.monadic (
                      M.switch (|
                        M.get_var (| "selector" |),
                        [
                          (
                            Some (Literal.number 0x26121ff0),
                            M.scope (
                              do* ltac:(M.monadic (
                                M.expr_stmt (|
                                  M.call (|
                                    "external_fun_f",
                                    []
                                  |)
                                |)
                              )) in
                              M.pure BlockUnit.Tt
                            )
                          );
                          (
                            None,
                            M.scope (
                              M.pure BlockUnit.Tt
                            )
                          )
                        ]
                      |)
                    )) in
                    M.pure BlockUnit.Tt
                  )
                |)
              )) in
              do* ltac:(M.monadic (
                M.expr_stmt (|
                  M.call (|
                    "revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74",
                    []
                  |)
                |)
              )) in
              M.pure BlockUnit.Tt
            )
          )) in
          M.pure BlockUnit.Tt
        );
    |}.

    Definition data : string :=
      "a2646970667358221220813dfd0aa939bc915f2a171f8d8d6762df94fa1113c49046da774353f55fbfb464736f6c634300081b0033".
  End deployed.
End C.

Definition codes : list (U256.t * M.t BlockUnit.t) :=
  ltac2:(
    let codes := Code.get_codes () in
    exact $codes
  ).
