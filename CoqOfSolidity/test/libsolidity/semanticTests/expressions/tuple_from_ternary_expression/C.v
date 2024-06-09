(* Generated by solc *)
Require Import CoqOfSolidity.CoqOfSolidity.

Module C_27.
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
                [Literal.string "435f32375f6465706c6f796564"]
              ]
            |);
            M.call (|
              "datasize",
              [
                [Literal.string "435f32375f6465706c6f796564"]
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
                [Literal.string "435f32375f6465706c6f796564"]
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

  Module C_27_deployed.
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
          "abi_encode_bool_to_bool",
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
          "abi_encode_bool",
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
                "abi_encode_bool_to_bool",
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
              M.assign (|
                ["ret"],
                Some (M.call (|
                  "fun_f",
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
                  "abi_encode_bool",
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
          "zero_value_for_split_bool",
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
          "cleanup_uint8",
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
                    [Literal.number 0xff]
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
          "convert_rational_by_to_uint8",
          ["value"],
          ["converted"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["converted"],
                M.call (|
                  "cleanup_uint8",
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
          "convert_rational_2_by_1_to_uint8",
          ["value"],
          ["converted"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["converted"],
                M.call (|
                  "cleanup_uint8",
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
          "convert_t_rational_by_to_t_uint8",
          ["value"],
          ["converted"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["converted"],
                M.call (|
                  "cleanup_uint8",
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
          "convert_rational_by_rational_by_rational_by_to_uint8_uint8_uint8_",
          ["value0"; "value1"; "value2"],
          ["converted0";
      "converted1";
      "converted2"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["converted0"],
                M.call (|
                  "convert_rational_by_to_uint8",
                  [
                    M.get (| "value0" |)
                  ]
                |)
              |) in
            let _ :=
              M.declare (|
                ["converted1"],
                M.call (|
                  "convert_rational_2_by_1_to_uint8",
                  [
                    M.get (| "value1" |)
                  ]
                |)
              |) in
            let _ :=
              M.declare (|
                ["converted2"],
                M.call (|
                  "convert_t_rational_by_to_t_uint8",
                  [
                    M.get (| "value2" |)
                  ]
                |)
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "convert_rational_by_rational_by_rational_by_to_uint8_uint8_uint",
          ["value0"; "value1"; "value2"],
          ["converted0";
      "converted1";
      "converted2"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["converted0"],
                M.call (|
                  "convert_t_rational_by_to_t_uint8",
                  [
                    M.get (| "value0" |)
                  ]
                |)
              |) in
            let _ :=
              M.declare (|
                ["converted1"],
                M.call (|
                  "convert_rational_2_by_1_to_uint8",
                  [
                    M.get (| "value1" |)
                  ]
                |)
              |) in
            let _ :=
              M.declare (|
                ["converted2"],
                M.call (|
                  "convert_rational_by_to_uint8",
                  [
                    M.get (| "value2" |)
                  ]
                |)
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "fun_f",
          [],
          ["var"],
          ltac:(M.monadic (
            let _ :=
              M.assign (|
                ["zero_bool"],
                Some (M.call (|
                  "zero_value_for_split_bool",
                  []
                |))
              |) in
            let _ :=
              M.declare (|
                ["var"],
                M.get (| "zero_bool" |)
              |) in
            let _ :=
              M.assign (|
                ["var_flag"],
                None
              |) in
            let _ :=
              M.assign (|
                ["zero_t_bool"],
                Some (M.call (|
                  "zero_value_for_split_bool",
                  []
                |))
              |) in
            let _ :=
              M.declare (|
                ["var_flag"],
                M.get (| "zero_t_bool" |)
              |) in
            let _ :=
              M.assign (|
                ["expr"],
                Some ([Literal.number 0x01])
              |) in
            let _ :=
              M.declare (|
                ["var_flag"],
                M.get (| "expr" |)
              |) in
            let _ :=
              M.assign (|
                ["expr_1"],
                Some (M.get (| "expr" |))
              |) in
            let _ :=
              M.assign (|
                ["expr_2"],
                Some (M.get (| "expr_1" |))
              |) in
            let _ :=
              M.assign (|
                ["expr_component"; "expr_20_component"; "expr_20_component_1"],
                None
              |) in
            let _ :=
              M.switch (|
                M.get (| "expr_2" |),
                [
                  (
                    Some (Literal.number 0),
                    ltac:(M.monadic (
                      let _ :=
                        M.assign (|
                          ["expr_3"],
                          Some ([Literal.number 0x03])
                        |) in
                      let _ :=
                        M.assign (|
                          ["expr_19_component"],
                          Some (M.get (| "expr_3" |))
                        |) in
                      let _ :=
                        M.assign (|
                          ["expr_4"],
                          Some ([Literal.number 0x02])
                        |) in
                      let _ :=
                        M.assign (|
                          ["expr_component_1"],
                          Some (M.get (| "expr_4" |))
                        |) in
                      let _ :=
                        M.assign (|
                          ["expr_5"],
                          Some ([Literal.number 0x01])
                        |) in
                      let _ :=
                        M.assign (|
                          ["expr_19_component_1"],
                          Some (M.get (| "expr_5" |))
                        |) in
                      let _ :=
                        M.declare (|
                          ["expr_component"; "expr_20_component"; "expr_20_component_1"],
                          M.call (|
                            "convert_rational_by_rational_by_rational_by_to_uint8_uint8_uint8_",
                            [
                              M.get (| "expr_19_component" |);
                              M.get (| "expr_component_1" |);
                              M.get (| "expr_19_component_1" |)
                            ]
                          |)
                        |) in
                      tt
                    ))            );
                  (
                    None,
                    ltac:(M.monadic (
                      let _ :=
                        M.assign (|
                          ["expr_6"],
                          Some ([Literal.number 0x01])
                        |) in
                      let _ :=
                        M.assign (|
                          ["expr_component_2"],
                          Some (M.get (| "expr_6" |))
                        |) in
                      let _ :=
                        M.assign (|
                          ["expr_7"],
                          Some ([Literal.number 0x02])
                        |) in
                      let _ :=
                        M.assign (|
                          ["expr_15_component"],
                          Some (M.get (| "expr_7" |))
                        |) in
                      let _ :=
                        M.assign (|
                          ["expr_8"],
                          Some ([Literal.number 0x03])
                        |) in
                      let _ :=
                        M.assign (|
                          ["expr_component_3"],
                          Some (M.get (| "expr_8" |))
                        |) in
                      let _ :=
                        M.declare (|
                          ["expr_component"; "expr_20_component"; "expr_20_component_1"],
                          M.call (|
                            "convert_rational_by_rational_by_rational_by_to_uint8_uint8_uint",
                            [
                              M.get (| "expr_component_2" |);
                              M.get (| "expr_15_component" |);
                              M.get (| "expr_component_3" |)
                            ]
                          |)
                        |) in
                      tt
                    ))            )          ]
              |) in
            let _ :=
              M.assign (|
                ["_1"],
                Some (M.get (| "var_flag" |))
              |) in
            let _ :=
              M.assign (|
                ["expr_9"],
                Some (M.get (| "_1" |))
              |) in
            let _ :=
              M.declare (|
                ["var"],
                M.get (| "expr_9" |)
              |) in
            let _ :=
              M.leave (||) in
            tt
          ))
        |) in
      tt
    )).

    Definition data : string :=
      "a264697066735822122002b0bf70c30d31333886b3d53ba5309af7f46923315e1d21d63805ff377b1cf964736f6c634300081b0033".
  End C_27_deployed.
End C_27.
