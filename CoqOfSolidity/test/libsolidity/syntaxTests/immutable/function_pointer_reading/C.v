(* Generated by solc *)
Require Import CoqOfSolidity.CoqOfSolidity.

Module C_33.
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
                [Literal.number 0xa0]
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
        M.call (|
          "constructor_C",
          []
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
                [Literal.string "435f33335f6465706c6f796564"]
              ]
            |);
            M.call (|
              "datasize",
              [
                [Literal.string "435f33335f6465706c6f796564"]
              ]
            |)
          ]
        |) in
      let _ :=
        M.call (|
          "setimmutable",
          [
            M.get (| "_1" |);
            [Literal.string "32"];
            M.call (|
              "mload",
              [
                [Literal.number 128]
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
                [Literal.string "435f33335f6465706c6f796564"]
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
    let _ :=
      M.function (|
        "convert_function_internal_view_returns_uint256_to_function_internal_nonpayable_returns_uint",
        ["functionId"],
        ["outFunctionId"],
        ltac:(M.monadic (
          let _ :=
            M.declare (|
              ["outFunctionId"],
              M.get (| "functionId" |)
            |) in
          tt
        ))
      |) in
    let _ :=
      M.function (|
        "constructor_C",
        [],
        [],
        ltac:(M.monadic (
          let _ :=
            M.assign (|
              ["expr_functionIdentifier"],
              Some ([Literal.number 1])
            |) in
          let _ :=
            M.assign (|
              ["_2_functionIdentifier"],
              Some (M.call (|
                "convert_function_internal_view_returns_uint256_to_function_internal_nonpayable_returns_uint",
                [
                  M.get (| "expr_functionIdentifier" |)
                ]
              |))
            |) in
          let _ :=
            M.call (|
              "constructor_B",
              [
                M.get (| "_2_functionIdentifier" |)
              ]
            |) in
          tt
        ))
      |) in
    let _ :=
      M.function (|
        "constructor_B",
        ["var_fp_functionIdentifier"],
        [],
        ltac:(M.monadic (
          let _ :=
            M.assign (|
              ["_functionIdentifier"],
              Some (M.get (| "var_fp_functionIdentifier" |))
            |) in
          let _ :=
            M.assign (|
              ["expr_12_functionIdentifier"],
              Some (M.get (| "_functionIdentifier" |))
            |) in
          let _ :=
            M.assign (|
              ["expr"],
              Some (M.call (|
                "dispatch_internal_in_out",
                [
                  M.get (| "expr_12_functionIdentifier" |)
                ]
              |))
            |) in
          let _ :=
            M.assign (|
              ["_1"],
              Some (M.get (| "expr" |))
            |) in
          let _ :=
            M.call (|
              "mstore",
              [
                [Literal.number 128];
                M.get (| "_1" |)
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
        "panic_error_0x11",
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
                [Literal.number 0x11]
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
        "checked_add_uint256",
        ["x"; "y"],
        ["sum"],
        ltac:(M.monadic (
          let _ :=
            M.declare (|
              ["x"],
              M.call (|
                "cleanup_uint256",
                [
                  M.get (| "x" |)
                ]
              |)
            |) in
          let _ :=
            M.declare (|
              ["y"],
              M.call (|
                "cleanup_uint256",
                [
                  M.get (| "y" |)
                ]
              |)
            |) in
          let _ :=
            M.declare (|
              ["sum"],
              M.call (|
                "add",
                [
                  M.get (| "x" |);
                  M.get (| "y" |)
                ]
              |)
            |) in
          let _ :=
            M.if_ (|
              M.call (|
                "gt",
                [
                  M.get (| "x" |);
                  M.get (| "sum" |)
                ]
              |),
              ltac:(M.monadic (
                let _ :=
                  M.call (|
                    "panic_error_0x11",
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
        "fun_f",
        [],
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
              ["_1"],
              Some (M.call (|
                "read_from_memoryt_uint256",
                [
                  [Literal.number 128]
                ]
              |))
            |) in
          let _ :=
            M.assign (|
              ["expr"],
              Some (M.get (| "_1" |))
            |) in
          let _ :=
            M.assign (|
              ["expr_1"],
              Some ([Literal.number 0x02])
            |) in
          let _ :=
            M.assign (|
              ["expr_2"],
              Some (M.call (|
                "checked_add_uint256",
                [
                  M.get (| "expr" |);
                  M.call (|
                    "convert_rational_by_to_uint256",
                    [
                      M.get (| "expr_1" |)
                    ]
                  |)
                ]
              |))
            |) in
          let _ :=
            M.declare (|
              ["var"],
              M.get (| "expr_2" |)
            |) in
          let _ :=
            M.leave (||) in
          tt
        ))
      |) in
    let _ :=
      M.function (|
        "panic_error_0x51",
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
                [Literal.number 0x51]
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
        "dispatch_internal_in_out",
        ["fun"],
        ["out"],
        ltac:(M.monadic (
          let _ :=
            M.switch (|
              M.get (| "fun" |),
              [
                (
                  Some (Literal.number 1),
                  ltac:(M.monadic (
                    let _ :=
                      M.declare (|
                        ["out"],
                        M.call (|
                          "fun_f",
                          []
                        |)
                      |) in
                    tt
                  ))            );
                (
                  None,
                  ltac:(M.monadic (
                    let _ :=
                      M.call (|
                        "panic_error_0x51",
                        []
                      |) in
                    tt
                  ))            )          ]
            |) in
          tt
        ))
      |) in
    tt
  )).

  Module C_33_deployed.
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
          M.call (|
            "revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74",
            []
          |) in
        tt in
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
      tt
    )).

    Definition data : string :=
      "a26469706673582212205407bde51b34f481abe1ae5aee0cc2d54f3174cc79323751c9677803449802f264736f6c634300081b0033".
  End C_33_deployed.
End C_33.
