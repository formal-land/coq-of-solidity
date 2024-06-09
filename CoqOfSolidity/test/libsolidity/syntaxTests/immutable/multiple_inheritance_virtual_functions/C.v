(* Generated by solc *)
Require Import CoqOfSolidity.CoqOfSolidity.

Module C_65.
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
                [Literal.string "435f36355f6465706c6f796564"]
              ]
            |);
            M.call (|
              "datasize",
              [
                [Literal.string "435f36355f6465706c6f796564"]
              ]
            |)
          ]
        |) in
      let _ :=
        M.call (|
          "setimmutable",
          [
            M.get (| "_1" |);
            [Literal.string "3131"];
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
                [Literal.string "435f36355f6465706c6f796564"]
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
        "constructor_C",
        [],
        [],
        ltac:(M.monadic (
          let _ :=
            M.call (|
              "constructor_B",
              []
            |) in
          tt
        ))
      |) in
    let _ :=
      M.function (|
        "constructor_B",
        [],
        [],
        ltac:(M.monadic (
          let _ :=
            M.assign (|
              ["expr"],
              Some (M.call (|
                "fun_xInit",
                []
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
        "fun_xInit",
        [],
        ["var_"],
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
              ["var_"],
              M.get (| "zero_uint256" |)
            |) in
          let _ :=
            M.assign (|
              ["expr"],
              Some (M.call (|
                "fun_xInit_29",
                []
              |))
            |) in
          let _ :=
            M.declare (|
              ["var_"],
              M.get (| "expr" |)
            |) in
          let _ :=
            M.leave (||) in
          tt
        ))
      |) in
    let _ :=
      M.function (|
        "fun_xInit_29",
        [],
        ["var"],
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
              ["var"],
              M.get (| "zero_t_uint256" |)
            |) in
          let _ :=
            M.assign (|
              ["expr"],
              Some (M.call (|
                "fun_f",
                []
              |))
            |) in
          let _ :=
            M.declare (|
              ["var"],
              M.get (| "expr" |)
            |) in
          let _ :=
            M.leave (||) in
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
            M.declare (|
              ["var"],
              M.get (| "expr" |)
            |) in
          let _ :=
            M.leave (||) in
          tt
        ))
      |) in
    tt
  )).

  Module C_65_deployed.
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
      "a2646970667358221220e872fe16c4e1ab9a681312bf3c83f4088d4e89280437bd8c6d0e9b1163ae35df64736f6c634300081b0033".
  End C_65_deployed.
End C_65.
