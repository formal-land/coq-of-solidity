(* Generated by solc *)
Require Import CoqOfSolidity.CoqOfSolidity.

Module A_11.
  Definition code : M.t BlockUnit.t :=
    do* M.open_scope in
    do* ltac:(M.monadic (
      M.function (|
        "allocate_unbounded",
        [],
        ["memPtr"],
        do* M.open_scope in
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
        M.close_scope
      |)
    )) in
    do* ltac:(M.monadic (
      M.function (|
        "revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb",
        [],
        [],
        do* M.open_scope in
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
        M.close_scope
      |)
    )) in
    do* ltac:(M.monadic (
      do* M.open_scope in
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
          do* M.open_scope in
          do* ltac:(M.monadic (
            M.expr_stmt (|
              M.call (|
                "revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb",
                []
              |)
            |)
          )) in
          M.close_scope
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
                  [Literal.string "415f31315f6465706c6f79656400000000000000000000000000000000000000"]
                ]
              |);
              M.call (|
                "datasize",
                [
                  [Literal.string "415f31315f6465706c6f79656400000000000000000000000000000000000000"]
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
                  [Literal.string "415f31315f6465706c6f79656400000000000000000000000000000000000000"]
                ]
              |)
            ]
          |)
        |)
      )) in
      M.close_scope
    )) in
    M.close_scope.

  Module A_11_deployed.
    Definition code : M.t BlockUnit.t :=
      do* M.open_scope in
      do* ltac:(M.monadic (
        M.function (|
          "allocate_unbounded",
          [],
          ["memPtr"],
          do* M.open_scope in
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
          M.close_scope
        |)
      )) in
      do* ltac:(M.monadic (
        M.function (|
          "revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb",
          [],
          [],
          do* M.open_scope in
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
          M.close_scope
        |)
      )) in
      do* ltac:(M.monadic (
        M.function (|
          "zero_value_for_split_bytes",
          [],
          ["ret"],
          do* M.open_scope in
          do* ltac:(M.monadic (
            M.assign (|
              ["ret"],
              Some ([Literal.number 96])
            |)
          )) in
          M.close_scope
        |)
      )) in
      do* ltac:(M.monadic (
        M.function (|
          "revert_error_987264b3b1d58a9c7f8255e93e81c77d86d6299019c33110a076957a3e06e2ae",
          [],
          [],
          do* M.open_scope in
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
          M.close_scope
        |)
      )) in
      do* ltac:(M.monadic (
        M.function (|
          "round_up_to_mul_of",
          ["value"],
          ["result"],
          do* M.open_scope in
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
          M.close_scope
        |)
      )) in
      do* ltac:(M.monadic (
        M.function (|
          "panic_error_0x41",
          [],
          [],
          do* M.open_scope in
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
          M.close_scope
        |)
      )) in
      do* ltac:(M.monadic (
        M.function (|
          "finalize_allocation",
          ["memPtr"; "size"],
          [],
          do* M.open_scope in
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
              do* M.open_scope in
              do* ltac:(M.monadic (
                M.expr_stmt (|
                  M.call (|
                    "panic_error_0x41",
                    []
                  |)
                |)
              )) in
              M.close_scope
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
          M.close_scope
        |)
      )) in
      do* ltac:(M.monadic (
        M.function (|
          "allocate_memory",
          ["size"],
          ["memPtr"],
          do* M.open_scope in
          do* ltac:(M.monadic (
            M.assign (|
              ["memPtr"],
              Some (M.call (|
                "allocate_unbounded",
                []
              |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.expr_stmt (|
              M.call (|
                "finalize_allocation",
                [
                  M.get_var (| "memPtr" |);
                  M.get_var (| "size" |)
                ]
              |)
            |)
          )) in
          M.close_scope
        |)
      )) in
      do* ltac:(M.monadic (
        M.function (|
          "array_allocation_size_bytes",
          ["length"],
          ["size"],
          do* M.open_scope in
          do* ltac:(M.monadic (
            M.if_ (|
              M.call (|
                "gt",
                [
                  M.get_var (| "length" |);
                  [Literal.number 0xffffffffffffffff]
                ]
              |),
              do* M.open_scope in
              do* ltac:(M.monadic (
                M.expr_stmt (|
                  M.call (|
                    "panic_error_0x41",
                    []
                  |)
                |)
              )) in
              M.close_scope
            |)
          )) in
          do* ltac:(M.monadic (
            M.assign (|
              ["size"],
              Some (M.call (|
                "round_up_to_mul_of",
                [
                  M.get_var (| "length" |)
                ]
              |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.assign (|
              ["size"],
              Some (M.call (|
                "add",
                [
                  M.get_var (| "size" |);
                  [Literal.number 0x20]
                ]
              |))
            |)
          )) in
          M.close_scope
        |)
      )) in
      do* ltac:(M.monadic (
        M.function (|
          "copy_calldata_to_memory_with_cleanup",
          ["src"; "dst"; "length"],
          [],
          do* M.open_scope in
          do* ltac:(M.monadic (
            M.expr_stmt (|
              M.call (|
                "calldatacopy",
                [
                  M.get_var (| "dst" |);
                  M.get_var (| "src" |);
                  M.get_var (| "length" |)
                ]
              |)
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
                      M.get_var (| "dst" |);
                      M.get_var (| "length" |)
                    ]
                  |);
                  [Literal.number 0]
                ]
              |)
            |)
          )) in
          M.close_scope
        |)
      )) in
      do* ltac:(M.monadic (
        M.function (|
          "abi_decode_available_length_bytes",
          ["src"; "length"; "end"],
          ["array"],
          do* M.open_scope in
          do* ltac:(M.monadic (
            M.assign (|
              ["array"],
              Some (M.call (|
                "allocate_memory",
                [
                  M.call (|
                    "array_allocation_size_bytes",
                    [
                      M.get_var (| "length" |)
                    ]
                  |)
                ]
              |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.expr_stmt (|
              M.call (|
                "mstore",
                [
                  M.get_var (| "array" |);
                  M.get_var (| "length" |)
                ]
              |)
            |)
          )) in
          do* ltac:(M.monadic (
            M.declare (|
              ["dst"],
              Some (M.call (|
                "add",
                [
                  M.get_var (| "array" |);
                  [Literal.number 0x20]
                ]
              |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.if_ (|
              M.call (|
                "gt",
                [
                  M.call (|
                    "add",
                    [
                      M.get_var (| "src" |);
                      M.get_var (| "length" |)
                    ]
                  |);
                  M.get_var (| "end" |)
                ]
              |),
              do* M.open_scope in
              do* ltac:(M.monadic (
                M.expr_stmt (|
                  M.call (|
                    "revert_error_987264b3b1d58a9c7f8255e93e81c77d86d6299019c33110a076957a3e06e2ae",
                    []
                  |)
                |)
              )) in
              M.close_scope
            |)
          )) in
          do* ltac:(M.monadic (
            M.expr_stmt (|
              M.call (|
                "copy_calldata_to_memory_with_cleanup",
                [
                  M.get_var (| "src" |);
                  M.get_var (| "dst" |);
                  M.get_var (| "length" |)
                ]
              |)
            |)
          )) in
          M.close_scope
        |)
      )) in
      do* ltac:(M.monadic (
        M.function (|
          "convert_array_bytes_calldata_to_bytes",
          ["value"; "length"],
          ["converted"],
          do* M.open_scope in
          do* ltac:(M.monadic (
            M.assign (|
              ["converted"],
              Some (M.call (|
                "abi_decode_available_length_bytes",
                [
                  M.get_var (| "value" |);
                  M.get_var (| "length" |);
                  M.call (|
                    "calldatasize",
                    []
                  |)
                ]
              |))
            |)
          )) in
          M.close_scope
        |)
      )) in
      do* ltac:(M.monadic (
        M.function (|
          "fun",
          ["var_input_offset"; "var_input_length"],
          ["var_mpos"],
          do* M.open_scope in
          do* ltac:(M.monadic (
            M.declare (|
              ["zero_bytes_mpos"],
              Some (M.call (|
                "zero_value_for_split_bytes",
                []
              |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.assign (|
              ["var_mpos"],
              Some (M.get_var (| "zero_bytes_mpos" |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.declare (|
              ["_offset"],
              Some (M.get_var (| "var_input_offset" |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.declare (|
              ["_length"],
              Some (M.get_var (| "var_input_length" |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.declare (|
              ["expr_offset"],
              Some (M.get_var (| "_offset" |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.declare (|
              ["expr_length"],
              Some (M.get_var (| "_length" |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.assign (|
              ["var_mpos"],
              Some (M.call (|
                "convert_array_bytes_calldata_to_bytes",
                [
                  M.get_var (| "expr_offset" |);
                  M.get_var (| "expr_length" |)
                ]
              |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.leave (||)
          )) in
          M.close_scope
        |)
      )) in
      do* ltac:(M.monadic (
        do* M.open_scope in
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
            do* M.open_scope in
            do* ltac:(M.monadic (
              M.expr_stmt (|
                M.call (|
                  "revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb",
                  []
                |)
              |)
            )) in
            M.close_scope
          |)
        )) in
        do* ltac:(M.monadic (
          M.declare (|
            ["retval"],
            Some (M.call (|
              "fun",
              [
                [Literal.number 0];
                M.call (|
                  "calldatasize",
                  []
                |)
              ]
            |))
          |)
        )) in
        do* ltac:(M.monadic (
          M.expr_stmt (|
            M.call (|
              "return",
              [
                M.call (|
                  "add",
                  [
                    M.get_var (| "retval" |);
                    [Literal.number 0x20]
                  ]
                |);
                M.call (|
                  "mload",
                  [
                    M.get_var (| "retval" |)
                  ]
                |)
              ]
            |)
          |)
        )) in
        M.close_scope
      )) in
      M.close_scope.

    Definition data : string :=
      "a2646970667358221220a62e37baaee39401d0fdd2b3d997bb9dd61893fab996a51fd91b119aac457ddc64736f6c634300081b0033".
  End A_11_deployed.
End A_11.
