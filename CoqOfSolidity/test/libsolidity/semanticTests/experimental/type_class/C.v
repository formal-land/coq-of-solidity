(* Generated by solc *)
Require Import CoqOfSolidity.CoqOfSolidity.

Module C_120.
  Definition code : M.t BlockUnit.t :=
    do* M.open_scope in
    do* ltac:(M.monadic (
      do* M.open_scope in
      do* ltac:(M.monadic (
        M.expr_stmt (|
          M.call (|
            "codecopy",
            [
              [Literal.number 0];
              M.call (|
                "dataoffset",
                [
                  [Literal.string "435f3132305f6465706c6f796564000000000000000000000000000000000000"]
                ]
              |);
              M.call (|
                "datasize",
                [
                  [Literal.string "435f3132305f6465706c6f796564000000000000000000000000000000000000"]
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
              [Literal.number 0];
              M.call (|
                "datasize",
                [
                  [Literal.string "435f3132305f6465706c6f796564000000000000000000000000000000000000"]
                ]
              |)
            ]
          |)
        |)
      )) in
      M.close_scope
    )) in
    M.close_scope.

  Module C_120_deployed.
    Definition code : M.t BlockUnit.t :=
      do* M.open_scope in
      do* ltac:(M.monadic (
        M.function (|
          "fun_fun$unit$unit$$",
          [],
          [],
          do* M.open_scope in
          do* ltac:(M.monadic (
            M.declare (|
              ["var_boolResult1"],
              None
            |)
          )) in
          do* ltac:(M.monadic (
            M.declare (|
              ["var_boolResult2"],
              None
            |)
          )) in
          do* ltac:(M.monadic (
            M.declare (|
              ["expr"],
              Some (M.call (|
                "fun_new$fun$unit$t_Cat$$",
                []
              |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.declare (|
              ["var_c"],
              Some (M.get_var (| "expr" |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.declare (|
              ["expr_1"],
              Some (M.get_var (| "var_c" |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.declare (|
              ["expr_2"],
              Some (M.call (|
                "fun_alive$fun$t_Cat$bool$$",
                [
                  M.get_var (| "expr_1" |)
                ]
              |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.assign (|
              ["var_boolResult1"],
              Some (M.get_var (| "expr_2" |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.declare (|
              ["expr_3"],
              Some (M.call (|
                "fun_new$fun$unit$t_Dog$$",
                []
              |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.declare (|
              ["var_d"],
              Some (M.get_var (| "expr_3" |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.declare (|
              ["expr_4"],
              Some (M.get_var (| "var_d" |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.declare (|
              ["expr_5"],
              Some (M.call (|
                "fun_alive$fun$t_Dog$bool$$",
                [
                  M.get_var (| "expr_4" |)
                ]
              |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.assign (|
              ["var_boolResult2"],
              Some (M.get_var (| "expr_5" |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.declare (|
              ["expr_6"],
              Some (M.get_var (| "var_boolResult1" |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.declare (|
              ["expr_7"],
              Some (M.get_var (| "expr_6" |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.declare (|
              ["var_wordResult1"],
              Some (M.get_var (| "expr_7" |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.declare (|
              ["expr_8"],
              Some (M.get_var (| "var_boolResult2" |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.declare (|
              ["expr_9"],
              Some (M.get_var (| "expr_8" |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.declare (|
              ["var_wordResult2"],
              Some (M.get_var (| "expr_9" |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.expr_stmt (|
              M.call (|
                "mstore",
                [
                  [Literal.number 0];
                  M.get_var (| "var_wordResult1" |)
                ]
              |)
            |)
          )) in
          do* ltac:(M.monadic (
            M.expr_stmt (|
              M.call (|
                "mstore",
                [
                  [Literal.number 32];
                  M.get_var (| "var_wordResult2" |)
                ]
              |)
            |)
          )) in
          do* ltac:(M.monadic (
            M.expr_stmt (|
              M.call (|
                "return",
                [
                  [Literal.number 0];
                  [Literal.number 64]
                ]
              |)
            |)
          )) in
          M.close_scope
        |)
      )) in
      do* ltac:(M.monadic (
        M.function (|
          "fun_new$fun$unit$t_Cat$$",
          [],
          ["expr"],
          do* M.open_scope in
          do* ltac:(M.monadic (
            M.declare (|
              ["var_c"],
              None
            |)
          )) in
          do* ltac:(M.monadic (
            M.declare (|
              ["expr_1"],
              Some (M.get_var (| "var_c" |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.assign (|
              ["expr"],
              Some (M.get_var (| "expr_1" |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.leave (||)
          )) in
          M.close_scope
        |)
      )) in
      do* ltac:(M.monadic (
        M.function (|
          "fun_alive$fun$t_Cat$bool$$",
          ["var_self"],
          ["expr"],
          do* M.open_scope in
          do* ltac:(M.monadic (
            M.declare (|
              ["var_w"],
              None
            |)
          )) in
          do* ltac:(M.monadic (
            M.assign (|
              ["var_w"],
              Some ([Literal.number 1])
            |)
          )) in
          do* ltac:(M.monadic (
            M.declare (|
              ["expr_1"],
              Some (M.get_var (| "var_w" |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.declare (|
              ["expr_2"],
              Some (M.call (|
                "iszero",
                [
                  M.call (|
                    "iszero",
                    [
                      M.get_var (| "expr_1" |)
                    ]
                  |)
                ]
              |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.assign (|
              ["expr"],
              Some (M.get_var (| "expr_2" |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.leave (||)
          )) in
          M.close_scope
        |)
      )) in
      do* ltac:(M.monadic (
        M.function (|
          "fun_new$fun$unit$t_Dog$$",
          [],
          ["expr"],
          do* M.open_scope in
          do* ltac:(M.monadic (
            M.declare (|
              ["var_d"],
              None
            |)
          )) in
          do* ltac:(M.monadic (
            M.declare (|
              ["expr_1"],
              Some (M.get_var (| "var_d" |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.assign (|
              ["expr"],
              Some (M.get_var (| "expr_1" |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.leave (||)
          )) in
          M.close_scope
        |)
      )) in
      do* ltac:(M.monadic (
        M.function (|
          "fun_alive$fun$t_Dog$bool$$",
          ["var_self"],
          ["expr"],
          do* M.open_scope in
          do* ltac:(M.monadic (
            M.declare (|
              ["var_b"],
              None
            |)
          )) in
          do* ltac:(M.monadic (
            M.declare (|
              ["expr_1"],
              Some (M.get_var (| "var_b" |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.assign (|
              ["expr"],
              Some (M.get_var (| "expr_1" |))
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
              "fun_fun$unit$unit$$",
              []
            |)
          |)
        )) in
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
      )) in
      M.close_scope.
  End C_120_deployed.
End C_120.
