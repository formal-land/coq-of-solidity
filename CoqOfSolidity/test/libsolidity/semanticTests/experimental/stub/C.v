(* Generated by solc *)
Require Import CoqOfSolidity.CoqOfSolidity.

Module C_174.
  Definition code : M.t unit := ltac:(M.monadic (
    let _ :=
      let _ :=
        M.call (|
          "codecopy",
          [
            [Literal.number 0];
            M.call (|
              "dataoffset",
              [
                [Literal.string "435f3137345f6465706c6f796564"]
              ]
            |);
            M.call (|
              "datasize",
              [
                [Literal.string "435f3137345f6465706c6f796564"]
              ]
            |)
          ]
        |) in
      let _ :=
        M.call (|
          "return",
          [
            [Literal.number 0];
            M.call (|
              "datasize",
              [
                [Literal.string "435f3137345f6465706c6f796564"]
              ]
            |)
          ]
        |) in
      tt in
    tt
  )).

  Module C_174_deployed.
    Definition code : M.t unit := ltac:(M.monadic (
      let _ :=
        let _ :=
          M.call (|
            "fun_fun$unit$unit$$",
            []
          |) in
        let _ :=
          M.call (|
            "revert",
            [
              [Literal.number 0];
              [Literal.number 0]
            ]
          |) in
        tt in
      let _ :=
        M.function (|
          "fun_fun$unit$unit$$",
          [],
          [],
          ltac:(M.monadic (
            let _ :=
              M.assign (|
                ["var_arg"],
                None
              |) in
            let _ :=
              M.declare (|
                ["var_arg"],
                M.call (|
                  "calldataload",
                  [
                    [Literal.number 0]
                  ]
                |)
              |) in
            let _ :=
              M.assign (|
                ["var_x"],
                None
              |) in
            let _ :=
              M.assign (|
                ["expr"],
                Some (M.get (| "var_arg" |))
              |) in
            let _ :=
              M.assign (|
                ["expr_1"],
                Some (M.call (|
                  "iszero",
                  [
                    M.call (|
                      "iszero",
                      [
                        M.get (| "expr" |)
                      ]
                    |)
                  ]
                |))
              |) in
            let _ :=
              M.if_ (|
                M.get (| "expr_1" |),
                ltac:(M.monadic (
                  let _ :=
                    M.declare (|
                      ["var_x"],
                      [Literal.number 0x10]
                    |) in
                  tt
                ))
              |) in
            let _ :=
              M.assign (|
                ["expr_2"],
                Some (M.get (| "var_x" |))
              |) in
            let _ :=
              M.assign (|
                ["expr_3"],
                Some (M.get (| "expr_2" |))
              |) in
            let _ :=
              M.assign (|
                ["var_w"],
                Some (M.get (| "expr_3" |))
              |) in
            let _ :=
              M.assign (|
                ["expr_4"],
                Some (M.get (| "var_w" |))
              |) in
            let _ :=
              M.assign (|
                ["expr_5"],
                Some (M.get (| "var_w" |))
              |) in
            let _ :=
              M.assign (|
                ["expr_6"],
                Some (M.call (|
                  "fun_mul$fun$pair$t_uint256$t_uint256$$t_uint256$$",
                  [
                    M.get (| "expr_4" |);
                    M.get (| "expr_5" |)
                  ]
                |))
              |) in
            let _ :=
              M.assign (|
                ["expr_7"],
                Some (M.get (| "var_w" |))
              |) in
            let _ :=
              M.assign (|
                ["expr_8"],
                Some (M.call (|
                  "fun_add$fun$pair$t_uint256$t_uint256$$t_uint256$$",
                  [
                    M.get (| "expr_6" |);
                    M.get (| "expr_7" |)
                  ]
                |))
              |) in
            let _ :=
              M.declare (|
                ["var_w"],
                M.get (| "expr_8" |)
              |) in
            let _ :=
              M.assign (|
                ["var_y"],
                None
              |) in
            let _ :=
              M.declare (|
                ["var_y"],
                [Literal.number 2]
              |) in
            let _ :=
              M.assign (|
                ["expr_9"],
                Some (M.get (| "var_w" |))
              |) in
            let _ :=
              M.assign (|
                ["expr_10"],
                Some (M.get (| "expr_9" |))
              |) in
            let _ :=
              M.assign (|
                ["expr_11"],
                Some (M.get (| "var_y" |))
              |) in
            let _ :=
              M.assign (|
                ["expr_12"],
                Some (M.call (|
                  "fun_mul$fun$pair$word$word$$word$$",
                  [
                    M.get (| "expr_10" |);
                    M.get (| "expr_11" |)
                  ]
                |))
              |) in
            let _ :=
              M.declare (|
                ["var_y"],
                M.get (| "expr_12" |)
              |) in
            let _ :=
              M.call (|
                "mstore",
                [
                  [Literal.number 0];
                  M.get (| "var_y" |)
                ]
              |) in
            let _ :=
              M.call (|
                "return",
                [
                  [Literal.number 0];
                  [Literal.number 32]
                ]
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "fun_mul$fun$pair$t_uint256$t_uint256$$t_uint256$$",
          ["var_x"; "var_y"],
          ["expr"],
          ltac:(M.monadic (
            let _ :=
              M.assign (|
                ["expr_1"],
                Some (M.get (| "var_x" |))
              |) in
            let _ :=
              M.assign (|
                ["expr_2"],
                Some (M.get (| "expr_1" |))
              |) in
            let _ :=
              M.assign (|
                ["var_a"],
                Some (M.get (| "expr_2" |))
              |) in
            let _ :=
              M.assign (|
                ["expr_3"],
                Some (M.get (| "var_y" |))
              |) in
            let _ :=
              M.assign (|
                ["expr_4"],
                Some (M.get (| "expr_3" |))
              |) in
            let _ :=
              M.assign (|
                ["var_b"],
                Some (M.get (| "expr_4" |))
              |) in
            let _ :=
              M.declare (|
                ["var_a"],
                M.call (|
                  "mul",
                  [
                    M.get (| "var_a" |);
                    M.get (| "var_b" |)
                  ]
                |)
              |) in
            let _ :=
              M.assign (|
                ["expr_5"],
                Some (M.get (| "var_a" |))
              |) in
            let _ :=
              M.assign (|
                ["expr_6"],
                Some (M.get (| "expr_5" |))
              |) in
            let _ :=
              M.declare (|
                ["expr"],
                M.get (| "expr_6" |)
              |) in
            let _ :=
              M.leave (||) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "fun_add$fun$pair$t_uint256$t_uint256$$t_uint256$$",
          ["var_x"; "var_y"],
          ["expr"],
          ltac:(M.monadic (
            let _ :=
              M.assign (|
                ["expr_1"],
                Some (M.get (| "var_x" |))
              |) in
            let _ :=
              M.assign (|
                ["expr_2"],
                Some (M.get (| "expr_1" |))
              |) in
            let _ :=
              M.assign (|
                ["var_a"],
                Some (M.get (| "expr_2" |))
              |) in
            let _ :=
              M.assign (|
                ["expr_3"],
                Some (M.get (| "var_y" |))
              |) in
            let _ :=
              M.assign (|
                ["expr_4"],
                Some (M.get (| "expr_3" |))
              |) in
            let _ :=
              M.assign (|
                ["var_b"],
                Some (M.get (| "expr_4" |))
              |) in
            let _ :=
              M.declare (|
                ["var_a"],
                M.call (|
                  "add",
                  [
                    M.get (| "var_a" |);
                    M.get (| "var_b" |)
                  ]
                |)
              |) in
            let _ :=
              M.assign (|
                ["expr_5"],
                Some (M.get (| "var_a" |))
              |) in
            let _ :=
              M.assign (|
                ["expr_6"],
                Some (M.get (| "expr_5" |))
              |) in
            let _ :=
              M.declare (|
                ["expr"],
                M.get (| "expr_6" |)
              |) in
            let _ :=
              M.leave (||) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "fun_mul$fun$pair$word$word$$word$$",
          ["var_x"; "var_y"],
          ["expr"],
          ltac:(M.monadic (
            let _ :=
              M.assign (|
                ["var_z"],
                None
              |) in
            let _ :=
              M.declare (|
                ["var_z"],
                M.call (|
                  "mul",
                  [
                    M.get (| "var_x" |);
                    M.get (| "var_y" |)
                  ]
                |)
              |) in
            let _ :=
              M.assign (|
                ["expr_1"],
                Some (M.get (| "var_z" |))
              |) in
            let _ :=
              M.declare (|
                ["expr"],
                M.get (| "expr_1" |)
              |) in
            let _ :=
              M.leave (||) in
            tt
          ))
        |) in
      tt
    )).
  End C_174_deployed.
End C_174.
