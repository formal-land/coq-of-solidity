(* Generated by shallow_embed.py *)
Require Import CoqOfSolidity.CoqOfSolidity.
Require Import CoqOfSolidity.simulations.CoqOfSolidity.
Import Stdlib.

Module Contract_91.
  Definition allocate_unbounded : M.t U256.t :=
    let~ '(_, memPtr) :=
      let memPtr := 0 in
      let~ memPtr := [[ mload ~(| 64 |) ]] in
      M.pure (BlockUnit.Tt, memPtr)
    in
    M.pure memPtr.

  Definition constructor_Contract_91 : M.t unit :=
    let~ '(_, tt) :=
      M.pure (BlockUnit.Tt, tt)
    in
    M.pure tt.

  Definition revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb : M.t unit :=
    let~ '(_, tt) :=
      do~ [[ revert ~(| 0, 0 |) ]] in
      M.pure (BlockUnit.Tt, tt)
    in
    M.pure tt.

  Definition body : M.t unit :=
    let~ '(_, result) :=
      do~ [[ mstore ~(| 64, memoryguard ~(| 128 |) |) ]] in
      let_state~ 'tt := [[
        Shallow.if_ (|
          callvalue ~(||),
          do~ [[ revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb ~(||) ]] in
          M.pure (BlockUnit.Tt, tt),
          tt
        |)
      ]] default~ tt in
      do~ [[ constructor_Contract_91 ~(||) ]] in
      let~ _1 := [[ allocate_unbounded ~(||) ]] in
      do~ [[ codecopy ~(| _1, dataoffset ~(| 0x436f6e74726163745f39315f6465706c6f796564000000000000000000000000 (* Contract_91_deployed *) |), datasize ~(| 0x436f6e74726163745f39315f6465706c6f796564000000000000000000000000 (* Contract_91_deployed *) |) |) ]] in
      do~ [[ return_ ~(| _1, datasize ~(| 0x436f6e74726163745f39315f6465706c6f796564000000000000000000000000 (* Contract_91_deployed *) |) |) ]] in
      M.pure (BlockUnit.Tt, tt)
    in
    M.pure result.

  Module Contract_91_deployed.
    Definition cleanup_t_uint256 (value : U256.t) : M.t U256.t :=
      let~ '(_, cleaned) :=
        let cleaned := 0 in
        let~ cleaned := [[ value ]] in
        M.pure (BlockUnit.Tt, cleaned)
      in
      M.pure cleaned.

    Definition validator_revert_t_uint256 (value : U256.t) : M.t unit :=
      let~ '(_, tt) :=
        let_state~ 'tt := [[
          Shallow.if_ (|
            iszero ~(| eq ~(| value, cleanup_t_uint256 ~(| value |) |) |),
            do~ [[ revert ~(| 0, 0 |) ]] in
            M.pure (BlockUnit.Tt, tt),
            tt
          |)
        ]] default~ tt in
        M.pure (BlockUnit.Tt, tt)
      in
      M.pure tt.

    Definition abi_decode_t_uint256 (offset : U256.t) (end_ : U256.t) : M.t U256.t :=
      let~ '(_, value) :=
        let value := 0 in
        let~ value := [[ calldataload ~(| offset |) ]] in
        do~ [[ validator_revert_t_uint256 ~(| value |) ]] in
        M.pure (BlockUnit.Tt, value)
      in
      M.pure value.

    Definition allocate_unbounded : M.t U256.t :=
      let~ '(_, memPtr) :=
        let memPtr := 0 in
        let~ memPtr := [[ mload ~(| 64 |) ]] in
        M.pure (BlockUnit.Tt, memPtr)
      in
      M.pure memPtr.

    Definition panic_error_0x41 : M.t unit :=
      let~ '(_, tt) :=
        do~ [[ mstore ~(| 0, 35408467139433450592217433187231851964531694900788300625387963629091585785856 |) ]] in
        do~ [[ mstore ~(| 4, 0x41 |) ]] in
        do~ [[ revert ~(| 0, 0x24 |) ]] in
        M.pure (BlockUnit.Tt, tt)
      in
      M.pure tt.

    Definition round_up_to_mul_of_32 (value : U256.t) : M.t U256.t :=
      let~ '(_, result) :=
        let result := 0 in
        let~ result := [[ and ~(| add ~(| value, 31 |), not ~(| 31 |) |) ]] in
        M.pure (BlockUnit.Tt, result)
      in
      M.pure result.

    Definition finalize_allocation (memPtr : U256.t) (size : U256.t) : M.t unit :=
      let~ '(_, tt) :=
        let~ newFreePtr := [[ add ~(| memPtr, round_up_to_mul_of_32 ~(| size |) |) ]] in
        let_state~ 'tt := [[
          Shallow.if_ (|
            or ~(| gt ~(| newFreePtr, 0xffffffffffffffff |), lt ~(| newFreePtr, memPtr |) |),
            do~ [[ panic_error_0x41 ~(||) ]] in
            M.pure (BlockUnit.Tt, tt),
            tt
          |)
        ]] default~ tt in
        do~ [[ mstore ~(| 64, newFreePtr |) ]] in
        M.pure (BlockUnit.Tt, tt)
      in
      M.pure tt.

    Definition allocate_memory (size : U256.t) : M.t U256.t :=
      let~ '(_, memPtr) :=
        let memPtr := 0 in
        let~ memPtr := [[ allocate_unbounded ~(||) ]] in
        do~ [[ finalize_allocation ~(| memPtr, size |) ]] in
        M.pure (BlockUnit.Tt, memPtr)
      in
      M.pure memPtr.

    Definition array_allocation_size_t_arrayδ_t_uint256_δ10_memory_ptr (length : U256.t) : M.t U256.t :=
      let~ '(_, size) :=
        let size := 0 in
        let_state~ 'tt := [[
          Shallow.if_ (|
            gt ~(| length, 0xffffffffffffffff |),
            do~ [[ panic_error_0x41 ~(||) ]] in
            M.pure (BlockUnit.Tt, tt),
            tt
          |)
        ]] default~ size in
        let~ size := [[ mul ~(| length, 0x20 |) ]] in
        M.pure (BlockUnit.Tt, size)
      in
      M.pure size.

    Definition revert_error_81385d8c0b31fffe14be1da910c8bd3a80be4cfa248e04f42ec0faea3132a8ef : M.t unit :=
      let~ '(_, tt) :=
        do~ [[ revert ~(| 0, 0 |) ]] in
        M.pure (BlockUnit.Tt, tt)
      in
      M.pure tt.

    Definition abi_decode_available_length_t_arrayδ_t_uint256_δ10_memory_ptr (offset : U256.t) (length : U256.t) (end_ : U256.t) : M.t U256.t :=
      let~ '(_, array) :=
        let array := 0 in
        let~ array := [[ allocate_memory ~(| array_allocation_size_t_arrayδ_t_uint256_δ10_memory_ptr ~(| length |) |) ]] in
        let~ dst := [[ array ]] in
        let~ srcEnd := [[ add ~(| offset, mul ~(| length, 0x20 |) |) ]] in
        let_state~ 'tt := [[
          Shallow.if_ (|
            gt ~(| srcEnd, end_ |),
            do~ [[ revert_error_81385d8c0b31fffe14be1da910c8bd3a80be4cfa248e04f42ec0faea3132a8ef ~(||) ]] in
            M.pure (BlockUnit.Tt, tt),
            tt
          |)
        ]] default~ array in
        let_state~ dst :=
          let~ src := [[ offset ]] in
          let_state~ '(dst, src) :=
            (* for loop *)
            Shallow.for_
              (* init state *)
              (dst, src)
              (* condition *)
              (fun '(dst, src) => [[
                lt ~(| src, srcEnd |)
              ]])
              (* body *)
              (fun '(dst, src) =>
                Shallow.lift_state_update
                  (fun dst => (dst, src))
                  (let~ elementPos := [[ src ]] in
                  do~ [[ mstore ~(| dst, abi_decode_t_uint256 ~(| elementPos, end_ |) |) ]] in
                  let~ dst := [[ add ~(| dst, 0x20 |) ]] in
                  M.pure (BlockUnit.Tt, dst)))
              (* post *)
              (fun '(dst, src) =>
                Shallow.lift_state_update
                  (fun src => (dst, src))
                  (let~ src := [[ add ~(| src, 0x20 |) ]] in
                  M.pure (BlockUnit.Tt, src)))
          default~ dst in
          M.pure (BlockUnit.Tt, dst)
        default~ array in
        M.pure (BlockUnit.Tt, array)
      in
      M.pure array.

    Definition revert_error_1b9f4a0a5773e33b91aa01db23bf8c55fce1411167c872835e7fa00a4f17d46d : M.t unit :=
      let~ '(_, tt) :=
        do~ [[ revert ~(| 0, 0 |) ]] in
        M.pure (BlockUnit.Tt, tt)
      in
      M.pure tt.

    Definition abi_decode_t_arrayδ_t_uint256_δ10_memory_ptr (offset : U256.t) (end_ : U256.t) : M.t U256.t :=
      let~ '(_, array) :=
        let array := 0 in
        let_state~ 'tt := [[
          Shallow.if_ (|
            iszero ~(| slt ~(| add ~(| offset, 0x1f |), end_ |) |),
            do~ [[ revert_error_1b9f4a0a5773e33b91aa01db23bf8c55fce1411167c872835e7fa00a4f17d46d ~(||) ]] in
            M.pure (BlockUnit.Tt, tt),
            tt
          |)
        ]] default~ array in
        let~ length := [[ 0x0a ]] in
        let~ array := [[ abi_decode_available_length_t_arrayδ_t_uint256_δ10_memory_ptr ~(| offset, length, end_ |) ]] in
        M.pure (BlockUnit.Tt, array)
      in
      M.pure array.

    Definition revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b : M.t unit :=
      let~ '(_, tt) :=
        do~ [[ revert ~(| 0, 0 |) ]] in
        M.pure (BlockUnit.Tt, tt)
      in
      M.pure tt.

    Definition abi_decode_tuple_t_arrayδ_t_uint256_δ10_memory_ptrt_uint256t_uint256 (headStart : U256.t) (dataEnd : U256.t) : M.t (U256.t * U256.t * U256.t) :=
      let~ '(_, (value0, value1, value2)) :=
        let '(value0, value1, value2) := (0, 0, 0) in
        let_state~ 'tt := [[
          Shallow.if_ (|
            slt ~(| sub ~(| dataEnd, headStart |), 384 |),
            do~ [[ revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b ~(||) ]] in
            M.pure (BlockUnit.Tt, tt),
            tt
          |)
        ]] default~ (value0, value1, value2) in
        let_state~ value0 :=
          let~ offset := [[ 0 ]] in
          let~ value0 := [[ abi_decode_t_arrayδ_t_uint256_δ10_memory_ptr ~(| add ~(| headStart, offset |), dataEnd |) ]] in
          M.pure (BlockUnit.Tt, value0)
        default~ (value0, value1, value2) in
        let_state~ value1 :=
          let~ offset := [[ 320 ]] in
          let~ value1 := [[ abi_decode_t_uint256 ~(| add ~(| headStart, offset |), dataEnd |) ]] in
          M.pure (BlockUnit.Tt, value1)
        default~ (value0, value1, value2) in
        let_state~ value2 :=
          let~ offset := [[ 352 ]] in
          let~ value2 := [[ abi_decode_t_uint256 ~(| add ~(| headStart, offset |), dataEnd |) ]] in
          M.pure (BlockUnit.Tt, value2)
        default~ (value0, value1, value2) in
        M.pure (BlockUnit.Tt, (value0, value1, value2))
      in
      M.pure (value0, value1, value2).

    Definition abi_encode_t_uint256_to_t_uint256_fromStack (value : U256.t) (pos : U256.t) : M.t unit :=
      let~ '(_, tt) :=
        do~ [[ mstore ~(| pos, cleanup_t_uint256 ~(| value |) |) ]] in
        M.pure (BlockUnit.Tt, tt)
      in
      M.pure tt.

    Definition abi_encode_tuple_t_uint256__to_t_uint256__fromStack (headStart : U256.t) (value0 : U256.t) : M.t U256.t :=
      let~ '(_, tail) :=
        let tail := 0 in
        let~ tail := [[ add ~(| headStart, 32 |) ]] in
        do~ [[ abi_encode_t_uint256_to_t_uint256_fromStack ~(| value0, add ~(| headStart, 0 |) |) ]] in
        M.pure (BlockUnit.Tt, tail)
      in
      M.pure tail.

    Definition cleanup_t_rational_0_by_1 (value : U256.t) : M.t U256.t :=
      let~ '(_, cleaned) :=
        let cleaned := 0 in
        let~ cleaned := [[ value ]] in
        M.pure (BlockUnit.Tt, cleaned)
      in
      M.pure cleaned.

    Definition cleanup_t_rational_170141183460469231731687303715884105728_by_1 (value : U256.t) : M.t U256.t :=
      let~ '(_, cleaned) :=
        let cleaned := 0 in
        let~ cleaned := [[ value ]] in
        M.pure (BlockUnit.Tt, cleaned)
      in
      M.pure cleaned.

    Definition identity (value : U256.t) : M.t U256.t :=
      let~ '(_, ret) :=
        let ret := 0 in
        let~ ret := [[ value ]] in
        M.pure (BlockUnit.Tt, ret)
      in
      M.pure ret.

    Definition convert_t_rational_0_by_1_to_t_uint256 (value : U256.t) : M.t U256.t :=
      let~ '(_, converted) :=
        let converted := 0 in
        let~ converted := [[ cleanup_t_uint256 ~(| identity ~(| cleanup_t_rational_0_by_1 ~(| value |) |) |) ]] in
        M.pure (BlockUnit.Tt, converted)
      in
      M.pure converted.

    Definition convert_t_rational_170141183460469231731687303715884105728_by_1_to_t_uint256 (value : U256.t) : M.t U256.t :=
      let~ '(_, converted) :=
        let converted := 0 in
        let~ converted := [[ cleanup_t_uint256 ~(| identity ~(| cleanup_t_rational_170141183460469231731687303715884105728_by_1 ~(| value |) |) |) ]] in
        M.pure (BlockUnit.Tt, converted)
      in
      M.pure converted.

    Definition usrδecAddn2 (usrδx1 : U256.t) (usrδy1 : U256.t) (usrδzz1 : U256.t) (usrδzzz1 : U256.t) (usrδx2 : U256.t) (usrδy2 : U256.t) (usrδ_p : U256.t) : M.t (U256.t * U256.t * U256.t * U256.t) :=
      let~ '(_, (usrδ_x, usrδ_y, usrδ_zz, usrδ_zzz, usrδx1, usrδx2, usrδy1, usrδy2, usrδzz1)) :=
        let '(usrδ_x, usrδ_y, usrδ_zz, usrδ_zzz) := (0, 0, 0, 0) in
        let~ usrδy1 := [[ sub ~(| usrδ_p, usrδy1 |) ]] in
        let~ usrδy2 := [[ addmod ~(| mulmod ~(| usrδy2, usrδzzz1, usrδ_p |), usrδy1, usrδ_p |) ]] in
        let~ usrδx2 := [[ addmod ~(| mulmod ~(| usrδx2, usrδzz1, usrδ_p |), sub ~(| usrδ_p, usrδx1 |), usrδ_p |) ]] in
        let~ usrδ_x := [[ mulmod ~(| usrδx2, usrδx2, usrδ_p |) ]] in
        let~ usrδ_y := [[ mulmod ~(| usrδ_x, usrδx2, usrδ_p |) ]] in
        let~ usrδ_zz := [[ mulmod ~(| usrδzz1, usrδ_x, usrδ_p |) ]] in
        let~ usrδ_zzz := [[ mulmod ~(| usrδzzz1, usrδ_y, usrδ_p |) ]] in
        let~ usrδzz1 := [[ mulmod ~(| usrδx1, usrδ_x, usrδ_p |) ]] in
        let~ usrδ_x := [[ addmod ~(| addmod ~(| mulmod ~(| usrδy2, usrδy2, usrδ_p |), sub ~(| usrδ_p, usrδ_y |), usrδ_p |), mulmod ~(| sub ~(| usrδ_p, 2 |), usrδzz1, usrδ_p |), usrδ_p |) ]] in
        let~ usrδx1 := [[ mulmod ~(| addmod ~(| usrδzz1, sub ~(| usrδ_p, usrδ_x |), usrδ_p |), usrδy2, usrδ_p |) ]] in
        let~ usrδ_y := [[ addmod ~(| usrδx1, mulmod ~(| usrδy1, usrδ_y, usrδ_p |), usrδ_p |) ]] in
        M.pure (BlockUnit.Tt, (usrδ_x, usrδ_y, usrδ_zz, usrδ_zzz, usrδx1, usrδx2, usrδy1, usrδy2, usrδzz1))
      in
      M.pure (usrδ_x, usrδ_y, usrδ_zz, usrδ_zzz).

    Definition usrδmstore4 (usrδaddr : U256.t) (usrδoffset : U256.t) (usrδval1 : U256.t) (usrδval2 : U256.t) (usrδval3 : U256.t) (usrδval4 : U256.t) : M.t unit :=
      let~ '(_, usrδoffset) :=
        do~ [[ mstore ~(| add ~(| usrδoffset, usrδaddr |), usrδval1 |) ]] in
        let~ usrδoffset := [[ add ~(| 32, usrδoffset |) ]] in
        do~ [[ mstore ~(| add ~(| usrδoffset, usrδaddr |), usrδval2 |) ]] in
        let~ usrδoffset := [[ add ~(| 32, usrδoffset |) ]] in
        do~ [[ mstore ~(| add ~(| usrδoffset, usrδaddr |), usrδval3 |) ]] in
        let~ usrδoffset := [[ add ~(| 32, usrδoffset |) ]] in
        do~ [[ mstore ~(| add ~(| usrδoffset, usrδaddr |), usrδval4 |) ]] in
        let~ usrδoffset := [[ add ~(| 32, usrδoffset |) ]] in
        M.pure (BlockUnit.Tt, usrδoffset)
      in
      M.pure tt.

    Definition zero_value_for_split_t_uint256 : M.t U256.t :=
      let~ '(_, ret) :=
        let ret := 0 in
        let~ ret := [[ 0 ]] in
        M.pure (BlockUnit.Tt, ret)
      in
      M.pure ret.

    Definition fun_ecGenMulmuladdX_store_90 (var_Q_53_mpos : U256.t) (var_scalar_u_55 : U256.t) (var_scalar_v_57 : U256.t) : M.t U256.t :=
      let~ '(_, var_X_60) :=
        let var_X_60 := 0 in
        let~ zero_t_uint256_1 := [[ zero_value_for_split_t_uint256 ~(||) ]] in
        let~ var_X_60 := [[ zero_t_uint256_1 ]] in
        let~ expr_66 := [[ 0x80000000000000000000000000000000 ]] in
        let~ var_mask_63 := [[ convert_t_rational_170141183460469231731687303715884105728_by_1_to_t_uint256 ~(| expr_66 |) ]] in
        let~ _2 := [[ var_scalar_u_55 ]] in
        let~ expr_68 := [[ _2 ]] in
        let~ expr_69 := [[ 0x00 ]] in
        let~ expr_70 := [[ eq ~(| cleanup_t_uint256 ~(| expr_68 |), convert_t_rational_0_by_1_to_t_uint256 ~(| expr_69 |) |) ]] in
        let~ expr_74 := [[ expr_70 ]] in
        let_state~ expr_74 := [[
          Shallow.if_ (|
            expr_74,
            let~ _3 := [[ var_scalar_v_57 ]] in
            let~ expr_71 := [[ _3 ]] in
            let~ expr_72 := [[ 0x00 ]] in
            let~ expr_73 := [[ eq ~(| cleanup_t_uint256 ~(| expr_71 |), convert_t_rational_0_by_1_to_t_uint256 ~(| expr_72 |) |) ]] in
            let~ expr_74 := [[ expr_73 ]] in
            M.pure (BlockUnit.Tt, expr_74),
            expr_74
          |)
        ]] default~ var_X_60 in
        let_state~ var_X_60 := [[
          Shallow.if_ (|
            expr_74,
            let~ expr_75 := [[ 0x00 ]] in
            let~ var_X_60 := [[ convert_t_rational_0_by_1_to_t_uint256 ~(| expr_75 |) ]] in
            M.pure (BlockUnit.Leave, var_X_60),
            var_X_60
          |)
        ]] default~ var_X_60 in
        let~ var_Y_80 := [[ 0 ]] in
        let~ zero_t_uint256_4 := [[ zero_value_for_split_t_uint256 ~(||) ]] in
        let~ var_Y_80 := [[ zero_t_uint256_4 ]] in
        let~ var_ZZZ_83 := [[ 0 ]] in
        let~ zero_t_uint256_5 := [[ zero_value_for_split_t_uint256 ~(||) ]] in
        let~ var_ZZZ_83 := [[ zero_t_uint256_5 ]] in
        let~ var_ZZ_86 := [[ 0 ]] in
        let~ zero_t_uint256_6 := [[ zero_value_for_split_t_uint256 ~(||) ]] in
        let~ var_ZZ_86 := [[ zero_t_uint256_6 ]] in
        let_state~ '(var_X_60, var_Y_80, var_ZZZ_83, var_ZZ_86, var_mask_63) :=
          do~ [[ mstore ~(| 0x40, add ~(| mload ~(| 0x40 |), 2048 |) |) ]] in
          do~ [[ mstore ~(| add ~(| mload ~(| 0x40 |), 2080 |), mload ~(| add ~(| var_Q_53_mpos, 128 |) |) |) ]] in
          let_state~ '(var_X_60, var_Y_80, var_ZZZ_83, var_ZZ_86) :=
            let~ usrδ_modulusp := [[ mload ~(| add ~(| mload ~(| 0x40 |), 2080 |) |) ]] in
            do~ [[ usrδmstore4 ~(| mload ~(| 0x40 |), 128, mload ~(| add ~(| var_Q_53_mpos, 192 |) |), mload ~(| add ~(| var_Q_53_mpos, 224 |) |), 1, 1 |) ]] in
            do~ [[ usrδmstore4 ~(| mload ~(| 0x40 |), 256, mload ~(| add ~(| var_Q_53_mpos, 256 |) |), mload ~(| add ~(| var_Q_53_mpos, 288 |) |), 1, 1 |) ]] in
            let~ var_X_60 := [[ mload ~(| add ~(| var_Q_53_mpos, 256 |) |) ]] in
            let~ var_Y_80 := [[ mload ~(| add ~(| var_Q_53_mpos, 288 |) |) ]] in
            let~ '(var_X_60, var_Y_80, var_ZZ_86, var_ZZZ_83) := [[ usrδecAddn2 ~(| var_X_60, var_Y_80, 1, 1, mload ~(| add ~(| var_Q_53_mpos, 192 |) |), mload ~(| add ~(| var_Q_53_mpos, 224 |) |), usrδ_modulusp |) ]] in
            do~ [[ usrδmstore4 ~(| mload ~(| 0x40 |), 384, var_X_60, var_Y_80, var_ZZ_86, var_ZZZ_83 |) ]] in
            do~ [[ usrδmstore4 ~(| mload ~(| 0x40 |), 512, mload ~(| var_Q_53_mpos |), mload ~(| add ~(| 32, var_Q_53_mpos |) |), 1, 1 |) ]] in
            let~ '(var_X_60, var_Y_80, var_ZZ_86, var_ZZZ_83) := [[ usrδecAddn2 ~(| mload ~(| var_Q_53_mpos |), mload ~(| add ~(| var_Q_53_mpos, 32 |) |), 1, 1, mload ~(| add ~(| var_Q_53_mpos, 192 |) |), mload ~(| add ~(| var_Q_53_mpos, 224 |) |), usrδ_modulusp |) ]] in
            do~ [[ usrδmstore4 ~(| mload ~(| 0x40 |), 640, var_X_60, var_Y_80, var_ZZ_86, var_ZZZ_83 |) ]] in
            let~ var_X_60 := [[ mload ~(| add ~(| var_Q_53_mpos, 256 |) |) ]] in
            let~ var_Y_80 := [[ mload ~(| add ~(| var_Q_53_mpos, 288 |) |) ]] in
            let~ '(var_X_60, var_Y_80, var_ZZ_86, var_ZZZ_83) := [[ usrδecAddn2 ~(| var_X_60, var_Y_80, 1, 1, mload ~(| var_Q_53_mpos |), mload ~(| add ~(| var_Q_53_mpos, 32 |) |), usrδ_modulusp |) ]] in
            do~ [[ usrδmstore4 ~(| mload ~(| 0x40 |), 768, var_X_60, var_Y_80, var_ZZ_86, var_ZZZ_83 |) ]] in
            let~ '(var_X_60, var_Y_80, var_ZZ_86, var_ZZZ_83) := [[ usrδecAddn2 ~(| var_X_60, var_Y_80, var_ZZ_86, var_ZZZ_83, mload ~(| add ~(| var_Q_53_mpos, 192 |) |), mload ~(| add ~(| var_Q_53_mpos, 224 |) |), usrδ_modulusp |) ]] in
            do~ [[ usrδmstore4 ~(| mload ~(| 0x40 |), 896, var_X_60, var_Y_80, var_ZZ_86, var_ZZZ_83 |) ]] in
            do~ [[ usrδmstore4 ~(| mload ~(| 0x40 |), 1024, mload ~(| add ~(| var_Q_53_mpos, 64 |) |), mload ~(| add ~(| var_Q_53_mpos, 96 |) |), 1, 1 |) ]] in
            let~ '(var_X_60, var_Y_80, var_ZZ_86, var_ZZZ_83) := [[ usrδecAddn2 ~(| mload ~(| add ~(| var_Q_53_mpos, 64 |) |), mload ~(| add ~(| var_Q_53_mpos, 96 |) |), 1, 1, mload ~(| add ~(| var_Q_53_mpos, 192 |) |), mload ~(| add ~(| var_Q_53_mpos, 224 |) |), mload ~(| add ~(| mload ~(| 0x40 |), 2080 |) |) |) ]] in
            do~ [[ usrδmstore4 ~(| mload ~(| 0x40 |), 1152, var_X_60, var_Y_80, var_ZZ_86, var_ZZZ_83 |) ]] in
            let~ var_X_60 := [[ mload ~(| add ~(| var_Q_53_mpos, 256 |) |) ]] in
            let~ var_Y_80 := [[ mload ~(| add ~(| var_Q_53_mpos, 288 |) |) ]] in
            let~ '(var_X_60, var_Y_80, var_ZZ_86, var_ZZZ_83) := [[ usrδecAddn2 ~(| mload ~(| add ~(| var_Q_53_mpos, 64 |) |), mload ~(| add ~(| var_Q_53_mpos, 96 |) |), 1, 1, var_X_60, var_Y_80, mload ~(| add ~(| mload ~(| 0x40 |), 2080 |) |) |) ]] in
            do~ [[ usrδmstore4 ~(| mload ~(| 0x40 |), 1280, var_X_60, var_Y_80, var_ZZ_86, var_ZZZ_83 |) ]] in
            let~ '(var_X_60, var_Y_80, var_ZZ_86, var_ZZZ_83) := [[ usrδecAddn2 ~(| var_X_60, var_Y_80, var_ZZ_86, var_ZZZ_83, mload ~(| add ~(| var_Q_53_mpos, 192 |) |), mload ~(| add ~(| var_Q_53_mpos, 224 |) |), mload ~(| add ~(| mload ~(| 0x40 |), 2080 |) |) |) ]] in
            do~ [[ usrδmstore4 ~(| mload ~(| 0x40 |), 1408, var_X_60, var_Y_80, var_ZZ_86, var_ZZZ_83 |) ]] in
            let~ '(var_X_60, var_Y_80, var_ZZ_86, var_ZZZ_83) := [[ usrδecAddn2 ~(| mload ~(| var_Q_53_mpos |), mload ~(| add ~(| var_Q_53_mpos, 32 |) |), 1, 1, mload ~(| add ~(| var_Q_53_mpos, 64 |) |), mload ~(| add ~(| var_Q_53_mpos, 96 |) |), mload ~(| add ~(| mload ~(| 0x40 |), 2080 |) |) |) ]] in
            do~ [[ usrδmstore4 ~(| mload ~(| 0x40 |), 1536, var_X_60, var_Y_80, var_ZZ_86, var_ZZZ_83 |) ]] in
            let~ '(var_X_60, var_Y_80, var_ZZ_86, var_ZZZ_83) := [[ usrδecAddn2 ~(| var_X_60, var_Y_80, var_ZZ_86, var_ZZZ_83, mload ~(| add ~(| var_Q_53_mpos, 192 |) |), mload ~(| add ~(| var_Q_53_mpos, 224 |) |), mload ~(| add ~(| mload ~(| 0x40 |), 2080 |) |) |) ]] in
            do~ [[ usrδmstore4 ~(| mload ~(| 0x40 |), 1664, var_X_60, var_Y_80, var_ZZ_86, var_ZZZ_83 |) ]] in
            let~ var_X_60 := [[ mload ~(| add ~(| 768, mload ~(| 0x40 |) |) |) ]] in
            let~ var_Y_80 := [[ mload ~(| add ~(| 800, mload ~(| 0x40 |) |) |) ]] in
            let~ var_ZZ_86 := [[ mload ~(| add ~(| 832, mload ~(| 0x40 |) |) |) ]] in
            let~ var_ZZZ_83 := [[ mload ~(| add ~(| 864, mload ~(| 0x40 |) |) |) ]] in
            let~ '(var_X_60, var_Y_80, var_ZZ_86, var_ZZZ_83) := [[ usrδecAddn2 ~(| var_X_60, var_Y_80, var_ZZ_86, var_ZZZ_83, mload ~(| add ~(| var_Q_53_mpos, 64 |) |), mload ~(| add ~(| var_Q_53_mpos, 96 |) |), mload ~(| add ~(| mload ~(| 0x40 |), 2080 |) |) |) ]] in
            do~ [[ usrδmstore4 ~(| mload ~(| 0x40 |), 1792, var_X_60, var_Y_80, var_ZZ_86, var_ZZZ_83 |) ]] in
            let~ '(var_X_60, var_Y_80, var_ZZ_86, var_ZZZ_83) := [[ usrδecAddn2 ~(| var_X_60, var_Y_80, var_ZZ_86, var_ZZZ_83, mload ~(| add ~(| var_Q_53_mpos, 0xc0 |) |), mload ~(| add ~(| var_Q_53_mpos, 224 |) |), mload ~(| add ~(| mload ~(| 0x40 |), 2080 |) |) |) ]] in
            do~ [[ usrδmstore4 ~(| mload ~(| 0x40 |), 1920, var_X_60, var_Y_80, var_ZZ_86, var_ZZZ_83 |) ]] in
            M.pure (BlockUnit.Tt, (var_X_60, var_Y_80, var_ZZZ_83, var_ZZ_86))
          default~ (var_X_60, var_Y_80, var_ZZZ_83, var_ZZ_86, var_mask_63) in
          let~ var_ZZZ_83 := [[ 0 ]] in
          let_state~ '(var_ZZZ_83, var_mask_63) :=
            (* for loop *)
            Shallow.for_
              (* init state *)
              (var_ZZZ_83, var_mask_63)
              (* condition *)
              (fun '(var_ZZZ_83, var_mask_63) => [[
                iszero ~(| var_ZZZ_83 |)
              ]])
              (* body *)
              (fun '(var_ZZZ_83, var_mask_63) =>
                Shallow.lift_state_update
                  (fun var_ZZZ_83 => (var_ZZZ_83, var_mask_63))
                  (let~ var_ZZZ_83 := [[ add ~(| add ~(| sub ~(| 1, iszero ~(| and ~(| var_scalar_u_55, var_mask_63 |) |) |), shl ~(| 1, sub ~(| 1, iszero ~(| and ~(| shr ~(| 128, var_scalar_u_55 |), var_mask_63 |) |) |) |) |), add ~(| shl ~(| 2, sub ~(| 1, iszero ~(| and ~(| var_scalar_v_57, var_mask_63 |) |) |) |), shl ~(| 3, sub ~(| 1, iszero ~(| and ~(| shr ~(| 128, var_scalar_v_57 |), var_mask_63 |) |) |) |) |) |) ]] in
                  M.pure (BlockUnit.Tt, var_ZZZ_83)))
              (* post *)
              (fun '(var_ZZZ_83, var_mask_63) =>
                Shallow.lift_state_update
                  (fun var_mask_63 => (var_ZZZ_83, var_mask_63))
                  (let~ var_mask_63 := [[ shr ~(| 1, var_mask_63 |) ]] in
                  M.pure (BlockUnit.Tt, var_mask_63)))
          default~ (var_X_60, var_Y_80, var_ZZZ_83, var_ZZ_86, var_mask_63) in
          let~ var_X_60 := [[ mload ~(| add ~(| mload ~(| 0x40 |), shl ~(| 7, var_ZZZ_83 |) |) |) ]] in
          let~ var_Y_80 := [[ mload ~(| add ~(| mload ~(| 0x40 |), add ~(| 32, shl ~(| 7, var_ZZZ_83 |) |) |) |) ]] in
          let~ var_ZZ_86 := [[ mload ~(| add ~(| mload ~(| 0x40 |), add ~(| 64, shl ~(| 7, var_ZZZ_83 |) |) |) |) ]] in
          let~ var_ZZZ_83 := [[ mload ~(| add ~(| mload ~(| 0x40 |), add ~(| 96, shl ~(| 7, var_ZZZ_83 |) |) |) |) ]] in
          let~ usrδMem := [[ mload ~(| 0x40 |) ]] in
          let~ usrδ_p := [[ mload ~(| add ~(| usrδMem, 2080 |) |) ]] in
          let_state~ '(var_X_60, var_Y_80, var_ZZZ_83, var_ZZ_86, var_mask_63) :=
            (* for loop *)
            Shallow.for_
              (* init state *)
              (var_X_60, var_Y_80, var_ZZZ_83, var_ZZ_86, var_mask_63)
              (* condition *)
              (fun '(var_X_60, var_Y_80, var_ZZZ_83, var_ZZ_86, var_mask_63) => [[
                gt ~(| var_mask_63, 0 |)
              ]])
              (* body *)
              (fun '(var_X_60, var_Y_80, var_ZZZ_83, var_ZZ_86, var_mask_63) =>
                Shallow.lift_state_update
                  (fun '(var_X_60, var_Y_80, var_ZZZ_83, var_ZZ_86) => (var_X_60, var_Y_80, var_ZZZ_83, var_ZZ_86, var_mask_63))
                  (let_state~ '(var_X_60, var_Y_80, var_ZZZ_83, var_ZZ_86) :=
                    let~ usrδT1 := [[ mulmod ~(| 2, var_Y_80, usrδ_p |) ]] in
                    let~ usrδT2 := [[ mulmod ~(| usrδT1, usrδT1, usrδ_p |) ]] in
                    let~ usrδT3 := [[ mulmod ~(| var_X_60, usrδT2, usrδ_p |) ]] in
                    let~ usrδT1 := [[ mulmod ~(| usrδT1, usrδT2, usrδ_p |) ]] in
                    let~ usrδT4 := [[ mulmod ~(| mload ~(| add ~(| var_Q_53_mpos, 160 |) |), mulmod ~(| var_ZZ_86, var_ZZ_86, usrδ_p |), usrδ_p |) ]] in
                    let~ usrδT4 := [[ addmod ~(| mulmod ~(| 3, mulmod ~(| var_X_60, var_X_60, usrδ_p |), usrδ_p |), usrδT4, usrδ_p |) ]] in
                    let~ var_ZZZ_83 := [[ mulmod ~(| usrδT1, var_ZZZ_83, usrδ_p |) ]] in
                    let~ var_ZZ_86 := [[ mulmod ~(| usrδT2, var_ZZ_86, usrδ_p |) ]] in
                    let~ var_X_60 := [[ sub ~(| usrδ_p, 2 |) ]] in
                    let~ var_X_60 := [[ addmod ~(| mulmod ~(| usrδT4, usrδT4, usrδ_p |), mulmod ~(| var_X_60, usrδT3, usrδ_p |), usrδ_p |) ]] in
                    let~ usrδT2 := [[ mulmod ~(| usrδT4, addmod ~(| var_X_60, sub ~(| usrδ_p, usrδT3 |), usrδ_p |), usrδ_p |) ]] in
                    let~ var_Y_80 := [[ addmod ~(| mulmod ~(| usrδT1, var_Y_80, usrδ_p |), usrδT2, usrδ_p |) ]] in
                    M.pure (BlockUnit.Tt, (var_X_60, var_Y_80, var_ZZZ_83, var_ZZ_86))
                  default~ (var_X_60, var_Y_80, var_ZZZ_83, var_ZZ_86) in
                  let~ usrδT1 := [[ add ~(| add ~(| sub ~(| 1, iszero ~(| and ~(| var_scalar_u_55, var_mask_63 |) |) |), shl ~(| 1, sub ~(| 1, iszero ~(| and ~(| shr ~(| 128, var_scalar_u_55 |), var_mask_63 |) |) |) |) |), add ~(| shl ~(| 2, sub ~(| 1, iszero ~(| and ~(| var_scalar_v_57, var_mask_63 |) |) |) |), shl ~(| 3, sub ~(| 1, iszero ~(| and ~(| shr ~(| 128, var_scalar_v_57 |), var_mask_63 |) |) |) |) |) |) ]] in
                  let_state~ var_Y_80 := [[
                    Shallow.if_ (|
                      iszero ~(| usrδT1 |),
                      let~ var_Y_80 := [[ sub ~(| usrδ_p, var_Y_80 |) ]] in
                      M.pure (BlockUnit.Continue, var_Y_80),
                      var_Y_80
                    |)
                  ]] default~ (var_X_60, var_Y_80, var_ZZZ_83, var_ZZ_86) in
                  let~ usrδT1 := [[ shl ~(| 7, usrδT1 |) ]] in
                  let~ usrδT4 := [[ mload ~(| add ~(| usrδMem, usrδT1 |) |) ]] in
                  do~ [[ mstore ~(| add ~(| usrδMem, 2144 |), mload ~(| add ~(| usrδMem, add ~(| 96, usrδT1 |) |) |) |) ]] in
                  let_state~ '(var_X_60, var_Y_80, var_ZZZ_83, var_ZZ_86) := [[
                    Shallow.if_ (|
                      iszero ~(| var_ZZ_86 |),
                      let~ var_X_60 := [[ usrδT4 ]] in
                      let~ var_Y_80 := [[ mload ~(| add ~(| usrδMem, add ~(| 32, usrδT1 |) |) |) ]] in
                      let~ var_ZZ_86 := [[ mload ~(| add ~(| usrδMem, add ~(| 64, usrδT1 |) |) |) ]] in
                      let~ var_ZZZ_83 := [[ mload ~(| add ~(| usrδMem, add ~(| 96, usrδT1 |) |) |) ]] in
                      M.pure (BlockUnit.Continue, (var_X_60, var_Y_80, var_ZZZ_83, var_ZZ_86)),
                      (var_X_60, var_Y_80, var_ZZZ_83, var_ZZ_86)
                    |)
                  ]] default~ (var_X_60, var_Y_80, var_ZZZ_83, var_ZZ_86) in
                  do~ [[ mstore ~(| add ~(| usrδMem, 2112 |), addmod ~(| mulmod ~(| mload ~(| add ~(| usrδMem, add ~(| 32, usrδT1 |) |) |), var_ZZZ_83, usrδ_p |), mulmod ~(| var_Y_80, mload ~(| add ~(| usrδMem, 2144 |) |), usrδ_p |), usrδ_p |) |) ]] in
                  let~ usrδT1 := [[ mload ~(| add ~(| usrδMem, add ~(| 64, usrδT1 |) |) |) ]] in
                  let~ usrδT2 := [[ addmod ~(| mulmod ~(| usrδT4, var_ZZ_86, usrδ_p |), sub ~(| usrδ_p, mulmod ~(| var_X_60, usrδT1, usrδ_p |) |), usrδ_p |) ]] in
                  let_state~ '(usrδT1, usrδT2, usrδT4, var_X_60, var_Y_80, var_ZZZ_83, var_ZZ_86) := [[
                    Shallow.if_ (|
                      iszero ~(| mload ~(| add ~(| usrδMem, 2112 |) |) |),
                      let_state~ '(usrδT1, usrδT2, usrδT4, var_X_60, var_Y_80, var_ZZZ_83, var_ZZ_86) := [[
                        Shallow.if_ (|
                          iszero ~(| usrδT2 |),
                          let~ usrδT1 := [[ mulmod ~(| sub ~(| usrδ_p, 2 |), var_Y_80, usrδ_p |) ]] in
                          let~ usrδT2 := [[ mulmod ~(| usrδT1, usrδT1, usrδ_p |) ]] in
                          do~ [[ mstore ~(| add ~(| usrδMem, 2112 |), mulmod ~(| var_X_60, usrδT2, usrδ_p |) |) ]] in
                          let~ usrδT1 := [[ mulmod ~(| usrδT1, usrδT2, usrδ_p |) ]] in
                          let~ usrδT4 := [[ mulmod ~(| mload ~(| add ~(| var_Q_53_mpos, 160 |) |), mulmod ~(| var_ZZ_86, var_ZZ_86, usrδ_p |), usrδ_p |) ]] in
                          let~ usrδT4 := [[ addmod ~(| mulmod ~(| 3, mulmod ~(| var_X_60, var_X_60, usrδ_p |), usrδ_p |), usrδT4, usrδ_p |) ]] in
                          let~ var_ZZZ_83 := [[ mulmod ~(| usrδT1, var_ZZZ_83, usrδ_p |) ]] in
                          let~ var_ZZ_86 := [[ mulmod ~(| usrδT2, var_ZZ_86, usrδ_p |) ]] in
                          let~ var_X_60 := [[ addmod ~(| mulmod ~(| usrδT4, usrδT4, usrδ_p |), mulmod ~(| sub ~(| usrδ_p, 2 |), mload ~(| add ~(| usrδMem, 2112 |) |), usrδ_p |), usrδ_p |) ]] in
                          let~ usrδT2 := [[ mulmod ~(| usrδT4, addmod ~(| mload ~(| add ~(| usrδMem, 2112 |) |), sub ~(| usrδ_p, var_X_60 |), usrδ_p |), usrδ_p |) ]] in
                          let~ var_Y_80 := [[ addmod ~(| usrδT2, mulmod ~(| usrδT1, var_Y_80, usrδ_p |), usrδ_p |) ]] in
                          M.pure (BlockUnit.Continue, (usrδT1, usrδT2, usrδT4, var_X_60, var_Y_80, var_ZZZ_83, var_ZZ_86)),
                          (usrδT1, usrδT2, usrδT4, var_X_60, var_Y_80, var_ZZZ_83, var_ZZ_86)
                        |)
                      ]] default~ (usrδT1, usrδT2, usrδT4, var_X_60, var_Y_80, var_ZZZ_83, var_ZZ_86) in
                      M.pure (BlockUnit.Tt, (usrδT1, usrδT2, usrδT4, var_X_60, var_Y_80, var_ZZZ_83, var_ZZ_86)),
                      (usrδT1, usrδT2, usrδT4, var_X_60, var_Y_80, var_ZZZ_83, var_ZZ_86)
                    |)
                  ]] default~ (var_X_60, var_Y_80, var_ZZZ_83, var_ZZ_86) in
                  let~ usrδT4 := [[ mulmod ~(| usrδT2, usrδT2, usrδ_p |) ]] in
                  let~ usrδT2 := [[ mulmod ~(| usrδT4, usrδT2, usrδ_p |) ]] in
                  let~ var_ZZ_86 := [[ mulmod ~(| mulmod ~(| var_ZZ_86, usrδT4, usrδ_p |), usrδT1, usrδ_p |) ]] in
                  let~ usrδT1 := [[ mulmod ~(| var_X_60, usrδT1, usrδ_p |) ]] in
                  let~ var_ZZZ_83 := [[ mulmod ~(| mulmod ~(| var_ZZZ_83, usrδT2, usrδ_p |), mload ~(| add ~(| usrδMem, 2144 |) |), usrδ_p |) ]] in
                  let~ var_X_60 := [[ addmod ~(| addmod ~(| mulmod ~(| mload ~(| add ~(| usrδMem, 2112 |) |), mload ~(| add ~(| usrδMem, 2112 |) |), usrδ_p |), sub ~(| usrδ_p, usrδT2 |), usrδ_p |), mulmod ~(| usrδT1, mulmod ~(| sub ~(| usrδ_p, 2 |), usrδT4, usrδ_p |), usrδ_p |), usrδ_p |) ]] in
                  let~ usrδT4 := [[ mulmod ~(| usrδT1, usrδT4, usrδ_p |) ]] in
                  let~ var_Y_80 := [[ addmod ~(| mulmod ~(| addmod ~(| usrδT4, sub ~(| usrδ_p, var_X_60 |), usrδ_p |), mload ~(| add ~(| usrδMem, 2112 |) |), usrδ_p |), mulmod ~(| mulmod ~(| var_Y_80, mload ~(| add ~(| usrδMem, 2144 |) |), usrδ_p |), usrδT2, usrδ_p |), usrδ_p |) ]] in
                  M.pure (BlockUnit.Tt, (var_X_60, var_Y_80, var_ZZZ_83, var_ZZ_86))))
              (* post *)
              (fun '(var_X_60, var_Y_80, var_ZZZ_83, var_ZZ_86, var_mask_63) =>
                Shallow.lift_state_update
                  (fun var_mask_63 => (var_X_60, var_Y_80, var_ZZZ_83, var_ZZ_86, var_mask_63))
                  (let~ var_mask_63 := [[ shr ~(| 1, var_mask_63 |) ]] in
                  M.pure (BlockUnit.Tt, var_mask_63)))
          default~ (var_X_60, var_Y_80, var_ZZZ_83, var_ZZ_86, var_mask_63) in
          do~ [[ mstore ~(| 0x40, 2176 |) ]] in
          let~ usrδT := [[ mload ~(| 0x40 |) ]] in
          do~ [[ mstore ~(| add ~(| usrδT, 0x60 |), var_ZZ_86 |) ]] in
          do~ [[ mstore ~(| usrδT, 0x20 |) ]] in
          do~ [[ mstore ~(| add ~(| usrδT, 0x20 |), 0x20 |) ]] in
          do~ [[ mstore ~(| add ~(| usrδT, 0x40 |), 0x20 |) ]] in
          do~ [[ mstore ~(| add ~(| usrδT, 0x80 |), sub ~(| usrδ_p, 2 |) |) ]] in
          do~ [[ mstore ~(| add ~(| usrδT, 0xa0 |), usrδ_p |) ]] in
          let_state~ 'tt := [[
            Shallow.if_ (|
              iszero ~(| staticcall ~(| not ~(| 0 |), 0x05, usrδT, 0xc0, usrδT, 0x20 |) |),
              do~ [[ mstore ~(| 0x40, 2047 |) ]] in
              do~ [[ revert ~(| 0x40, 0x20 |) ]] in
              M.pure (BlockUnit.Tt, tt),
              tt
            |)
          ]] default~ (var_X_60, var_Y_80, var_ZZZ_83, var_ZZ_86, var_mask_63) in
          let~ var_X_60 := [[ mulmod ~(| var_X_60, mload ~(| usrδT |), usrδ_p |) ]] in
          M.pure (BlockUnit.Tt, (var_X_60, var_Y_80, var_ZZZ_83, var_ZZ_86, var_mask_63))
        default~ var_X_60 in
        M.pure (BlockUnit.Tt, var_X_60)
      in
      M.pure var_X_60.

    Definition revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb : M.t unit :=
      let~ '(_, tt) :=
        do~ [[ revert ~(| 0, 0 |) ]] in
        M.pure (BlockUnit.Tt, tt)
      in
      M.pure tt.

    Definition external_fun_ecGenMulmuladdX_store_90 : M.t unit :=
      let~ '(_, tt) :=
        let_state~ 'tt := [[
          Shallow.if_ (|
            callvalue ~(||),
            do~ [[ revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb ~(||) ]] in
            M.pure (BlockUnit.Tt, tt),
            tt
          |)
        ]] default~ tt in
        let~ '(param_0, param_1, param_2) := [[ abi_decode_tuple_t_arrayδ_t_uint256_δ10_memory_ptrt_uint256t_uint256 ~(| 4, calldatasize ~(||) |) ]] in
        let~ ret_0 := [[ fun_ecGenMulmuladdX_store_90 ~(| param_0, param_1, param_2 |) ]] in
        let~ memPos := [[ allocate_unbounded ~(||) ]] in
        let~ memEnd := [[ abi_encode_tuple_t_uint256__to_t_uint256__fromStack ~(| memPos, ret_0 |) ]] in
        do~ [[ return_ ~(| memPos, sub ~(| memEnd, memPos |) |) ]] in
        M.pure (BlockUnit.Tt, tt)
      in
      M.pure tt.

    Definition revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74 : M.t unit :=
      let~ '(_, tt) :=
        do~ [[ revert ~(| 0, 0 |) ]] in
        M.pure (BlockUnit.Tt, tt)
      in
      M.pure tt.

    Definition revert_error_c1322bf8034eace5e0b5c7295db60986aa89aae5e0ea0873e4689e076861a5db : M.t unit :=
      let~ '(_, tt) :=
        do~ [[ revert ~(| 0, 0 |) ]] in
        M.pure (BlockUnit.Tt, tt)
      in
      M.pure tt.

    Definition shift_right_224_unsigned (value : U256.t) : M.t U256.t :=
      let~ '(_, newValue) :=
        let newValue := 0 in
        let~ newValue := [[ shr ~(| 224, value |) ]] in
        M.pure (BlockUnit.Tt, newValue)
      in
      M.pure newValue.

    Definition body : M.t unit :=
      let~ '(_, result) :=
        do~ [[ mstore ~(| 64, memoryguard ~(| 128 |) |) ]] in
        let_state~ 'tt := [[
          Shallow.if_ (|
            iszero ~(| lt ~(| calldatasize ~(||), 4 |) |),
            let~ selector := [[ shift_right_224_unsigned ~(| calldataload ~(| 0 |) |) ]] in
            let_state~ 'tt := [[
              (* switch *)
              let~ δ := [[ selector ]] in
              if δ =? 0x81a379ec then
                do~ [[ external_fun_ecGenMulmuladdX_store_90 ~(||) ]] in
                M.pure (BlockUnit.Tt, tt)
              else
                M.pure (BlockUnit.Tt, tt)
            ]] default~ tt in
            M.pure (BlockUnit.Tt, tt),
            tt
          |)
        ]] default~ tt in
        do~ [[ revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74 ~(||) ]] in
        M.pure (BlockUnit.Tt, tt)
      in
      M.pure result.
  End Contract_91_deployed.
End Contract_91.
