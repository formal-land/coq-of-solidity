IR:

/// @use-src 0:"CoqOfSolidity/contracts/scl/mulmuladdX_fullgen_b4/contract.sol"
object "Contract_91" {
    code {
        /// @src 0:2011:14102  "contract Contract {..."
        mstore(64, memoryguard(128))
        if callvalue() { revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb() }

        constructor_Contract_91()

        let _1 := allocate_unbounded()
        codecopy(_1, dataoffset("Contract_91_deployed"), datasize("Contract_91_deployed"))

        return(_1, datasize("Contract_91_deployed"))

        function allocate_unbounded() -> memPtr {
            memPtr := mload(64)
        }

        function revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb() {
            revert(0, 0)
        }

        /// @src 0:2011:14102  "contract Contract {..."
        function constructor_Contract_91() {

            /// @src 0:2011:14102  "contract Contract {..."

        }
        /// @src 0:2011:14102  "contract Contract {..."

    }
    /// @use-src 0:"CoqOfSolidity/contracts/scl/mulmuladdX_fullgen_b4/contract.sol"
    object "Contract_91_deployed" {
        code {
            /// @src 0:2011:14102  "contract Contract {..."
            mstore(64, memoryguard(128))

            if iszero(lt(calldatasize(), 4))
            {
                let selector := shift_right_224_unsigned(calldataload(0))
                switch selector

                case 0x81a379ec
                {
                    // ecGenMulmuladdX_store(uint256[10],uint256,uint256)

                    external_fun_ecGenMulmuladdX_store_90()
                }

                default {}
            }

            revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74()

            function shift_right_224_unsigned(value) -> newValue {
                newValue :=

                shr(224, value)

            }

            function allocate_unbounded() -> memPtr {
                memPtr := mload(64)
            }

            function revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb() {
                revert(0, 0)
            }

            function revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b() {
                revert(0, 0)
            }

            function revert_error_c1322bf8034eace5e0b5c7295db60986aa89aae5e0ea0873e4689e076861a5db() {
                revert(0, 0)
            }

            function revert_error_1b9f4a0a5773e33b91aa01db23bf8c55fce1411167c872835e7fa00a4f17d46d() {
                revert(0, 0)
            }

            function round_up_to_mul_of_32(value) -> result {
                result := and(add(value, 31), not(31))
            }

            function panic_error_0x41() {
                mstore(0, 35408467139433450592217433187231851964531694900788300625387963629091585785856)
                mstore(4, 0x41)
                revert(0, 0x24)
            }

            function finalize_allocation(memPtr, size) {
                let newFreePtr := add(memPtr, round_up_to_mul_of_32(size))
                // protect against overflow
                if or(gt(newFreePtr, 0xffffffffffffffff), lt(newFreePtr, memPtr)) { panic_error_0x41() }
                mstore(64, newFreePtr)
            }

            function allocate_memory(size) -> memPtr {
                memPtr := allocate_unbounded()
                finalize_allocation(memPtr, size)
            }

            function array_allocation_size_t_array$_t_uint256_$10_memory_ptr(length) -> size {
                // Make sure we can allocate memory without overflow
                if gt(length, 0xffffffffffffffff) { panic_error_0x41() }

                size := mul(length, 0x20)

            }

            function revert_error_81385d8c0b31fffe14be1da910c8bd3a80be4cfa248e04f42ec0faea3132a8ef() {
                revert(0, 0)
            }

            function cleanup_t_uint256(value) -> cleaned {
                cleaned := value
            }

            function validator_revert_t_uint256(value) {
                if iszero(eq(value, cleanup_t_uint256(value))) { revert(0, 0) }
            }

            function abi_decode_t_uint256(offset, end) -> value {
                value := calldataload(offset)
                validator_revert_t_uint256(value)
            }

            // uint256[10]
            function abi_decode_available_length_t_array$_t_uint256_$10_memory_ptr(offset, length, end) -> array {
                array := allocate_memory(array_allocation_size_t_array$_t_uint256_$10_memory_ptr(length))
                let dst := array

                let srcEnd := add(offset, mul(length, 0x20))
                if gt(srcEnd, end) {
                    revert_error_81385d8c0b31fffe14be1da910c8bd3a80be4cfa248e04f42ec0faea3132a8ef()
                }
                for { let src := offset } lt(src, srcEnd) { src := add(src, 0x20) }
                {

                    let elementPos := src

                    mstore(dst, abi_decode_t_uint256(elementPos, end))
                    dst := add(dst, 0x20)
                }
            }

            // uint256[10]
            function abi_decode_t_array$_t_uint256_$10_memory_ptr(offset, end) -> array {
                if iszero(slt(add(offset, 0x1f), end)) { revert_error_1b9f4a0a5773e33b91aa01db23bf8c55fce1411167c872835e7fa00a4f17d46d() }
                let length := 0x0a
                array := abi_decode_available_length_t_array$_t_uint256_$10_memory_ptr(offset, length, end)
            }

            function abi_decode_tuple_t_array$_t_uint256_$10_memory_ptrt_uint256t_uint256(headStart, dataEnd) -> value0, value1, value2 {
                if slt(sub(dataEnd, headStart), 384) { revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b() }

                {

                    let offset := 0

                    value0 := abi_decode_t_array$_t_uint256_$10_memory_ptr(add(headStart, offset), dataEnd)
                }

                {

                    let offset := 320

                    value1 := abi_decode_t_uint256(add(headStart, offset), dataEnd)
                }

                {

                    let offset := 352

                    value2 := abi_decode_t_uint256(add(headStart, offset), dataEnd)
                }

            }

            function abi_encode_t_uint256_to_t_uint256_fromStack(value, pos) {
                mstore(pos, cleanup_t_uint256(value))
            }

            function abi_encode_tuple_t_uint256__to_t_uint256__fromStack(headStart , value0) -> tail {
                tail := add(headStart, 32)

                abi_encode_t_uint256_to_t_uint256_fromStack(value0,  add(headStart, 0))

            }

            function external_fun_ecGenMulmuladdX_store_90() {

                if callvalue() { revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb() }
                let param_0, param_1, param_2 :=  abi_decode_tuple_t_array$_t_uint256_$10_memory_ptrt_uint256t_uint256(4, calldatasize())
                let ret_0 :=  fun_ecGenMulmuladdX_store_90(param_0, param_1, param_2)
                let memPos := allocate_unbounded()
                let memEnd := abi_encode_tuple_t_uint256__to_t_uint256__fromStack(memPos , ret_0)
                return(memPos, sub(memEnd, memPos))

            }

            function revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74() {
                revert(0, 0)
            }

            function zero_value_for_split_t_uint256() -> ret {
                ret := 0
            }

            function cleanup_t_rational_170141183460469231731687303715884105728_by_1(value) -> cleaned {
                cleaned := value
            }

            function identity(value) -> ret {
                ret := value
            }

            function convert_t_rational_170141183460469231731687303715884105728_by_1_to_t_uint256(value) -> converted {
                converted := cleanup_t_uint256(identity(cleanup_t_rational_170141183460469231731687303715884105728_by_1(value)))
            }

            function cleanup_t_rational_0_by_1(value) -> cleaned {
                cleaned := value
            }

            function convert_t_rational_0_by_1_to_t_uint256(value) -> converted {
                converted := cleanup_t_uint256(identity(cleanup_t_rational_0_by_1(value)))
            }

            function usr$mstore4(usr$addr, usr$offset, usr$val1, usr$val2, usr$val3, usr$val4)
            {
                mstore(add(usr$offset, usr$addr), usr$val1)
                usr$offset := add(32, usr$offset)
                mstore(add(usr$offset, usr$addr), usr$val2)
                usr$offset := add(32, usr$offset)
                mstore(add(usr$offset, usr$addr), usr$val3)
                usr$offset := add(32, usr$offset)
                mstore(add(usr$offset, usr$addr), usr$val4)
                usr$offset := add(32, usr$offset)
            }

            function usr$ecAddn2(usr$x1, usr$y1, usr$zz1, usr$zzz1, usr$x2, usr$y2, usr$_p) -> usr$_x, usr$_y, usr$_zz, usr$_zzz
            {
                usr$y1 := sub(usr$_p, usr$y1)
                usr$y2 := addmod(mulmod(usr$y2, usr$zzz1, usr$_p), usr$y1, usr$_p)
                usr$x2 := addmod(mulmod(usr$x2, usr$zz1, usr$_p), sub(usr$_p, usr$x1), usr$_p)
                usr$_x := mulmod(usr$x2, usr$x2, usr$_p)
                usr$_y := mulmod(usr$_x, usr$x2, usr$_p)
                usr$_zz := mulmod(usr$zz1, usr$_x, usr$_p)
                usr$_zzz := mulmod(usr$zzz1, usr$_y, usr$_p)
                usr$zz1 := mulmod(usr$x1, usr$_x, usr$_p)
                usr$_x := addmod(addmod(mulmod(usr$y2, usr$y2, usr$_p), sub(usr$_p, usr$_y), usr$_p), mulmod(sub(usr$_p, 2), usr$zz1, usr$_p), usr$_p)
                usr$x1 := mulmod(addmod(usr$zz1, sub(usr$_p, usr$_x), usr$_p), usr$y2, usr$_p)
                usr$_y := addmod(usr$x1, mulmod(usr$y1, usr$_y, usr$_p), usr$_p)
            }

            /// @ast-id 90
            /// @src 0:2383:14100  "function ecGenMulmuladdX_store(..."
            function fun_ecGenMulmuladdX_store_90(var_Q_53_mpos, var_scalar_u_55, var_scalar_v_57) -> var_X_60 {
                /// @src 0:2586:2595  "uint256 X"
                let zero_t_uint256_1 := zero_value_for_split_t_uint256()
                var_X_60 := zero_t_uint256_1

                /// @src 0:2620:2626  "1<<127"
                let expr_66 := 0x80000000000000000000000000000000
                /// @src 0:2607:2626  "uint256 mask=1<<127"
                let var_mask_63 := convert_t_rational_170141183460469231731687303715884105728_by_1_to_t_uint256(expr_66)
                /// @src 0:2679:2687  "scalar_u"
                let _2 := var_scalar_u_55
                let expr_68 := _2
                /// @src 0:2689:2690  "0"
                let expr_69 := 0x00
                /// @src 0:2679:2690  "scalar_u==0"
                let expr_70 := eq(cleanup_t_uint256(expr_68), convert_t_rational_0_by_1_to_t_uint256(expr_69))
                /// @src 0:2679:2703  "scalar_u==0&&scalar_v==0"
                let expr_74 := expr_70
                if expr_74 {
                    /// @src 0:2692:2700  "scalar_v"
                    let _3 := var_scalar_v_57
                    let expr_71 := _3
                    /// @src 0:2702:2703  "0"
                    let expr_72 := 0x00
                    /// @src 0:2692:2703  "scalar_v==0"
                    let expr_73 := eq(cleanup_t_uint256(expr_71), convert_t_rational_0_by_1_to_t_uint256(expr_72))
                    /// @src 0:2679:2703  "scalar_u==0&&scalar_v==0"
                    expr_74 := expr_73
                }
                /// @src 0:2676:2737  "if(scalar_u==0&&scalar_v==0){..."
                if expr_74 {
                    /// @src 0:2725:2726  "0"
                    let expr_75 := 0x00
                    /// @src 0:2718:2726  "return 0"
                    var_X_60 := convert_t_rational_0_by_1_to_t_uint256(expr_75)
                    leave
                    /// @src 0:2676:2737  "if(scalar_u==0&&scalar_v==0){..."
                }
                /// @src 0:2746:2755  "uint256 Y"
                let var_Y_80
                let zero_t_uint256_4 := zero_value_for_split_t_uint256()
                var_Y_80 := zero_t_uint256_4
                /// @src 0:2765:2776  "uint256 ZZZ"
                let var_ZZZ_83
                let zero_t_uint256_5 := zero_value_for_split_t_uint256()
                var_ZZZ_83 := zero_t_uint256_5
                /// @src 0:2786:2796  "uint256 ZZ"
                let var_ZZ_86
                let zero_t_uint256_6 := zero_value_for_split_t_uint256()
                var_ZZ_86 := zero_t_uint256_6
                /// @src 0:2864:14080  "assembly (\"memory-safe\") {..."
                {
                    mstore(0x40, add(mload(0x40), 2048))
                    mstore(add(mload(0x40), 2080), mload(add(var_Q_53_mpos, 128)))
                    {
                        let usr$_modulusp := mload(add(mload(0x40), 2080))
                        usr$mstore4(mload(0x40), 128, mload(add(var_Q_53_mpos, 192)), mload(add(var_Q_53_mpos, 224)), 1, 1)
                        usr$mstore4(mload(0x40), 256, mload(add(var_Q_53_mpos, 256)), mload(add(var_Q_53_mpos, 288)), 1, 1)
                        var_X_60 := mload(add(var_Q_53_mpos, 256))
                        var_Y_80 := mload(add(var_Q_53_mpos, 288))
                        var_X_60, var_Y_80, var_ZZ_86, var_ZZZ_83 := usr$ecAddn2(var_X_60, var_Y_80, 1, 1, mload(add(var_Q_53_mpos, 192)), mload(add(var_Q_53_mpos, 224)), usr$_modulusp)
                        usr$mstore4(mload(0x40), 384, var_X_60, var_Y_80, var_ZZ_86, var_ZZZ_83)
                        usr$mstore4(mload(0x40), 512, mload(var_Q_53_mpos), mload(add(32, var_Q_53_mpos)), 1, 1)
                        var_X_60, var_Y_80, var_ZZ_86, var_ZZZ_83 := usr$ecAddn2(mload(var_Q_53_mpos), mload(add(var_Q_53_mpos, 32)), 1, 1, mload(add(var_Q_53_mpos, 192)), mload(add(var_Q_53_mpos, 224)), usr$_modulusp)
                        usr$mstore4(mload(0x40), 640, var_X_60, var_Y_80, var_ZZ_86, var_ZZZ_83)
                        var_X_60 := mload(add(var_Q_53_mpos, 256))
                        var_Y_80 := mload(add(var_Q_53_mpos, 288))
                        var_X_60, var_Y_80, var_ZZ_86, var_ZZZ_83 := usr$ecAddn2(var_X_60, var_Y_80, 1, 1, mload(var_Q_53_mpos), mload(add(var_Q_53_mpos, 32)), usr$_modulusp)
                        usr$mstore4(mload(0x40), 768, var_X_60, var_Y_80, var_ZZ_86, var_ZZZ_83)
                        var_X_60, var_Y_80, var_ZZ_86, var_ZZZ_83 := usr$ecAddn2(var_X_60, var_Y_80, var_ZZ_86, var_ZZZ_83, mload(add(var_Q_53_mpos, 192)), mload(add(var_Q_53_mpos, 224)), usr$_modulusp)
                        usr$mstore4(mload(0x40), 896, var_X_60, var_Y_80, var_ZZ_86, var_ZZZ_83)
                        usr$mstore4(mload(0x40), 1024, mload(add(var_Q_53_mpos, 64)), mload(add(var_Q_53_mpos, 96)), 1, 1)
                        var_X_60, var_Y_80, var_ZZ_86, var_ZZZ_83 := usr$ecAddn2(mload(add(var_Q_53_mpos, 64)), mload(add(var_Q_53_mpos, 96)), 1, 1, mload(add(var_Q_53_mpos, 192)), mload(add(var_Q_53_mpos, 224)), mload(add(mload(0x40), 2080)))
                        usr$mstore4(mload(0x40), 1152, var_X_60, var_Y_80, var_ZZ_86, var_ZZZ_83)
                        var_X_60 := mload(add(var_Q_53_mpos, 256))
                        var_Y_80 := mload(add(var_Q_53_mpos, 288))
                        var_X_60, var_Y_80, var_ZZ_86, var_ZZZ_83 := usr$ecAddn2(mload(add(var_Q_53_mpos, 64)), mload(add(var_Q_53_mpos, 96)), 1, 1, var_X_60, var_Y_80, mload(add(mload(0x40), 2080)))
                        usr$mstore4(mload(0x40), 1280, var_X_60, var_Y_80, var_ZZ_86, var_ZZZ_83)
                        var_X_60, var_Y_80, var_ZZ_86, var_ZZZ_83 := usr$ecAddn2(var_X_60, var_Y_80, var_ZZ_86, var_ZZZ_83, mload(add(var_Q_53_mpos, 192)), mload(add(var_Q_53_mpos, 224)), mload(add(mload(0x40), 2080)))
                        usr$mstore4(mload(0x40), 1408, var_X_60, var_Y_80, var_ZZ_86, var_ZZZ_83)
                        var_X_60, var_Y_80, var_ZZ_86, var_ZZZ_83 := usr$ecAddn2(mload(var_Q_53_mpos), mload(add(var_Q_53_mpos, 32)), 1, 1, mload(add(var_Q_53_mpos, 64)), mload(add(var_Q_53_mpos, 96)), mload(add(mload(0x40), 2080)))
                        usr$mstore4(mload(0x40), 1536, var_X_60, var_Y_80, var_ZZ_86, var_ZZZ_83)
                        var_X_60, var_Y_80, var_ZZ_86, var_ZZZ_83 := usr$ecAddn2(var_X_60, var_Y_80, var_ZZ_86, var_ZZZ_83, mload(add(var_Q_53_mpos, 192)), mload(add(var_Q_53_mpos, 224)), mload(add(mload(0x40), 2080)))
                        usr$mstore4(mload(0x40), 1664, var_X_60, var_Y_80, var_ZZ_86, var_ZZZ_83)
                        var_X_60 := mload(add(768, mload(0x40)))
                        var_Y_80 := mload(add(800, mload(0x40)))
                        var_ZZ_86 := mload(add(832, mload(0x40)))
                        var_ZZZ_83 := mload(add(864, mload(0x40)))
                        var_X_60, var_Y_80, var_ZZ_86, var_ZZZ_83 := usr$ecAddn2(var_X_60, var_Y_80, var_ZZ_86, var_ZZZ_83, mload(add(var_Q_53_mpos, 64)), mload(add(var_Q_53_mpos, 96)), mload(add(mload(0x40), 2080)))
                        usr$mstore4(mload(0x40), 1792, var_X_60, var_Y_80, var_ZZ_86, var_ZZZ_83)
                        var_X_60, var_Y_80, var_ZZ_86, var_ZZZ_83 := usr$ecAddn2(var_X_60, var_Y_80, var_ZZ_86, var_ZZZ_83, mload(add(var_Q_53_mpos, 0xc0)), mload(add(var_Q_53_mpos, 224)), mload(add(mload(0x40), 2080)))
                        usr$mstore4(mload(0x40), 1920, var_X_60, var_Y_80, var_ZZ_86, var_ZZZ_83)
                    }
                    var_ZZZ_83 := 0
                    for { }
                    iszero(var_ZZZ_83)
                    {
                        var_mask_63 := shr(1, var_mask_63)
                    }
                    {
                        var_ZZZ_83 := add(add(sub(1, iszero(and(var_scalar_u_55, var_mask_63))), shl(1, sub(1, iszero(and(shr(128, var_scalar_u_55), var_mask_63))))), add(shl(2, sub(1, iszero(and(var_scalar_v_57, var_mask_63)))), shl(3, sub(1, iszero(and(shr(128, var_scalar_v_57), var_mask_63))))))
                    }
                    var_X_60 := mload(add(mload(0x40), shl(7, var_ZZZ_83)))
                    var_Y_80 := mload(add(mload(0x40), add(32, shl(7, var_ZZZ_83))))
                    var_ZZ_86 := mload(add(mload(0x40), add(64, shl(7, var_ZZZ_83))))
                    var_ZZZ_83 := mload(add(mload(0x40), add(96, shl(7, var_ZZZ_83))))
                    let usr$Mem := mload(0x40)
                    let usr$_p := mload(add(usr$Mem, 2080))
                    for { }
                    gt(var_mask_63, 0)
                    {
                        var_mask_63 := shr(1, var_mask_63)
                    }
                    {
                        {
                            let usr$T1 := mulmod(2, var_Y_80, usr$_p)
                            let usr$T2 := mulmod(usr$T1, usr$T1, usr$_p)
                            let usr$T3 := mulmod(var_X_60, usr$T2, usr$_p)
                            usr$T1 := mulmod(usr$T1, usr$T2, usr$_p)
                            let usr$T4 := mulmod(mload(add(var_Q_53_mpos, 160)), mulmod(var_ZZ_86, var_ZZ_86, usr$_p), usr$_p)
                            usr$T4 := addmod(mulmod(3, mulmod(var_X_60, var_X_60, usr$_p), usr$_p), usr$T4, usr$_p)
                            var_ZZZ_83 := mulmod(usr$T1, var_ZZZ_83, usr$_p)
                            var_ZZ_86 := mulmod(usr$T2, var_ZZ_86, usr$_p)
                            var_X_60 := sub(usr$_p, 2)
                            var_X_60 := addmod(mulmod(usr$T4, usr$T4, usr$_p), mulmod(var_X_60, usr$T3, usr$_p), usr$_p)
                            usr$T2 := mulmod(usr$T4, addmod(var_X_60, sub(usr$_p, usr$T3), usr$_p), usr$_p)
                            var_Y_80 := addmod(mulmod(usr$T1, var_Y_80, usr$_p), usr$T2, usr$_p)
                        }
                        let usr$T1 := add(add(sub(1, iszero(and(var_scalar_u_55, var_mask_63))), shl(1, sub(1, iszero(and(shr(128, var_scalar_u_55), var_mask_63))))), add(shl(2, sub(1, iszero(and(var_scalar_v_57, var_mask_63)))), shl(3, sub(1, iszero(and(shr(128, var_scalar_v_57), var_mask_63))))))
                        if iszero(usr$T1)
                        {
                            var_Y_80 := sub(usr$_p, var_Y_80)
                            continue
                        }
                        usr$T1 := shl(7, usr$T1)
                        let usr$T4 := mload(add(usr$Mem, usr$T1))
                        mstore(add(usr$Mem, 2144), mload(add(usr$Mem, add(96, usr$T1))))
                        if iszero(var_ZZ_86)
                        {
                            var_X_60 := usr$T4
                            var_Y_80 := mload(add(usr$Mem, add(32, usr$T1)))
                            var_ZZ_86 := mload(add(usr$Mem, add(64, usr$T1)))
                            var_ZZZ_83 := mload(add(usr$Mem, add(96, usr$T1)))
                            continue
                        }
                        mstore(add(usr$Mem, 2112), addmod(mulmod(mload(add(usr$Mem, add(32, usr$T1))), var_ZZZ_83, usr$_p), mulmod(var_Y_80, mload(add(usr$Mem, 2144)), usr$_p), usr$_p))
                        usr$T1 := mload(add(usr$Mem, add(64, usr$T1)))
                        let usr$T2 := addmod(mulmod(usr$T4, var_ZZ_86, usr$_p), sub(usr$_p, mulmod(var_X_60, usr$T1, usr$_p)), usr$_p)
                        if iszero(mload(add(usr$Mem, 2112)))
                        {
                            if iszero(usr$T2)
                            {
                                usr$T1 := mulmod(sub(usr$_p, 2), var_Y_80, usr$_p)
                                usr$T2 := mulmod(usr$T1, usr$T1, usr$_p)
                                mstore(add(usr$Mem, 2112), mulmod(var_X_60, usr$T2, usr$_p))
                                usr$T1 := mulmod(usr$T1, usr$T2, usr$_p)
                                usr$T4 := mulmod(mload(add(var_Q_53_mpos, 160)), mulmod(var_ZZ_86, var_ZZ_86, usr$_p), usr$_p)
                                usr$T4 := addmod(mulmod(3, mulmod(var_X_60, var_X_60, usr$_p), usr$_p), usr$T4, usr$_p)
                                var_ZZZ_83 := mulmod(usr$T1, var_ZZZ_83, usr$_p)
                                var_ZZ_86 := mulmod(usr$T2, var_ZZ_86, usr$_p)
                                var_X_60 := addmod(mulmod(usr$T4, usr$T4, usr$_p), mulmod(sub(usr$_p, 2), mload(add(usr$Mem, 2112)), usr$_p), usr$_p)
                                usr$T2 := mulmod(usr$T4, addmod(mload(add(usr$Mem, 2112)), sub(usr$_p, var_X_60), usr$_p), usr$_p)
                                var_Y_80 := addmod(usr$T2, mulmod(usr$T1, var_Y_80, usr$_p), usr$_p)
                                continue
                            }
                        }
                        usr$T4 := mulmod(usr$T2, usr$T2, usr$_p)
                        usr$T2 := mulmod(usr$T4, usr$T2, usr$_p)
                        var_ZZ_86 := mulmod(mulmod(var_ZZ_86, usr$T4, usr$_p), usr$T1, usr$_p)
                        usr$T1 := mulmod(var_X_60, usr$T1, usr$_p)
                        var_ZZZ_83 := mulmod(mulmod(var_ZZZ_83, usr$T2, usr$_p), mload(add(usr$Mem, 2144)), usr$_p)
                        var_X_60 := addmod(addmod(mulmod(mload(add(usr$Mem, 2112)), mload(add(usr$Mem, 2112)), usr$_p), sub(usr$_p, usr$T2), usr$_p), mulmod(usr$T1, mulmod(sub(usr$_p, 2), usr$T4, usr$_p), usr$_p), usr$_p)
                        usr$T4 := mulmod(usr$T1, usr$T4, usr$_p)
                        var_Y_80 := addmod(mulmod(addmod(usr$T4, sub(usr$_p, var_X_60), usr$_p), mload(add(usr$Mem, 2112)), usr$_p), mulmod(mulmod(var_Y_80, mload(add(usr$Mem, 2144)), usr$_p), usr$T2, usr$_p), usr$_p)
                    }
                    mstore(0x40, 2176)
                    let usr$T := mload(0x40)
                    mstore(add(usr$T, 0x60), var_ZZ_86)
                    mstore(usr$T, 0x20)
                    mstore(add(usr$T, 0x20), 0x20)
                    mstore(add(usr$T, 0x40), 0x20)
                    mstore(add(usr$T, 0x80), sub(usr$_p, 2))
                    mstore(add(usr$T, 0xa0), usr$_p)
                    if iszero(staticcall(not(0), 0x05, usr$T, 0xc0, usr$T, 0x20))
                    {
                        mstore(0x40, 2047)
                        revert(0x40, 0x20)
                    }
                    var_X_60 := mulmod(var_X_60, mload(usr$T), usr$_p)
                }

            }
            /// @src 0:2011:14102  "contract Contract {..."

        }

        data ".metadata" hex"a2646970667358221220fabf0b08487ebc86e7a3d068a53dd1bf308d76dd68b5fb240112ed47c0c9263864736f6c634300081b0033"
    }

}


