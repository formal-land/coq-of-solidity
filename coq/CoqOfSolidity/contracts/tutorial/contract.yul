IR:

/// @use-src 0:"CoqOfSolidity/contracts/simple/contract.sol"
object "Contract_16" {
    code {
        /// @src 0:66:186  "contract Contract {..."
        mstore(64, memoryguard(128))
        if callvalue() { revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb() }

        constructor_Contract_16()

        let _1 := allocate_unbounded()
        codecopy(_1, dataoffset("Contract_16_deployed"), datasize("Contract_16_deployed"))

        return(_1, datasize("Contract_16_deployed"))

        function allocate_unbounded() -> memPtr {
            memPtr := mload(64)
        }

        function revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb() {
            revert(0, 0)
        }

        /// @src 0:66:186  "contract Contract {..."
        function constructor_Contract_16() {

            /// @src 0:66:186  "contract Contract {..."

        }
        /// @src 0:66:186  "contract Contract {..."

    }
    /// @use-src 0:"CoqOfSolidity/contracts/simple/contract.sol"
    object "Contract_16_deployed" {
        code {
            /// @src 0:66:186  "contract Contract {..."
            mstore(64, memoryguard(128))

            if iszero(lt(calldatasize(), 4))
            {
                let selector := shift_right_224_unsigned(calldataload(0))
                switch selector

                case 0x771602f7
                {
                    // add(uint256,uint256)

                    external_fun_add_15()
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

            function abi_decode_tuple_t_uint256t_uint256(headStart, dataEnd) -> value0, value1 {
                if slt(sub(dataEnd, headStart), 64) { revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b() }

                {

                    let offset := 0

                    value0 := abi_decode_t_uint256(add(headStart, offset), dataEnd)
                }

                {

                    let offset := 32

                    value1 := abi_decode_t_uint256(add(headStart, offset), dataEnd)
                }

            }

            function abi_encode_t_uint256_to_t_uint256_fromStack(value, pos) {
                mstore(pos, cleanup_t_uint256(value))
            }

            function abi_encode_tuple_t_uint256__to_t_uint256__fromStack(headStart , value0) -> tail {
                tail := add(headStart, 32)

                abi_encode_t_uint256_to_t_uint256_fromStack(value0,  add(headStart, 0))

            }

            function external_fun_add_15() {

                if callvalue() { revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb() }
                let param_0, param_1 :=  abi_decode_tuple_t_uint256t_uint256(4, calldatasize())
                let ret_0 :=  fun_add_15(param_0, param_1)
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

            function panic_error_0x11() {
                mstore(0, 35408467139433450592217433187231851964531694900788300625387963629091585785856)
                mstore(4, 0x11)
                revert(0, 0x24)
            }

            function checked_add_t_uint256(x, y) -> sum {
                x := cleanup_t_uint256(x)
                y := cleanup_t_uint256(y)
                sum := add(x, y)

                if gt(x, sum) { panic_error_0x11() }

            }

            /// @ast-id 15
            /// @src 0:90:184  "function add(uint256 a, uint256 b) public pure returns (uint256) {..."
            function fun_add_15(var_a_3, var_b_5) -> var__8 {
                /// @src 0:146:153  "uint256"
                let zero_t_uint256_1 := zero_value_for_split_t_uint256()
                var__8 := zero_t_uint256_1

                /// @src 0:172:173  "a"
                let _2 := var_a_3
                let expr_10 := _2
                /// @src 0:176:177  "b"
                let _3 := var_b_5
                let expr_11 := _3
                /// @src 0:172:177  "a + b"
                let expr_12 := checked_add_t_uint256(expr_10, expr_11)

                /// @src 0:165:177  "return a + b"
                var__8 := expr_12
                leave

            }
            /// @src 0:66:186  "contract Contract {..."

        }

        data ".metadata" hex"a2646970667358221220df7b226d7d032609bf8ff6433ec4f6ef7cc818ab0e5ad2edcdc28e1f3095899564736f6c634300081d0033"
    }

}


