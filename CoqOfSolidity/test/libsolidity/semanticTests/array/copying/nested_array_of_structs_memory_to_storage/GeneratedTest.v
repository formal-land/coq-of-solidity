(* Generated test file *)
Require Import CoqOfSolidity.CoqOfSolidity.
Require Import simulations.CoqOfSolidity.

Require test.libsolidity.semanticTests.array.copying.nested_array_of_structs_memory_to_storage.C.

Module Constructor.
  Definition environment : Environment.t :={|
    Environment.caller := 0x1212121212121212121212121212120000000012;
    Environment.callvalue := 0;
    Environment.calldata := [];
    Environment.codedata := Memory.hex_string_as_bytes "";
    Environment.address := None;
  |}.

  Definition code : M.t BlockUnit.t :=
    test.libsolidity.semanticTests.array.copying.nested_array_of_structs_memory_to_storage.C.C.code.

  Definition result_state :=
    eval 1000 environment code Stdlib.initial_state.

  Definition result := Eval vm_compute in fst result_state.
  Definition state := snd result_state.

  Goal Test.IsReturn result.
  Proof.
    unfold result.
    exact I.
  Qed.
End Constructor.

(* // test1((uint8[],uint8[2])[][]): 0x20, 2, 0x40, 0x0140, 1, 0x20, 0x60, 3, 7, 2, 1, 2, 2, 0x40, 0x0100, 0x60, 17, 19, 2, 11, 13, 0x60, 31, 37, 2, 23, 29 -> 0x20, 2, 0x40, 0x0140, 1, 0x20, 0x60, 3, 7, 2, 1, 2, 2, 0x40, 0x0100, 0x60, 17, 19, 2, 11, 13, 0x60, 31, 37, 2, 23, 29
// gas irOptimized: 309078 *)
Module Step1.
  Definition environment : Environment.t :={|
    Environment.caller := 0x1212121212121212121212121212120000000012;
    Environment.callvalue := 0;
    Environment.calldata := Memory.hex_string_as_bytes "21edf2920000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000140000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000060000000000000000000000000000000000000000000000000000000000000000300000000000000000000000000000000000000000000000000000000000000070000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000060000000000000000000000000000000000000000000000000000000000000001100000000000000000000000000000000000000000000000000000000000000130000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000b000000000000000000000000000000000000000000000000000000000000000d0000000000000000000000000000000000000000000000000000000000000060000000000000000000000000000000000000000000000000000000000000001f000000000000000000000000000000000000000000000000000000000000002500000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000017000000000000000000000000000000000000000000000000000000000000001d";
    Environment.codedata := [];
    Environment.address := Some 0xc06afe3a8444fc0004668591e8306bfb9968e79e;
  |}.

  Definition code : M.t BlockUnit.t :=
    test.libsolidity.semanticTests.array.copying.nested_array_of_structs_memory_to_storage.C.C.deployed.code.

  Definition initial_state : State.t :=
    Stdlib.initial_state <|
      State.storage := Constructor.state.(State.storage)
    |>.

  Definition result_state :=
    eval 1000 environment code initial_state.

  Definition result := Eval vm_compute in fst result_state.
  Definition state := snd result_state.

  Definition expected_output : list Z :=
    Memory.hex_string_as_bytes "0000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000140000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000060000000000000000000000000000000000000000000000000000000000000000300000000000000000000000000000000000000000000000000000000000000070000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000060000000000000000000000000000000000000000000000000000000000000001100000000000000000000000000000000000000000000000000000000000000130000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000b000000000000000000000000000000000000000000000000000000000000000d0000000000000000000000000000000000000000000000000000000000000060000000000000000000000000000000000000000000000000000000000000001f000000000000000000000000000000000000000000000000000000000000002500000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000017000000000000000000000000000000000000000000000000000000000000001d".

  Goal Test.extract_output result state = Some expected_output.
  Proof.
    unfold result.
    vm_compute.
    reflexivity.
  Qed.
End Step1.

(* // test2((uint8[],uint8[2])[][1]): 0x20, 0x20, 1, 0x20, 0x60, 17, 19, 2, 11, 13 -> 0x20, 0x20, 1, 0x20, 0x60, 17, 19, 2, 11, 13
// gas irOptimized: 118314 *)
Module Step2.
  Definition environment : Environment.t :={|
    Environment.caller := 0x1212121212121212121212121212120000000012;
    Environment.callvalue := 0;
    Environment.calldata := Memory.hex_string_as_bytes "45cc4f9300000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000060000000000000000000000000000000000000000000000000000000000000001100000000000000000000000000000000000000000000000000000000000000130000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000b000000000000000000000000000000000000000000000000000000000000000d";
    Environment.codedata := [];
    Environment.address := Some 0xc06afe3a8444fc0004668591e8306bfb9968e79e;
  |}.

  Definition code : M.t BlockUnit.t :=
    test.libsolidity.semanticTests.array.copying.nested_array_of_structs_memory_to_storage.C.C.deployed.code.

  Definition initial_state : State.t :=
    Stdlib.initial_state <|
      State.storage := Step1.state.(State.storage)
    |>.

  Definition result_state :=
    eval 1000 environment code initial_state.

  Definition result := Eval vm_compute in fst result_state.
  Definition state := snd result_state.

  Definition expected_output : list Z :=
    Memory.hex_string_as_bytes "00000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000060000000000000000000000000000000000000000000000000000000000000001100000000000000000000000000000000000000000000000000000000000000130000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000b000000000000000000000000000000000000000000000000000000000000000d".

  Goal Test.extract_output result state = Some expected_output.
  Proof.
    unfold result.
    reflexivity.
  Qed.
End Step2.

(* // test3((uint8[],uint8[2])[1][]): 0x20, 2, 0x40, 0x0120, 0x20, 0x60, 3, 7, 2, 1, 2, 0x20, 0x60, 17, 19, 2, 11, 13 -> 0x20, 2, 0x40, 0x0120, 0x20, 0x60, 3, 7, 2, 1, 2, 0x20, 0x60, 17, 19, 2, 11, 13
// gas irOptimized: 191051 *)
Module Step3.
  Definition environment : Environment.t :={|
    Environment.caller := 0x1212121212121212121212121212120000000012;
    Environment.callvalue := 0;
    Environment.calldata := Memory.hex_string_as_bytes "30d6890d0000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000120000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000600000000000000000000000000000000000000000000000000000000000000003000000000000000000000000000000000000000000000000000000000000000700000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000060000000000000000000000000000000000000000000000000000000000000001100000000000000000000000000000000000000000000000000000000000000130000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000b000000000000000000000000000000000000000000000000000000000000000d";
    Environment.codedata := [];
    Environment.address := Some 0xc06afe3a8444fc0004668591e8306bfb9968e79e;
  |}.

  Definition code : M.t BlockUnit.t :=
    test.libsolidity.semanticTests.array.copying.nested_array_of_structs_memory_to_storage.C.C.deployed.code.

  Definition initial_state : State.t :=
    Stdlib.initial_state <|
      State.storage := Step2.state.(State.storage)
    |>.

  Definition result_state :=
    eval 1000 environment code initial_state.

  Definition result := Eval vm_compute in fst result_state.
  Definition state := snd result_state.

  Definition expected_output : list Z :=
    Memory.hex_string_as_bytes "0000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000120000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000600000000000000000000000000000000000000000000000000000000000000003000000000000000000000000000000000000000000000000000000000000000700000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000060000000000000000000000000000000000000000000000000000000000000001100000000000000000000000000000000000000000000000000000000000000130000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000b000000000000000000000000000000000000000000000000000000000000000d".

  Goal Test.extract_output result state = Some expected_output.
  Proof.
    unfold result.
    reflexivity.
  Qed.
End Step3.
