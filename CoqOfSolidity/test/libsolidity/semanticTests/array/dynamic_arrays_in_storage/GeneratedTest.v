(* Generated test file *)
Require Import CoqOfSolidity.CoqOfSolidity.
Require Import simulations.CoqOfSolidity.

Require test.libsolidity.semanticTests.array.dynamic_arrays_in_storage.c.

Definition constructor_code : M.t BlockUnit.t :=
  test.libsolidity.semanticTests.array.dynamic_arrays_in_storage.c.c.code.

Definition deployed_code : M.t BlockUnit.t :=
  test.libsolidity.semanticTests.array.dynamic_arrays_in_storage.c.c.deployed.code.

Module Constructor.
  Definition environment : Environment.t :={|
    Environment.caller := 0x1212121212121212121212121212120000000012;
    Environment.callvalue := 0;
    Environment.calldata := [];
    Environment.codedata := Memory.hex_string_as_bytes "";
    Environment.address := HexString.of_Z 0xc06afe3a8444fc0004668591e8306bfb9968e79e;
  |}.

  Definition initial_state : State.t :=
    let address := environment.(Environment.address) in
    let account := {|
      Account.balance := environment.(Environment.callvalue);
      Account.code := deployed_code;
      Account.storage := Memory.init;
    |} in
    Stdlib.initial_state <|
      State.accounts := [(address, account)]
    |>.

  Definition result_state :=
    eval_with_revert 1000 environment constructor_code initial_state.

  Definition result := fst result_state.
  Definition state := snd result_state.

  Goal Test.is_return result = None.
  Proof.
    vm_compute.
    reflexivity.
  Qed.
End Constructor.

(* // getLengths() -> 0, 0 *)
Module Step1.
  Definition environment : Environment.t :={|
    Environment.caller := 0x1212121212121212121212121212120000000012;
    Environment.callvalue := 0;
    Environment.calldata := Memory.hex_string_as_bytes "800bd5c8";
    Environment.codedata := [];
    Environment.address := HexString.of_Z 0xc06afe3a8444fc0004668591e8306bfb9968e79e;
  |}.

  Definition initial_state : State.t :=
    Stdlib.initial_state <|
      State.accounts := Constructor.state.(State.accounts)
    |>.

  Definition result_state :=
    eval_with_revert 1000 environment deployed_code initial_state.

  Definition result := fst result_state.
  Definition state := snd result_state.

  Definition expected_output : list Z :=
    Memory.hex_string_as_bytes "00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000".

  Goal Test.extract_output result state true = inl expected_output.
  Proof.
    vm_compute.
    reflexivity.
  Qed.
End Step1.

(* // setLengths(uint256,uint256): 48, 49 ->
// gas irOptimized: 112674
// gas legacy: 108273
// gas legacyOptimized: 100269 *)
Module Step2.
  Definition environment : Environment.t :={|
    Environment.caller := 0x1212121212121212121212121212120000000012;
    Environment.callvalue := 0;
    Environment.calldata := Memory.hex_string_as_bytes "23fef0c000000000000000000000000000000000000000000000000000000000000000300000000000000000000000000000000000000000000000000000000000000031";
    Environment.codedata := [];
    Environment.address := HexString.of_Z 0xc06afe3a8444fc0004668591e8306bfb9968e79e;
  |}.

  Definition initial_state : State.t :=
    Stdlib.initial_state <|
      State.accounts := Step1.state.(State.accounts)
    |>.

  Definition result_state :=
    eval_with_revert 1000 environment deployed_code initial_state.

  Definition result := fst result_state.
  Definition state := snd result_state.

  Definition expected_output : list Z :=
    Memory.hex_string_as_bytes "".

  Goal Test.extract_output result state true = inl expected_output.
  Proof.
    vm_compute.
    reflexivity.
  Qed.
End Step2.

(* // getLengths() -> 48, 49 *)
Module Step3.
  Definition environment : Environment.t :={|
    Environment.caller := 0x1212121212121212121212121212120000000012;
    Environment.callvalue := 0;
    Environment.calldata := Memory.hex_string_as_bytes "800bd5c8";
    Environment.codedata := [];
    Environment.address := HexString.of_Z 0xc06afe3a8444fc0004668591e8306bfb9968e79e;
  |}.

  Definition initial_state : State.t :=
    Stdlib.initial_state <|
      State.accounts := Step2.state.(State.accounts)
    |>.

  Definition result_state :=
    eval_with_revert 1000 environment deployed_code initial_state.

  Definition result := fst result_state.
  Definition state := snd result_state.

  Definition expected_output : list Z :=
    Memory.hex_string_as_bytes "00000000000000000000000000000000000000000000000000000000000000300000000000000000000000000000000000000000000000000000000000000031".

  Goal Test.extract_output result state true = inl expected_output.
  Proof.
    vm_compute.
    reflexivity.
  Qed.
End Step3.

(* // setIDStatic(uint256): 11 -> *)
Module Step4.
  Definition environment : Environment.t :={|
    Environment.caller := 0x1212121212121212121212121212120000000012;
    Environment.callvalue := 0;
    Environment.calldata := Memory.hex_string_as_bytes "b55e49c0000000000000000000000000000000000000000000000000000000000000000b";
    Environment.codedata := [];
    Environment.address := HexString.of_Z 0xc06afe3a8444fc0004668591e8306bfb9968e79e;
  |}.

  Definition initial_state : State.t :=
    Stdlib.initial_state <|
      State.accounts := Step3.state.(State.accounts)
    |>.

  Definition result_state :=
    eval_with_revert 1000 environment deployed_code initial_state.

  Definition result := fst result_state.
  Definition state := snd result_state.

  Definition expected_output : list Z :=
    Memory.hex_string_as_bytes "".

  Goal Test.extract_output result state true = inl expected_output.
  Proof.
    vm_compute.
    reflexivity.
  Qed.
End Step4.

(* // getID(uint256): 2 -> 11 *)
Module Step5.
  Definition environment : Environment.t :={|
    Environment.caller := 0x1212121212121212121212121212120000000012;
    Environment.callvalue := 0;
    Environment.calldata := Memory.hex_string_as_bytes "0d18e43c0000000000000000000000000000000000000000000000000000000000000002";
    Environment.codedata := [];
    Environment.address := HexString.of_Z 0xc06afe3a8444fc0004668591e8306bfb9968e79e;
  |}.

  Definition initial_state : State.t :=
    Stdlib.initial_state <|
      State.accounts := Step4.state.(State.accounts)
    |>.

  Definition result_state :=
    eval_with_revert 1000 environment deployed_code initial_state.

  Definition result := fst result_state.
  Definition state := snd result_state.

  Definition expected_output : list Z :=
    Memory.hex_string_as_bytes "000000000000000000000000000000000000000000000000000000000000000b".

  Goal Test.extract_output result state true = inl expected_output.
  Proof.
    vm_compute.
    reflexivity.
  Qed.
End Step5.

(* // setID(uint256,uint256): 7, 8 -> *)
Module Step6.
  Definition environment : Environment.t :={|
    Environment.caller := 0x1212121212121212121212121212120000000012;
    Environment.callvalue := 0;
    Environment.calldata := Memory.hex_string_as_bytes "cc959c7300000000000000000000000000000000000000000000000000000000000000070000000000000000000000000000000000000000000000000000000000000008";
    Environment.codedata := [];
    Environment.address := HexString.of_Z 0xc06afe3a8444fc0004668591e8306bfb9968e79e;
  |}.

  Definition initial_state : State.t :=
    Stdlib.initial_state <|
      State.accounts := Step5.state.(State.accounts)
    |>.

  Definition result_state :=
    eval_with_revert 1000 environment deployed_code initial_state.

  Definition result := fst result_state.
  Definition state := snd result_state.

  Definition expected_output : list Z :=
    Memory.hex_string_as_bytes "".

  Goal Test.extract_output result state true = inl expected_output.
  Proof.
    vm_compute.
    reflexivity.
  Qed.
End Step6.

(* // getID(uint256): 7 -> 8 *)
Module Step7.
  Definition environment : Environment.t :={|
    Environment.caller := 0x1212121212121212121212121212120000000012;
    Environment.callvalue := 0;
    Environment.calldata := Memory.hex_string_as_bytes "0d18e43c0000000000000000000000000000000000000000000000000000000000000007";
    Environment.codedata := [];
    Environment.address := HexString.of_Z 0xc06afe3a8444fc0004668591e8306bfb9968e79e;
  |}.

  Definition initial_state : State.t :=
    Stdlib.initial_state <|
      State.accounts := Step6.state.(State.accounts)
    |>.

  Definition result_state :=
    eval_with_revert 1000 environment deployed_code initial_state.

  Definition result := fst result_state.
  Definition state := snd result_state.

  Definition expected_output : list Z :=
    Memory.hex_string_as_bytes "0000000000000000000000000000000000000000000000000000000000000008".

  Goal Test.extract_output result state true = inl expected_output.
  Proof.
    vm_compute.
    reflexivity.
  Qed.
End Step7.

(* // setData(uint256,uint256,uint256): 7, 8, 9 -> *)
Module Step8.
  Definition environment : Environment.t :={|
    Environment.caller := 0x1212121212121212121212121212120000000012;
    Environment.callvalue := 0;
    Environment.calldata := Memory.hex_string_as_bytes "2909f638000000000000000000000000000000000000000000000000000000000000000700000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000009";
    Environment.codedata := [];
    Environment.address := HexString.of_Z 0xc06afe3a8444fc0004668591e8306bfb9968e79e;
  |}.

  Definition initial_state : State.t :=
    Stdlib.initial_state <|
      State.accounts := Step7.state.(State.accounts)
    |>.

  Definition result_state :=
    eval_with_revert 1000 environment deployed_code initial_state.

  Definition result := fst result_state.
  Definition state := snd result_state.

  Definition expected_output : list Z :=
    Memory.hex_string_as_bytes "".

  Goal Test.extract_output result state true = inl expected_output.
  Proof.
    vm_compute.
    reflexivity.
  Qed.
End Step8.

(* // setData(uint256,uint256,uint256): 8, 10, 11 -> *)
Module Step9.
  Definition environment : Environment.t :={|
    Environment.caller := 0x1212121212121212121212121212120000000012;
    Environment.callvalue := 0;
    Environment.calldata := Memory.hex_string_as_bytes "2909f6380000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000a000000000000000000000000000000000000000000000000000000000000000b";
    Environment.codedata := [];
    Environment.address := HexString.of_Z 0xc06afe3a8444fc0004668591e8306bfb9968e79e;
  |}.

  Definition initial_state : State.t :=
    Stdlib.initial_state <|
      State.accounts := Step8.state.(State.accounts)
    |>.

  Definition result_state :=
    eval_with_revert 1000 environment deployed_code initial_state.

  Definition result := fst result_state.
  Definition state := snd result_state.

  Definition expected_output : list Z :=
    Memory.hex_string_as_bytes "".

  Goal Test.extract_output result state true = inl expected_output.
  Proof.
    vm_compute.
    reflexivity.
  Qed.
End Step9.

(* // getData(uint256): 7 -> 8, 9 *)
Module Step10.
  Definition environment : Environment.t :={|
    Environment.caller := 0x1212121212121212121212121212120000000012;
    Environment.callvalue := 0;
    Environment.calldata := Memory.hex_string_as_bytes "0178fe3f0000000000000000000000000000000000000000000000000000000000000007";
    Environment.codedata := [];
    Environment.address := HexString.of_Z 0xc06afe3a8444fc0004668591e8306bfb9968e79e;
  |}.

  Definition initial_state : State.t :=
    Stdlib.initial_state <|
      State.accounts := Step9.state.(State.accounts)
    |>.

  Definition result_state :=
    eval_with_revert 1000 environment deployed_code initial_state.

  Definition result := fst result_state.
  Definition state := snd result_state.

  Definition expected_output : list Z :=
    Memory.hex_string_as_bytes "00000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000009".

  Goal Test.extract_output result state true = inl expected_output.
  Proof.
    vm_compute.
    reflexivity.
  Qed.
End Step10.

(* // getData(uint256): 8 -> 10, 11 *)
Module Step11.
  Definition environment : Environment.t :={|
    Environment.caller := 0x1212121212121212121212121212120000000012;
    Environment.callvalue := 0;
    Environment.calldata := Memory.hex_string_as_bytes "0178fe3f0000000000000000000000000000000000000000000000000000000000000008";
    Environment.codedata := [];
    Environment.address := HexString.of_Z 0xc06afe3a8444fc0004668591e8306bfb9968e79e;
  |}.

  Definition initial_state : State.t :=
    Stdlib.initial_state <|
      State.accounts := Step10.state.(State.accounts)
    |>.

  Definition result_state :=
    eval_with_revert 1000 environment deployed_code initial_state.

  Definition result := fst result_state.
  Definition state := snd result_state.

  Definition expected_output : list Z :=
    Memory.hex_string_as_bytes "000000000000000000000000000000000000000000000000000000000000000a000000000000000000000000000000000000000000000000000000000000000b".

  Goal Test.extract_output result state true = inl expected_output.
  Proof.
    vm_compute.
    reflexivity.
  Qed.
End Step11.
