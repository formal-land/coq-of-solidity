(* Generated test file *)
Require Import CoqOfSolidity.CoqOfSolidity.
Require Import simulations.CoqOfSolidity.

Require test.libsolidity.semanticTests.array.string_literal_assign_to_storage_bytes.C.

Definition constructor_code : M.t BlockUnit.t :=
  test.libsolidity.semanticTests.array.string_literal_assign_to_storage_bytes.C.C.code.

Definition deployed_code : M.t BlockUnit.t :=
  test.libsolidity.semanticTests.array.string_literal_assign_to_storage_bytes.C.C.deployed.code.

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

(* // s() -> 0x20, 3, "abc" *)
Module Step1.
  Definition environment : Environment.t :={|
    Environment.caller := 0x1212121212121212121212121212120000000012;
    Environment.callvalue := 0;
    Environment.calldata := Memory.hex_string_as_bytes "86b714e2";
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
    Memory.hex_string_as_bytes "000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000036162630000000000000000000000000000000000000000000000000000000000".

  Goal Test.extract_output result state true = inl expected_output.
  Proof.
    vm_compute.
    reflexivity.
  Qed.
End Step1.

(* // s1() -> 0x20, 4, "abcd" *)
Module Step2.
  Definition environment : Environment.t :={|
    Environment.caller := 0x1212121212121212121212121212120000000012;
    Environment.callvalue := 0;
    Environment.calldata := Memory.hex_string_as_bytes "6cc014de";
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
    Memory.hex_string_as_bytes "000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000046162636400000000000000000000000000000000000000000000000000000000".

  Goal Test.extract_output result state true = inl expected_output.
  Proof.
    vm_compute.
    reflexivity.
  Qed.
End Step2.

(* // f() -> *)
Module Step3.
  Definition environment : Environment.t :={|
    Environment.caller := 0x1212121212121212121212121212120000000012;
    Environment.callvalue := 0;
    Environment.calldata := Memory.hex_string_as_bytes "26121ff0";
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
    Memory.hex_string_as_bytes "".

  Goal Test.extract_output result state true = inl expected_output.
  Proof.
    vm_compute.
    reflexivity.
  Qed.
End Step3.

(* // s() -> 0x20, 4, "abcd" *)
Module Step4.
  Definition environment : Environment.t :={|
    Environment.caller := 0x1212121212121212121212121212120000000012;
    Environment.callvalue := 0;
    Environment.calldata := Memory.hex_string_as_bytes "86b714e2";
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
    Memory.hex_string_as_bytes "000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000046162636400000000000000000000000000000000000000000000000000000000".

  Goal Test.extract_output result state true = inl expected_output.
  Proof.
    vm_compute.
    reflexivity.
  Qed.
End Step4.

(* // s1() -> 0x20, 3, "abc" *)
Module Step5.
  Definition environment : Environment.t :={|
    Environment.caller := 0x1212121212121212121212121212120000000012;
    Environment.callvalue := 0;
    Environment.calldata := Memory.hex_string_as_bytes "6cc014de";
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
    Memory.hex_string_as_bytes "000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000036162630000000000000000000000000000000000000000000000000000000000".

  Goal Test.extract_output result state true = inl expected_output.
  Proof.
    vm_compute.
    reflexivity.
  Qed.
End Step5.

(* // g() -> *)
Module Step6.
  Definition environment : Environment.t :={|
    Environment.caller := 0x1212121212121212121212121212120000000012;
    Environment.callvalue := 0;
    Environment.calldata := Memory.hex_string_as_bytes "e2179b8e";
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

(* // s() -> 0x20, 3, "abc" *)
Module Step7.
  Definition environment : Environment.t :={|
    Environment.caller := 0x1212121212121212121212121212120000000012;
    Environment.callvalue := 0;
    Environment.calldata := Memory.hex_string_as_bytes "86b714e2";
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
    Memory.hex_string_as_bytes "000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000036162630000000000000000000000000000000000000000000000000000000000".

  Goal Test.extract_output result state true = inl expected_output.
  Proof.
    vm_compute.
    reflexivity.
  Qed.
End Step7.

(* // s1() -> 0x20, 4, "abcd" *)
Module Step8.
  Definition environment : Environment.t :={|
    Environment.caller := 0x1212121212121212121212121212120000000012;
    Environment.callvalue := 0;
    Environment.calldata := Memory.hex_string_as_bytes "6cc014de";
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
    Memory.hex_string_as_bytes "000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000046162636400000000000000000000000000000000000000000000000000000000".

  Goal Test.extract_output result state true = inl expected_output.
  Proof.
    vm_compute.
    reflexivity.
  Qed.
End Step8.
