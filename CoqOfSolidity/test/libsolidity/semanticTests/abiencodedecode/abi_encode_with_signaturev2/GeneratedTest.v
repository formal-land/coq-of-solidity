(* Generated test file *)
Require Import CoqOfSolidity.CoqOfSolidity.
Require Import simulations.CoqOfSolidity.

Require test.libsolidity.semanticTests.abiencodedecode.abi_encode_with_signaturev2.C.

Module Constructor.
  Definition environment : Environment.t :={|
    Environment.caller := 0x1212121212121212121212121212120000000012;
    Environment.callvalue := 0;
    Environment.calldata := Memory.hex_string_as_bytes "";
  |}.

  Definition code : M.t BlockUnit.t :=
    test.libsolidity.semanticTests.abiencodedecode.abi_encode_with_signaturev2.C.C.code.

  Definition state : State.t :=
    snd (eval 1000 environment code Stdlib.initial_state).
End Constructor.

(* // f0() -> 0x20, 4, -34435155370463444793260793355178157075203752403645521721995013737368954863616 *)
Module Step1.
  Definition environment : Environment.t :={|
    Environment.caller := 0x1212121212121212121212121212120000000012;
    Environment.callvalue := 0;
    Environment.calldata := Memory.hex_string_as_bytes "a5850475";
  |}.

  Definition code : M.t BlockUnit.t :=
    test.libsolidity.semanticTests.abiencodedecode.abi_encode_with_signaturev2.C.C.deployed.code.

  Definition initial_state : State.t :=
    Stdlib.initial_state <|
      State.storage := Constructor.state.(State.storage)
    |>.

  Definition result_state :=
    eval 1000 environment code initial_state.

  Definition result := fst result_state.
  Definition state := snd result_state.

  Definition expected_output : list Z :=
    Memory.hex_string_as_bytes "00000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000004b3de648b00000000000000000000000000000000000000000000000000000000".

  Goal extract_output result state = Some expected_output.
  Proof.
    reflexivity.
  Qed.
End Step1.

(* // f1() -> 0x20, 0x64, -34435155370463444793260793355178157075203752403645521721995013737368954863616, 862718293348820473429344482784628181556388621521298319395315527974912, 91135606241822717681769169345594720818313984248279388438121731325952, 0 *)
Module Step2.
  Definition environment : Environment.t :={|
    Environment.caller := 0x1212121212121212121212121212120000000012;
    Environment.callvalue := 0;
    Environment.calldata := Memory.hex_string_as_bytes "c27fc305";
  |}.

  Definition code : M.t BlockUnit.t :=
    test.libsolidity.semanticTests.abiencodedecode.abi_encode_with_signaturev2.C.C.deployed.code.

  Definition initial_state : State.t :=
    Stdlib.initial_state <|
      State.storage := Step1.state.(State.storage)
    |>.

  Definition result_state :=
    eval 1000 environment code initial_state.

  Definition result := fst result_state.
  Definition state := snd result_state.

  Definition expected_output : list Z :=
    Memory.hex_string_as_bytes "00000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000064b3de648b00000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000003616263000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000".

  Goal extract_output result state = Some expected_output.
  Proof.
    reflexivity.
  Qed.
End Step2.

(* // f1s() -> 0x20, 0x64, -34435155370463444793260793355178157075203752403645521721995013737368954863616, 862718293348820473429344482784628181556388621521298319395315527974912, 91135606241822717681769169345594720818313984248279388438121731325952, 0 *)
Module Step3.
  Definition environment : Environment.t :={|
    Environment.caller := 0x1212121212121212121212121212120000000012;
    Environment.callvalue := 0;
    Environment.calldata := Memory.hex_string_as_bytes "5e0740ed";
  |}.

  Definition code : M.t BlockUnit.t :=
    test.libsolidity.semanticTests.abiencodedecode.abi_encode_with_signaturev2.C.C.deployed.code.

  Definition initial_state : State.t :=
    Stdlib.initial_state <|
      State.storage := Step2.state.(State.storage)
    |>.

  Definition result_state :=
    eval 1000 environment code initial_state.

  Definition result := fst result_state.
  Definition state := snd result_state.

  Definition expected_output : list Z :=
    Memory.hex_string_as_bytes "00000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000064b3de648b00000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000003616263000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000".

  Goal extract_output result state = Some expected_output.
  Proof.
    reflexivity.
  Qed.
End Step3.

(* // f2() -> 0x40, 0x0140, 0xc4, -10047825972976160827854069633043429618646681939320956771263895477211642200064, 862718293348820473429344482784628181556388621521298319395315527974912, 0x04ffffffffffffffffffffffffffffffffffffffffffffffffffffffff, -1, -26959946667150639794667015087019630673637144422540572481103610249217, -53919893334301279589334030174039261347274288845081144962207220498433, -107839786668602559178668060348078522694548577690162289924414440996864, 2, 0, 0 *)
Module Step4.
  Definition environment : Environment.t :={|
    Environment.caller := 0x1212121212121212121212121212120000000012;
    Environment.callvalue := 0;
    Environment.calldata := Memory.hex_string_as_bytes "9942ec6f";
  |}.

  Definition code : M.t BlockUnit.t :=
    test.libsolidity.semanticTests.abiencodedecode.abi_encode_with_signaturev2.C.C.deployed.code.

  Definition initial_state : State.t :=
    Stdlib.initial_state <|
      State.storage := Step3.state.(State.storage)
    |>.

  Definition result_state :=
    eval 1000 environment code initial_state.

  Definition result := fst result_state.
  Definition state := snd result_state.

  Definition expected_output : list Z :=
    Memory.hex_string_as_bytes "0000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000014000000000000000000000000000000000000000000000000000000000000000c4e9c921cd00000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000004fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000".

  Goal extract_output result state = Some expected_output.
  Proof.
    reflexivity.
  Qed.
End Step4.

(* // f4() -> 0x20, 292, 0x7c793002ffffffffffffffffffffffffffffffffffffffffffffffffffffffff, -26959946667150639794667015087019630673637144422540572481103610249216, 2588154880046461420288033448353884544669165864563894958185946583924736, 80879840001451919384001045261058892020911433267621717443310830747648, 514631493222945105325971421573240365883976325135760395164659172419450175488, 2588154880046461420288033448353884544669165864563894958185946583924736, 125633351468921981443148290305511478939149093009039067761942823761346560, 0x264c6f72656d20697073756d20646f6c6f722073697420657468657265, 53113508339655873314659021564971517366334151400493876485713881232784043802624, 0 *)
Module Step5.
  Definition environment : Environment.t :={|
    Environment.caller := 0x1212121212121212121212121212120000000012;
    Environment.callvalue := 0;
    Environment.calldata := Memory.hex_string_as_bytes "c3f90202";
  |}.

  Definition code : M.t BlockUnit.t :=
    test.libsolidity.semanticTests.abiencodedecode.abi_encode_with_signaturev2.C.C.deployed.code.

  Definition initial_state : State.t :=
    Stdlib.initial_state <|
      State.storage := Step4.state.(State.storage)
    |>.

  Definition result_state :=
    eval 1000 environment code initial_state.

  Definition result := fst result_state.
  Definition state := snd result_state.

  Definition expected_output : list Z :=
    Memory.hex_string_as_bytes "000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000001247c793002ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000060000000000000000000000000000000000000000000000000000000000000000300000000000000000000000000000000000000000000000000000000012345670000000000000000000000000000000000000000000000000000000000000060000000000000000000000000000000000000000000000000000000000000123400000000000000000000000000000000000000000000000000000000000000264c6f72656d20697073756d20646f6c6f722073697420657468657265756d2e2e2e2e2e2e2e2e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000".

  Goal extract_output result state = Some expected_output.
  Proof.
    reflexivity.
  Qed.
End Step5.
