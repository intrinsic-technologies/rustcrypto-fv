import K256.Proofs.Signing.Signature
import K256.Proofs.Signing.Composition
import K256.Proofs.Verify.Execution
import K256.Proofs.Common.OutputExecution
import K256.Proofs.Ecdh.LIR
import K256.Proofs.Ecdh.Execution
import K256.Proofs.Generate.Execution
import K256.Proofs.Generate.Generate
import K256.Proofs.Generate.LIR
import K256.Proofs.Generate.Serialize
import K256.Proofs.RejectLength
import K256.Proofs.ParseSignature
import K256.Proofs.Sec1.Affine.Complete
import K256.Proofs.Sec1.Affine.Compressed.Execution
import K256.Proofs.Sec1.Affine.Uncompressed.Decode
import K256.Proofs.Sec1.Execution
import K256.Proofs.Sec1.Parser.Execution
import K256.Proofs.Sec1.Serialize.Execution
import K256.Proofs.Sec1.Wrapper.Copy.Call
import K256.Proofs.Sec1.Wrapper.Execution
import K256.Proofs.Sec1.Wrapper.SerializerFrame

namespace K256.Statements

open K256.Spec K256.Spec.Program Prelude X86 Standards.SECG.ECC Standards.SECG.DomainParameters

theorem k256_signature_from_slice_writes_signature_or_rejects_bytes
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {bytes : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall signatureFromSlice initial [bytes]) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      match Ecdsa.signatureScalars bytes with
      | some (r, s) =>
        SuccessfulStatus final ∧
        MemoryWriteFrame initial final
          #v[outputRegion signatureFromSlice initial,
            Stack.region initial signatureFromSlice.minStackBytes] ∧
        readOutput signatureFromSlice initial final = .ok (Ecdsa.signatureBytes r s)
      | none =>
        FailureStatus final signatureErrorStatus ∧
        MemoryWriteFrame initial final
          #v[Stack.region initial signatureFromSlice.minStackBytes] := by
  by_cases hLength : bytes.size = 64
  · exact K256.Proofs.parseSignature hBindings hMachine hCall hLength
  · exact K256.Proofs.rejectLength hBindings hMachine hCall hLength

theorem k256_public_key_from_sec1_bytes_writes_public_key_or_rejects_encoding
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {bytes : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall publicKeyFromSec1Bytes initial [bytes]) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      match Secp256k1.decodePublicKey bytes with
      | some point =>
        SuccessfulStatus final ∧
        MemoryWriteFrame initial final
          #v[outputRegion publicKeyFromSec1Bytes initial,
            Stack.region initial publicKeyFromSec1Bytes.minStackBytes] ∧
        readOutput publicKeyFromSec1Bytes initial final =
          .ok (Points.encodePoint Secp256k1.domain false point)
      | none =>
        FailureStatus final ellipticCurveErrorStatus ∧
        MemoryWriteFrame initial final
          #v[Stack.region initial publicKeyFromSec1Bytes.minStackBytes] := by
  have affine := K256.Proofs.Sec1.Affine.decodeCall_of_decoders hCall
    (K256.Proofs.Sec1.Affine.Compressed.decoderCall K256.Proofs.Common.fnCode_subset_programImage)
    (K256.Proofs.Sec1.Affine.Uncompressed.decoderCall K256.Proofs.Common.fnCode_subset_programImage)
  obtain ⟨out, exec, post⟩ := K256.Proofs.Sec1.Wrapper.execution hCall
    (K256.Proofs.Sec1.Parser.parserCall_of_affine hCall affine)
    (K256.Proofs.Sec1.Wrapper.serializerCall hCall K256.Proofs.Sec1.Serialize.serializerExecution)
    (K256.Proofs.Sec1.Wrapper.Copy.copyCall hCall)
  exact K256.Proofs.Sec1.ofExecution hBindings hMachine hCall exec post

theorem k256_signing_key_generate_from_rng_writes_signing_key
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {random : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall signingKeyGenerateFromRng initial [random]) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[outputRegion signingKeyGenerateFromRng initial,
          Stack.region initial signingKeyGenerateFromRng.minStackBytes] ∧
      readOutput signingKeyGenerateFromRng initial final =
        .ok (Secp256k1.generatedSigningKey random) := by
  obtain ⟨out, exec, returned, bytes⟩ := K256.Proofs.Generate.execution_of_key
    (K256.Proofs.Generate.generate hCall) (K256.Proofs.Generate.serialize hCall)
  apply K256.Proofs.Generate.ofExecution hBindings hMachine hCall
    (program := K256.Proofs.Generate.LIR.lifted) (entry := .l102510) rfl
    (K256.Proofs.Generate.LIR.blocks hBindings.stringStride _ K256.Proofs.Common.fnCode_subset_programImage)
    _ exec returned bytes
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem k256_ecdh_diffie_hellman_writes_shared_secret
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {secret publicKey : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall ecdhDiffieHellman initial [secret, publicKey]) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[outputRegion ecdhDiffieHellman initial,
          Stack.region initial ecdhDiffieHellman.minStackBytes] ∧
      readOutput ecdhDiffieHellman initial final =
        .ok (Secp256k1.sharedSecret secret publicKey) := by
  obtain ⟨out, run, returned, contents⟩ := K256.Proofs.Ecdh.execution hCall
  apply K256.Proofs.Common.output_of_lifted_execution hBindings hMachine hCall
    (program := K256.Proofs.Ecdh.LIR.lifted) (entry := .l101660) rfl
    (K256.Proofs.Ecdh.LIR.blocks hBindings.stringStride _ K256.Proofs.Common.fnCode_subset_programImage)
    _ run returned contents
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem k256_verifying_key_verify_accepts_signature_or_rejects_signature
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {publicKey message signature : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall verifyingKeyVerify initial [publicKey, message, signature]) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      if Ecdsa.verifies publicKey message signature then
        SuccessfulStatus final ∧
        MemoryWriteFrame initial final #v[Stack.region initial verifyingKeyVerify.minStackBytes]
      else
        FailureStatus final signatureErrorStatus ∧
        MemoryWriteFrame initial final
          #v[Stack.region initial verifyingKeyVerify.minStackBytes] := by
  obtain ⟨program, entry, out, address, blocks, live, run, returned, status⟩ :=
    K256.Proofs.Verify.execution hBindings.stringStride hCall
  exact K256.Proofs.Common.status_of_lifted_execution hBindings hMachine hCall
    address blocks live run returned status

open Classical in
theorem k256_signing_key_try_sign_writes_low_s_signature_or_never_returns
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {secret message : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall signingKeyTrySign initial [secret, message]) :
    if ¬ Ecdsa.NonceSearchSucceeds secret message then NeverReturns initial else
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[outputRegion signingKeyTrySign initial,
          Stack.region initial signingKeyTrySign.minStackBytes] ∧
      readOutput signingKeyTrySign initial final = .ok (Ecdsa.signature secret message) := by
  classical
  have valid : (Keys.decodeSecret Secp256k1.domain secret).isSome = true :=
    hCall.inputsHoldValues.1
  obtain ⟨d, decoded⟩ := Option.isSome_iff_exists.mp valid
  obtain ⟨returns, diverges⟩ := K256.Proofs.Signing.Composition.execution
    hBindings hMachine hCall decoded
  split
  next absent =>
    apply diverges
    intro attempts
    cases found : Ecdsa.signatureWithin d message attempts with
    | none => rfl
    | some rs =>
      apply False.elim
      apply absent
      intro other key
      have eq := Option.some.inj (key.symm.trans decoded)
      exact eq ▸ ⟨attempts, Option.isSome_iff_exists.mpr ⟨rs, found⟩⟩
  next success =>
    obtain ⟨attempts, found⟩ := Classical.not_not.mp success d decoded
    obtain ⟨⟨r, s⟩, h⟩ := Option.isSome_iff_exists.mp found
    have bytes := @K256.Proofs.Signing.signature_of_found secret message d r s attempts decoded h
    exact Eq.mpr (congrArg (K256.Proofs.Signing.ReturnedSignature initial) bytes)
      (returns attempts r s h)

end K256.Statements
