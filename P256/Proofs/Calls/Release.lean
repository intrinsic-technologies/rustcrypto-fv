import P256.Spec
import P256.Proofs.EcdhWrapper
import P256.Proofs.Sec1
import P256.Proofs.Verifying
import P256.Proofs.Generate
import P256.Proofs.Signing
import P256.Proofs.SignatureFromSlice.Wrapper.Correct
import P256.Proofs.SignatureFromDer.Fixed.Correct

set_option autoImplicit false

namespace P256.Statements

open P256.Spec Prelude X86 P256.Spec.Program.Routines

theorem p256_public_key_from_sec1_bytes_writes_public_key_or_rejects_encoding
    [bindings : Machine.Bindings] {initial : Machine.RamState}
    {bytes : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall publicKeyFromSec1Bytes initial [bytes]) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      match Keys.publicKeyFromSec1 #[bytes] with
      | some result =>
        SuccessfulStatus final ∧
        MemoryWriteFrame initial final
          #v[outputRegion publicKeyFromSec1Bytes initial [bytes], allocatorStateRegion,
            randomSourceRegion, callStack publicKeyFromSec1Bytes initial] ∧
        readOutput publicKeyFromSec1Bytes initial final = .ok result
      | none =>
        FailureStatus final invalidPublicKeyStatus ∧
        MemoryWriteFrame initial final
          #v[allocatorStateRegion, randomSourceRegion,
            callStack publicKeyFromSec1Bytes initial] := by
  exact P256.Proofs.Sec1.Wrapper.correct_of_decoder
    (fun _ _ _ pre ↦ P256.Proofs.Sec1.Decode.decode_correct pre)
    hBindings hMachine hCall

open Classical in

theorem p256_signing_key_try_sign_writes_signature_or_never_returns
    [bindings : Machine.Bindings] {initial : Machine.RamState}
    {signingKey msg : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall signingKeyTrySign initial [signingKey, msg]) :
    if Ecdsa.NeverSigns #[signingKey, msg] then NeverReturns initial else
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[outputRegion signingKeyTrySign initial [signingKey, msg], allocatorStateRegion,
          randomSourceRegion, callStack signingKeyTrySign initial] ∧
      readOutput signingKeyTrySign initial final = .ok (Ecdsa.signMessage #[signingKey, msg]) := by
  exact P256.Proofs.Signing.signing_correct hBindings hMachine hCall

theorem p256_verifying_key_verify_accepts_signature_or_rejects_signature
    [bindings : Machine.Bindings] {initial : Machine.RamState}
    {verifyingKey signature msg : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall verifyingKeyVerify initial [verifyingKey, signature, msg]) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      match Ecdsa.verifyMessage #[verifyingKey, signature, msg] with
      | some result =>
        SuccessfulStatus final ∧
        MemoryWriteFrame initial final
          #v[outputRegion verifyingKeyVerify initial [verifyingKey, signature, msg],
            allocatorStateRegion, randomSourceRegion, callStack verifyingKeyVerify initial] ∧
        readOutput verifyingKeyVerify initial final = .ok result
      | none =>
        FailureStatus final invalidSignatureStatus ∧
        MemoryWriteFrame initial final
          #v[allocatorStateRegion, randomSourceRegion, callStack verifyingKeyVerify initial] := by
  exact P256.Proofs.Verifying.Wrapper.correct_of_decoder_message
    (fun _ _ _ pre ↦ P256.Proofs.Sec1.Decode.decode_correct pre)
    P256.Proofs.Verifying.Message.correct hBindings hMachine hCall

theorem p256_signature_from_slice_writes_signature_or_rejects_bytes
    [bindings : Machine.Bindings] {initial : Machine.RamState}
    {bytes : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall signatureFromSlice initial [bytes]) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      match Ecdsa.signatureFromSlice #[bytes] with
      | some result =>
        SuccessfulStatus final ∧
        MemoryWriteFrame initial final
          #v[outputRegion signatureFromSlice initial [bytes], allocatorStateRegion,
            randomSourceRegion, callStack signatureFromSlice initial] ∧
        readOutput signatureFromSlice initial final = .ok result
      | none =>
        FailureStatus final invalidSignatureBytesStatus ∧
        MemoryWriteFrame initial final
          #v[allocatorStateRegion, randomSourceRegion, callStack signatureFromSlice initial] := by
  exact P256.Proofs.SignatureFromSlice.signature_from_slice_of_decoder
    P256.Proofs.SignatureFromDer.Fixed.signature_decode_bounded hBindings hMachine hCall

theorem p256_signing_key_generate_from_rng_writes_signing_key
    [bindings : Machine.Bindings] {initial : Machine.RamState}
    {randomBytes : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall signingKeyGenerateFromRng initial [randomBytes]) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[outputRegion signingKeyGenerateFromRng initial [randomBytes], allocatorStateRegion,
          randomSourceRegion, callStack signingKeyGenerateFromRng initial] ∧
      readOutput signingKeyGenerateFromRng initial final =
        .ok (Generate.generatedSigningKey #[randomBytes]) := by
  exact P256.Proofs.Generate.generate_correct hBindings hMachine hCall

theorem p256_ecdh_diffie_hellman_writes_shared_secret
    [bindings : Machine.Bindings] {initial : Machine.RamState}
    {secretKey publicKey : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall ecdhDiffieHellman initial [secretKey, publicKey]) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[outputRegion ecdhDiffieHellman initial [secretKey, publicKey], allocatorStateRegion,
          randomSourceRegion, callStack ecdhDiffieHellman initial] ∧
      readOutput ecdhDiffieHellman initial final =
        .ok (Ecdh.diffieHellman #[secretKey, publicKey]) := by
  exact P256.Proofs.EcdhWrapper.ecdh_correct_of_raw
    (fun _ _ _ pre ↦ P256.Proofs.Sec1.Affine.affine_decode_correct pre)
    hBindings hMachine hCall

end P256.Statements
