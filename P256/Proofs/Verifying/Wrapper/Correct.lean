import P256.Proofs.Verifying.Wrapper.KeyEntry
import P256.Proofs.Verifying.Wrapper.Finish
import P256.Proofs.Verifying.Message.Convert.Model

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem correct_of_decoder_message [bindings : Bindings]
    (decoder : ∀ (s : RamState) (boundary : ReturnBoundary) (bytes : ByteArray),
      Sec1.DecodePre s boundary bytes → ∃ t, CalleeResult s t boundary 80 3680 ∧
        Sec1.PublicKeyResultAt t (s.regValue .rdi) (Points.decodePublicKey bytes))
    (messageCorrect : Message.Correct)
    {initial : RamState} {key signature message : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall verifyingKeyVerify initial [key,signature,message]) :
    ∃ fuel final, UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧ DirectionFlagUnset final ∧
      match Ecdsa.verifyMessage #[key,signature,message] with
      | some result => SuccessfulStatus final ∧
        MemoryWriteFrame initial final
          #v[outputRegion verifyingKeyVerify initial [key,signature,message],
            allocatorStateRegion,randomSourceRegion,callStack verifyingKeyVerify initial] ∧
        readOutput verifyingKeyVerify initial final = .ok result
      | none => FailureStatus final invalidSignatureStatus ∧
        MemoryWriteFrame initial final
          #v[allocatorStateRegion,randomSourceRegion,callStack verifyingKeyVerify initial] := by
  obtain ⟨slices,call⟩ := hCall
  obtain ⟨point,r,scalarS,keyDecoded,signatureDecoded,keySize,_,rPositive,rBound,sPositive,sBound⟩ :=
    verifying_arguments_decoded call.argumentsValid
  have outside := outer_boundary call hMachine hBindings
  obtain ⟨a,t,stateA,pre,output,sp,ret,ag,execution⟩ := key_decoder_entry hBindings hMachine call
  obtain ⟨u,callee,result⟩ := decoder t (returnBoundary initial) key pre
  have decoded : Points.decodePublicKey key = some point := by
    simpa only [Ecdsa.decodePublicKey,keySize,ite_true] using keyDecoded
  obtain ⟨v,stateV⟩ := key_result call stateA outside decoded output sp ret ag execution callee result
  obtain ⟨w,stateW⟩ := decode_signature call stateV outside signatureDecoded
  obtain ⟨x,stateX⟩ := copy_signature call stateW outside
  have valid := Message.Convert.decoded_key keyDecoded
  obtain ⟨y,stateY⟩ := verify_message messageCorrect call stateX outside valid.1 valid.2
    rPositive rBound sPositive sBound
  apply finish hBindings hMachine call stateY
  rw [verifyMessage_eq]
  simp only [Ecdsa.keyValue,keyDecoded,Ecdsa.signatureValue,signatureDecoded,Option.getD_some]

end P256.Proofs.Verifying.Wrapper
