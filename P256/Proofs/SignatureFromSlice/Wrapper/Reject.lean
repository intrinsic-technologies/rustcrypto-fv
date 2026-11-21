import P256.Proofs.SignatureFromSlice.Wrapper.DecoderReturn
import P256.Proofs.SignatureFromSlice.Wrapper.Epilogue
import P256.Proofs.SignatureFromDer.Fixed.Interface
import P256.Proofs.Program.CallPre

set_option autoImplicit false

namespace P256.Proofs.SignatureFromSlice.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem reject_from_decoder [bindings : Bindings] {initial s t : RamState}
    {input : ByteArray} {slices : Array Input}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCallWithSlices signatureFromSlice initial [input] slices)
    (entry : DecoderEntry initial s input (returnBoundary initial))
    (result : CalleeResult s t (returnBoundary initial) 72 560)
    (decoded : SignatureFromDer.Fixed.ResultAt t (s.regValue .rdi) input)
    (hmodel : Ecdsa.signatureFromSlice #[input] = none) :
    ∃ fuel final, UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧ DirectionFlagUnset final ∧
      FailureStatus final invalidSignatureBytesStatus ∧
      MemoryWriteFrame initial final
        #v[allocatorStateRegion, randomSourceRegion, callStack signatureFromSlice initial] := by
  have hs : Stack.Valid initial 656 := hCall.stackAvailable.1
  have state := decoder_return_state hs entry result
  have frame := decoder_return_frame hs entry result
  obtain ⟨n, execution⟩ := decoder_return_execution entry result
  have hb := initial_boundary hCall hMachine hBindings
  obtain ⟨boundary, he, low, outside⟩ := hCall.returnAddress
  rw [hb] at he
  cases he
  have rip : t.RIP = 0x102280 := result.rip.trans entry.decoderReturn
  have failed : Ecdsa.decodeSignature input = none := by
    change (Ecdsa.decodeSignature input).map Ecdsa.encodeFixed = none at hmodel
    cases h : Ecdsa.decodeSignature input <;> simp_all only [Option.map_some, Option.map_none, reduceCtorEq]
  simp only [SignatureFromDer.Fixed.ResultAt, failed] at decoded
  rw [entry.destination] at decoded
  have null : memLoad t.external (stackPtr initial - 80) 64 = 0 := by
    simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg,
      BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using decoded.2
  obtain ⟨fuel,u,hu,machine,binding,saved,direction,status,memory⟩ :=
    Epilogue.reject state hs outside low rip decoded.1 null
  obtain ⟨total, unique⟩ := (execution.returns hu).unique_of_boundary hb
  refine ⟨total,u,unique,machine,binding,saved,direction,status,?_⟩
  intro a ha
  rw [memory]
  exact frame a ha

end P256.Proofs.SignatureFromSlice.Wrapper
