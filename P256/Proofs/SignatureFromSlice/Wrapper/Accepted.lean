import P256.Proofs.SignatureFromSlice.Wrapper.Epilogue
import P256.Proofs.SignatureFromSlice.Wrapper.DecoderReturn
import P256.Proofs.SignatureFromDer.Fixed.Interface
import P256.Proofs.Program.CallPre
import P256.Proofs.SignatureFromSlice.Wrapper.Epilogue.Success.Memory
import P256.Proofs.SignatureFromSlice.Model

set_option autoImplicit false

namespace P256.Proofs.SignatureFromSlice.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem success_output {initial : RamState} {input output : ByteArray}
    (hmodel : Ecdsa.signatureFromSlice #[input] = some output) :
    outputRegion signatureFromSlice initial [input] = registerRegion initial .rcx 72 := by
  have size := signatureFromSlice_result_size hmodel
  change registerRegion initial .rcx (8 + resultBytes (Ecdsa.signatureFromSlice #[input])) = _
  rw [hmodel]
  change registerRegion initial .rcx (8 + output.size) = _
  rw [size]

theorem success_pre [bindings : Bindings] {initial : RamState} {input output : ByteArray}
    {slices : Array Input}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCallWithSlices signatureFromSlice initial [input] slices)
    (hmodel : Ecdsa.signatureFromSlice #[input] = some output) :
    Epilogue.Success.Pre initial := by
  have accepts : signatureFromSlice.accepts #[input] = true := by
    change (Ecdsa.signatureFromSlice #[input]).isSome = true
    rw [hmodel]
    rfl
  have size := signatureFromSlice_result_size hmodel
  have outputEq := success_output (initial := initial) hmodel
  have valid := hCall.outputInMemoryIfAccepted accepts
  have separate := hCall.outputSeparationIfAccepted accepts
  refine ⟨hCall.stackAvailable.1, ?_, ?_, ?_, ?_, outer_boundary hCall hMachine hBindings, ?_⟩
  · simpa only [ValidOutput, outputEq] using valid.2.1
  · simpa only [ValidOutput, outputEq] using valid.2.2
  · have hp := separate.1 ⟨0, by decide⟩ ⟨4, by decide⟩ (by decide)
    change (outputRegion signatureFromSlice initial [input]).Disjoint
      (callStack signatureFromSlice initial) at hp
    rw [outputEq] at hp
    intro a ha hb
    exact hp a ha (stack_contains_callStack hb)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [← outputEq]
      exact (separate.2 _ (by simp)).2
    · exact call_stack_avoids (routine := signatureFromSlice) hCall
  · have hc := hCall.outputSufficesIfAccepted accepts
    change 8 + resultBytes (Ecdsa.signatureFromSlice #[input]) ≤ _ at hc
    rw [hmodel] at hc
    change 8 + output.size ≤ _ at hc
    rwa [size] at hc

theorem success_frame {initial s t : RamState} {input output : ByteArray}
    (hmodel : Ecdsa.signatureFromSlice #[input] = some output)
    (frame : MemoryWriteFrame s t #v[registerRegion initial .rcx 72]) :
    MemoryWriteFrame s t #v[outputRegion signatureFromSlice initial [input]] := by
  simpa only [success_output (initial := initial) hmodel] using frame

theorem accept_from_decoder [bindings : Bindings] {initial s t : RamState}
    {input output : ByteArray} {slices : Array Input}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCallWithSlices signatureFromSlice initial [input] slices)
    (entry : DecoderEntry initial s input (returnBoundary initial))
    (result : CalleeResult s t (returnBoundary initial) 72 560)
    (decoded : SignatureFromDer.Fixed.ResultAt t (s.regValue .rdi) input)
    (hmodel : Ecdsa.signatureFromSlice #[input] = some output) :
    ∃ fuel final, UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧ DirectionFlagUnset final ∧
      SuccessfulStatus final ∧
      MemoryWriteFrame initial final
        #v[outputRegion signatureFromSlice initial [input], allocatorStateRegion,
          randomSourceRegion, callStack signatureFromSlice initial] ∧
      readOutput signatureFromSlice initial final = .ok output := by
  have pre := success_pre hBindings hMachine hCall hmodel
  have state := decoder_return_state pre.stack entry result
  have priorFrame := decoder_return_frame pre.stack entry result
  obtain ⟨n, execution⟩ := decoder_return_execution entry result
  have hb := initial_boundary hCall hMachine hBindings
  obtain ⟨boundary, he, low, _⟩ := hCall.returnAddress
  rw [hb] at he
  cases he
  have rip : t.RIP = 0x102280 := result.rip.trans entry.decoderReturn
  have mapped : (Ecdsa.decodeSignature input).map Ecdsa.encodeFixed =
      some output := hmodel
  cases model : Ecdsa.decodeSignature input with
  | none => simp only [model, Option.map_none, reduceCtorEq] at mapped
  | some value =>
    have outputEq : Ecdsa.encodeFixed value = output := by
      simpa only [model, Option.map_some, Option.some.injEq] using mapped
    simp only [SignatureFromDer.Fixed.ResultAt, model] at decoded
    rw [entry.destination] at decoded
    have first : SecretKeyFromBytes.Scalar.Nat256At t (stackPtr initial - 80) value.1 := by
      simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg,
        BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using decoded.2.1
    have second : SecretKeyFromBytes.Scalar.Nat256At t (stackPtr initial - 48) value.2 := by
      simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg,
        BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using decoded.2.2
    obtain ⟨fuel,u,hu,machine,binding,saved,direction,status,frame,bytes⟩ :=
      Epilogue.accept pre state low rip decoded.1 first second
    obtain ⟨total, unique⟩ := (execution.returns hu).unique_of_boundary hb
    refine ⟨total,u,unique,machine,binding,saved,direction,status,?_,?_⟩
    · have widened := success_frame hmodel frame
      intro a ha
      rw [widened a ?_]
      · apply priorFrame a
        intro region hr hc
        exact ha region (by simpa using Or.inr hr) hc
      · intro region hr hc
        have hr' : region = outputRegion signatureFromSlice initial [input] := by simpa using hr
        subst region
        exact ha _ (by simp) hc
    · simpa only [outputEq] using bytes

end P256.Proofs.SignatureFromSlice.Wrapper
