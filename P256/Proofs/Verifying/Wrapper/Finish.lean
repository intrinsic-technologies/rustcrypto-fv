import P256.Proofs.Verifying.Wrapper.MessageResult
import P256.Proofs.Verifying.Wrapper.Accept
import P256.Proofs.Verifying.Wrapper.Reject
import P256.Proofs.Program.CallPre

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem finish [bindings : Bindings] {initial s : RamState} {key signature message : ByteArray}
    {slices : Array Input} {accepted : Bool}
    (hb : MachineRamUnitStrideDecodable bindings initial)
    (hm : SupportedIntegerMachineState bindings.processor initial)
    (call : ValidCallWithSlices verifyingKeyVerify initial [key,signature,message] slices)
    (state : Verified initial s accepted)
    (model : Ecdsa.verifyMessage #[key,signature,message] =
      if accepted then some .empty else none) :
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
  have boundaryEq := initial_boundary call hm hb
  obtain ⟨boundary,boundaryRead,low,outside⟩ := call.returnAddress
  rw [boundaryEq] at boundaryRead
  cases boundaryRead
  have readable : MemReadable s (stackPtr initial-208) 8 :=
    readable_of_grow (stack_sub_readable call.stackAvailable.1 (by decide) (by decide))
      state.allocated
  have tag := (Bytes.of_memLoad (n := 64) readable.mem).loadBytes64
  rw [state.result.tag] at tag
  obtain ⟨nf,first⟩ := state.execution
  cases accepted with
  | false =>
    have null : loadBytes s.external (stackPtr initial-200) 8 = .ok (0 : BitVec 64) := by
      have readable : MemReadable s (stackPtr initial-200) 8 :=
        readable_of_grow (stack_sub_readable call.stackAvailable.1 (by decide) (by decide))
          state.allocated
      have bytes := (Bytes.of_memLoad (n := 64) readable.mem).loadBytes64
      have value := state.result.error rfl
      have addr : stackPtr initial-208+8 = stackPtr initial-200 := by
        simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
        rfl
      rw [addr] at value
      rw [value] at bytes
      exact bytes
    obtain ⟨t,returned,machine,supported,saved,direction,status,memory⟩ :=
      reject state.toReturnState call.stackAvailable.1 outside low state.rip tag null
    obtain ⟨fuel,unique⟩ := (first.returns returned).unique_of_boundary boundaryEq
    refine ⟨fuel,t,unique,machine,supported,saved,direction,?_⟩
    rw [model]
    refine ⟨status,?_⟩
    intro address away
    rw [memory]
    exact state.frame address away
  | true =>
    have accepted : verifyingKeyVerify.accepts #[key,signature,message] = true := by
      change (Ecdsa.verifyMessage #[key,signature,message]).isSome = true
      rw [model]
      rfl
    obtain ⟨nt,t,returned,machine,supported,saved,direction,status,frame,output⟩ :=
      accept call accepted state.toReturnState outside low state.rip state.output state.capacity tag
    obtain ⟨fuel,unique⟩ := (first.returns returned).unique_of_boundary boundaryEq
    refine ⟨fuel,t,unique,machine,supported,saved,direction,?_⟩
    rw [model]
    refine ⟨status,?_,output⟩
    intro address away
    rw [frame address (by
      intro region member contains
      have eq : region = outputRegion verifyingKeyVerify initial [key,signature,message] :=
        by simpa using member
      subst region
      exact away _ (by simp) contains)]
    apply state.frame address
    intro region member contains
    exact away region (by simpa [wrapperRegions] using Or.inr member) contains

end P256.Proofs.Verifying.Wrapper
