import P256.Proofs.Sec1.Wrapper.Tag
import P256.Proofs.Sec1.Wrapper.Restore
import P256.Proofs.Sec1.Wrapper.DecoderReturn
import P256.Proofs.Program.CallPre

set_option autoImplicit false

namespace P256.Proofs.Sec1.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem reject [bindings : Bindings] {initial s : RamState}
    (state : ReturnState initial s) (stack : Stack.Valid initial 4048)
    (outside : ¬ InProgram (returnBoundary initial).rip)
    (low : (returnBoundary initial).rip.toNat < 2^32)
    (rip : s.RIP = 0x10183c)
    (tag : memLoad s.external (stackPtr initial - 232) 64 = 1) :
    ∃ fuel t, Returns (returnBoundary initial) fuel s t ∧
      SupportedIntegerMachineState bindings.processor t ∧
      MachineRamUnitStrideDecodable bindings t ∧
      CalleeSavedRegistersUnchanged initial t ∧ DirectionFlagUnset t ∧
      FailureStatus t invalidPublicKeyStatus ∧ t.external = s.external := by
  obtain ⟨a, ha, stateA, ripA, statusA, frameA⟩ :=
    tag_branch (valid := false) state stack outside rip tag
  obtain ⟨t, ht, machine, bindingsSupported, saved, direction, memory, status⟩ :=
    restore stateA stack outside low ripA
  refine ⟨_, t, ha.returns ht, machine, bindingsSupported, saved, direction, ?_, ?_⟩
  · change (t.regValue .rax).setWidth 32 = 1
    rw [status, statusA]
    rfl
  · exact memory.trans (frameA.external (by simp [Component.Covers]))

theorem reject_from_decoder [bindings : Bindings] {initial s t : RamState}
    {input : ByteArray} {slices : Array Input}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCallWithSlices publicKeyFromSec1Bytes initial [input] slices)
    (entry : DecoderEntry initial s input (returnBoundary initial))
    (result : CalleeResult s t (returnBoundary initial) 80 3680)
    (tag : memLoad t.external (s.regValue .rdi) 64 = 1) :
    ∃ fuel final, UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧ DirectionFlagUnset final ∧
      FailureStatus final invalidPublicKeyStatus ∧
      MemoryWriteFrame initial final
        #v[allocatorStateRegion, randomSourceRegion, callStack publicKeyFromSec1Bytes initial] := by
  have hs : Stack.Valid initial 4048 := hCall.stackAvailable.1
  have state := decoder_return_state hs entry result
  have frame := decoder_return_frame hs entry result
  obtain ⟨n, execution⟩ := decoder_return_execution entry result
  have hb := initial_boundary hCall hMachine hBindings
  obtain ⟨boundary, he, low, outside⟩ := hCall.returnAddress
  rw [hb] at he
  cases he
  have rip : t.RIP = 0x10183c := result.rip.trans entry.decoderReturn
  rw [entry.destination] at tag
  obtain ⟨_, final, returned, machine, binding, saved, direction, status, memory⟩ :=
    reject state hs outside low rip tag
  obtain ⟨total, unique⟩ := (execution.returns returned).unique_of_boundary hb
  refine ⟨total, final, unique, machine, binding, saved, direction, status, ?_⟩
  intro a ha
  rw [memory]
  exact frame a ha

end P256.Proofs.Sec1.Wrapper
