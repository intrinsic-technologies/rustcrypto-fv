import P256.Proofs.Program.ScalarFrame.Memory
import P256.Proofs.Generate.Wrapper.Descriptor
import P256.Proofs.Generate.Wrapper.Geometry
import P256.Proofs.Generate.Wrapper.Prologue

set_option autoImplicit false

namespace P256.Proofs.Generate.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program
open P256.Proofs.Pkcs8 (saveComponents)

theorem prepare_descriptor [bindings : Bindings] {initial : RamState} {input : ByteArray}
    {slices : Array Input}
    (hb : MachineRamUnitStrideDecodable bindings initial)
    (hm : SupportedIntegerMachineState bindings.processor initial)
    (call : ValidCallWithSlices signingKeyGenerateFromRng initial [input] slices) :
    ∃ u, State initial u 264 ∧ u.RIP = 0x106da8 ∧
      u.regValue .rsi = stackPtr initial-256 ∧ u.regValue .rdi = stackPtr initial-184 ∧
      u.regValue .r15 = stackPtr initial-184 ∧
      memLoad u.external (stackPtr initial-256) 64 =
        memLoad initial.external (initial.regValue .rdi) 64 ∧
      memLoad u.external (stackPtr initial-248) 64 = BitVec.ofNat 64 input.size := by
  obtain ⟨s,hs⟩ := guards_correct hb hm call
  have state : State initial s 264 := by
    refine ⟨hs.execution,bindingsSupported_of_ready_agrees hb hs.ready hs.agrees,
      supportedMachine_of_ready_agrees hm hs.ready hs.agrees,hs.loaded,
      hs.agrees.directionFlagClear (by simp [saveComponents,arenaComponents,guardComponents])
        call.directionFlagUnset,hs.rsp,hs.output,hs.capacity,hs.savedRbx,hs.savedR14,
      hs.savedR15,hs.returnAddress,?_,hs.agrees.grow,hs.frame⟩
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hs.agrees.read (n := 64) (r := 5) (by simp [saveComponents,arenaComponents,guardComponents])
    · exact hs.agrees.read (n := 64) (r := 12) (by simp [saveComponents,arenaComponents,guardComponents])
    · exact hs.agrees.read (n := 64) (r := 13) (by simp [saveComponents,arenaComponents,guardComponents])
  have address (off : Nat) (h : off ≤ 264) :
      stackPtr s+BitVec.ofNat 64 off = stackPtr initial-BitVec.ofNat 64 (264-off) :=
    ScalarFrame.scalar_stack_address state.rsp (by decide) h
  have addr8 : stackPtr s+8 = stackPtr initial-256 := address 8 (by decide)
  have addr16 : stackPtr s+16 = stackPtr initial-248 := address 16 (by decide)
  have addr80 : stackPtr s+80 = stackPtr initial-184 := address 80 (by decide)
  have pre : DescriptorPre s := by
    refine ⟨hs.rip,?_,?_⟩
    · intro off ho
      have hb : off = 8 ∨ off = 16 := by simpa using ho
      rw [address off (by omega)]
      exact stack_buffer_writable call state.allocated (by omega) (by omega) (by decide)
    · intro off ho codeOffset codeLen hcode
      have hb : off = 8 ∨ off = 16 := by simpa using ho
      rw [address off (by omega)]
      exact stack_buffer_code_apart call (by omega) (by omega) hcode
  obtain ⟨fuel,u,run,ready,_,effect⟩ := descriptor_block (returnBoundary initial)
    (outer_boundary call hm hb) s hs.ready
    (programText_slice (programLoaded_codeIn hs.loaded) 0x6d91 descriptorBytes
      (by decide) (by decide +kernel)) pre
  have next : State initial u 264 := state.after_effect call run ready effect.agrees
    (by
      intro c hc a ha
      simp only [descriptorEffect,Effect.components,Write.component,Operand.component,
        List.map_cons,List.map_nil,List.append_nil,List.cons_append,List.nil_append,
        List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals try exact ha.elim
      · refine ⟨workRegion initial,by simp,?_⟩
        rw [addr8] at ha
        exact work_contains call.stackAvailable.1 (by decide) (by decide) ha
      · refine ⟨workRegion initial,by simp,?_⟩
        rw [addr16] at ha
        exact work_contains call.stackAvailable.1 (by decide) (by decide) ha)
    ((effect.agrees.read (n := 64) (r := 4)
      (by simp [descriptorEffect,Effect.components])).trans state.rsp)
    (by simp [descriptorEffect,Effect.components])
    (by simp [descriptorEffect,Effect.components])
  refine ⟨u,next,effect.rip,?_,?_,?_,?_,?_⟩
  · exact effect.writes.2.2.2.1.trans (address 8 (by decide))
  · exact effect.writes.2.2.2.2.trans (address 80 (by decide))
  · exact effect.writes.2.2.1.trans (address 80 (by decide))
  · have h : memLoad u.external (stackPtr s+8) 64 = s.regValue .rcx := effect.writes.1
    rw [addr8] at h
    exact h.trans hs.sourceAddress
  · have h : memLoad u.external (stackPtr s+16) 64 = s.regValue .rax := effect.writes.2.1
    rw [addr16] at h
    exact h.trans hs.length

end P256.Proofs.Generate.Wrapper
