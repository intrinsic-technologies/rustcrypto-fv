import P256.Proofs.Program.ScalarFrame.Memory
import P256.Proofs.Generate.Wrapper.Tail.OutputSafety
import P256.Proofs.Generate.Wrapper.Geometry
import P256.Proofs.Generate.Wrapper.Finish.Zero

set_option autoImplicit false

namespace P256.Proofs.Generate.Wrapper.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program

set_option maxHeartbeats 800000 in
theorem zero_run [Bindings] {initial s : RamState} {input : ByteArray}
    {slices : Array Input}
    (call : ValidCallWithSlices signingKeyGenerateFromRng initial [input] slices)
    (state : OutputState initial s input) (rip : s.RIP = 0x106e7c)
    (outside : ¬ InProgram (returnBoundary initial).rip) :
    ∃ t, OutputState initial t input ∧ t.RIP = 0x106ec8 ∧
      MemoryWriteFrame s t #v[workRegion initial] ∧ t.regValue .r15 = s.regValue .r15 := by
  have hp : ZeroPre s := by
    refine ⟨rip,?_,?_⟩
    · intro off ho
      rw [ScalarFrame.scalar_stack_address (frameOffset := 264) state.rsp (by decide) (by
        all_goals simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
        all_goals rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
      apply stack_buffer_writable call state.allocated _ _ (by decide)
      all_goals simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
      all_goals rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · intro off ho offset len hb
      rw [ScalarFrame.scalar_stack_address (frameOffset := 264) state.rsp (by decide) (by
        all_goals simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
        all_goals rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
      apply stack_buffer_code_apart call _ _ hb
      all_goals simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
      all_goals rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  obtain ⟨n,t,run,ready,_,effect⟩ := zeroize (returnBoundary initial) outside s
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x6e7c zeroBytes
      (by decide) (by decide +kernel)) hp
  have writes : WritesWithin (zeroEffect s).components #v[workRegion initial] := by
    intro c hc a ha
    simp only [zeroEffect,Effect.components,List.map_cons,List.map_nil,Write.component_reg,
      Write.component_mem,Nat.reduceDiv,List.append_nil,List.cons_append,List.nil_append,
      List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals refine ⟨workRegion initial,by simp,?_⟩
    all_goals rw [ScalarFrame.scalar_stack_address (frameOffset := 264) state.rsp (by decide) (by decide)] at ha
    all_goals exact work_contains call.stackAvailable.1 (by decide) (by decide) ha
  have kept : ∀ r ∈ [14,3,5,12,13], Component.reg r ∉ (zeroEffect s).components := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [zeroEffect,Effect.components]
  exact ⟨t,state.after_effect call run ready effect.agrees writes
    ((effect.agrees.read (n := 64) (r := 4) (by simp [zeroEffect,Effect.components])).trans state.rsp)
    kept (by simp [zeroEffect,Effect.components]),effect.rip,
    effect.agrees.memoryWriteFrame writes,
    effect.agrees.read (n := 64) (r := 15) (by simp [zeroEffect,Effect.components])⟩

end P256.Proofs.Generate.Wrapper.Finish
