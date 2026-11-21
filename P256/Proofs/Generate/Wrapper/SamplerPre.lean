import P256.Proofs.Generate.Wrapper.Geometry
import P256.Proofs.Program.WrapperInput
import P256.Proofs.Program.CalleeStack

set_option autoImplicit false

namespace P256.Proofs.Generate.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program

def samplerLayout : StackCallLayout 4024 16 104 3624 :=
  ⟨272,256,184,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩

theorem sampler_pre [Bindings] {initial t : RamState} {input : ByteArray}
    {slices : Array Input}
    (call : ValidCallWithSlices signingKeyGenerateFromRng initial [input] slices)
    (state : State initial t 272)
    (outside : ¬ InProgram (returnBoundary initial).rip)
    (rip : t.RIP = 0x100bd0)
    (source : t.regValue .rsi = stackPtr initial-256)
    (destination : t.regValue .rdi = stackPtr initial-184)
    (pointer : memLoad t.external (t.regValue .rsi) 64 =
      memLoad initial.external (initial.regValue .rdi) 64)
    (length : memLoad t.external (t.regValue .rsi+8) 64 = BitVec.ofNat 64 input.size)
    (ret : (returnBoundary t).rip = 0x106dad) :
    Sampler.Pre t (returnBoundary initial) input := by
  have pre := CalleePre.of_stack_region call.stackAvailable.1 (call_stack_avoids call)
    outside samplerLayout state.bindingsSupported state.machine state.directionFlag state.loaded
    state.allocated rip state.rsp source destination
    (ret ▸ inProgram_of_textOffset 0x6dad (by decide))
  obtain ⟨address,slicesEq,_,_,_,bounded,_⟩ := singleton_call_input call
  subst slices
  have original : memLoad initial.external (initial.regValue .rdi) 64 = address := by
    simpa using input_pointer_memLoad call.inputsInMemory ⟨0,by simp⟩
  have src : Sampler.source t = address := pointer.trans original
  have region : Sampler.inputRegion t input = (Input.mk address input).region := by
    simp only [Sampler.inputRegion,src,Input.region]
  have inputBytes : (Input.mk address input).region.HasBytes t.external input := by
    obtain ⟨a,eq,_,_,bytes,_⟩ := preserved_input call state.frame
    have same : a = address := eq.symm.trans original
    simpa only [same,Input.region] using bytes
  have sub (r : MemoryRegion) (hr : r ∈ (Sampler.writes t).toList) :
      ∀ a, r.Contains a → (callStack signingKeyGenerateFromRng initial).Contains a := by
    have bounds := stack_bounds call.stackAvailable.1
    have rsp : (stackPtr t).toNat = (stackPtr initial).toNat-272 := by
      rw [state.rsp]
      exact stack_sub_toNat call.stackAvailable.1 (by decide)
    have cases : r = registerRegion t .rdi 104 ∨ r = registerRegion t .rsi 16 ∨
        r = Stack.region t 3624 := by simpa [Sampler.writes] using hr
    intro a ha
    apply stack_contains_callStack
    rcases cases with rfl | rfl | rfl
    · change (MemoryRegion.mk (t.regValue .rdi).toNat 104).Contains a at ha
      rw [destination] at ha
      exact stack_buffer_contains call.stackAvailable.1 (by decide) (by decide) ha
    · change (MemoryRegion.mk (t.regValue .rsi).toNat 16).Contains a at ha
      rw [source] at ha
      exact stack_buffer_contains call.stackAvailable.1 (by decide) (by decide) ha
    · change (stackPtr t).toNat-3624 ≤ a ∧
        a < (Stack.region t 3624).start + (Stack.region t 3624).size at ha
      rw [stack_region_end,rsp] at ha
      change (stackPtr initial).toNat-4024 ≤ a ∧
        a < (Stack.region initial 4024).start + (Stack.region initial 4024).size
      rw [stack_region_end]
      constructor <;> omega
  refine ⟨pre,length,region.symm ▸ inputBytes,region.symm ▸ bounded,?_,?_,?_⟩
  · exact region.symm ▸ hasBytes_allocated inputBytes
  · intro r hr a ha hb
    rw [region] at ha
    exact wrapper_read_disjoint call (region := (Input.mk address input).region)
      (by simp [readRegions]) (callStack signingKeyGenerateFromRng initial)
      (by simp [wrapperRegions]) a ha (sub r hr a hb)
  · change (MemoryRegion.mk (t.regValue .rsi).toNat 16).Avoids _
    rw [source]
    exact stack_buffer_avoids call (by decide) (by decide)

end P256.Proofs.Generate.Wrapper
