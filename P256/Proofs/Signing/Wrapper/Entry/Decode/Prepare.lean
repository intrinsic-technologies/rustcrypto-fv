import P256.Proofs.Signing.Wrapper.Entry.Decode.State
import P256.Proofs.Signing.Wrapper.Entry.Decode.Copy
import P256.Proofs.Signing.Wrapper.Entry.Decode.Saves
import P256.Proofs.Program.StackBuffer

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Entry.Decode

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem copy_pre [Bindings] {initial s : RamState} {secret message : ByteArray}
    {slices : Array Input}
    (call : ValidCallWithSlices signingKeyTrySign initial [secret,message] slices)
    (state : State initial s 520) (rip : s.RIP = 0x1023c9)
    (source : s.regValue .rax = memLoad initial.external (initial.regValue .rdi) 64) :
    CopyPre secret s := by
  have size := ((arguments_iff secret message).mp call.argumentsValid).1
  obtain ⟨address,original,_,bounded,bytes,_,_,_,_⟩ := preserved_first_input call state.frame
  have src : s.regValue .rax = address := source.trans original
  have dst : stackPtr s + 336 = stackPtr initial - 184 := by
    rw [state.rsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  refine ⟨rip, ?_, ?_, ?_, ?_, ?_⟩
  · change (MemoryRegion.mk (s.regValue .rax).toNat 32).Bounded
    simpa only [src,size] using bounded
  · change (MemoryRegion.mk (s.regValue .rax).toNat 32).HasBytes s.external secret
    simpa only [src,size] using bytes
  · rw [dst]
    exact stack_buffer_writable call.stackAvailable.1 (call_stack_avoids call) state.allocated
      (offset := 184) (by decide) (by decide) (by decide)
  · rw [dst,src]
    have sep := wrapper_read_disjoint call (first_input_region call)
      (callStack signingKeyTrySign initial) (by simp [wrapperRegions])
    rw [original,size] at sep
    intro i hi j hj eq
    apply sep (address + BitVec.ofNat 64 j).toNat
    · apply memoryRegion_contains_add (size ▸ bounded) (len := 32)
        (Nat.le_refl _) (Nat.le_refl _) hj
    · rw [← eq]
      exact stack_component_within call.stackAvailable.1
        (offset := 184) (by decide) (by decide) ⟨i,hi,rfl⟩
  · rw [dst]
    exact stack_buffer_avoids call.stackAvailable.1 (call_stack_avoids call)
      (offset := 184) (by decide) (by decide)

theorem prepare [bindings : Bindings] {initial s : RamState} {secret message : ByteArray}
    {slices : Array Input}
    (context : Context initial secret message)
    (call : ValidCallWithSlices signingKeyTrySign initial [secret,message] slices)
    (entry : GuardedEntry initial s secret) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ State initial t 520 ∧
      t.RIP = 0x102418 ∧ t.regValue .r12 = initial.regValue .rdi ∧
      t.regValue .r15 = initial.regValue .rdx ∧ t.regValue .r13 = 2 ∧
      (MemoryRegion.mk (stackPtr initial - 184).toNat 32).HasBytes t.external secret ∧
      t.regValue .rbx = initial.regValue .rcx ∧ t.regValue .r14 = initial.regValue .r8 := by
  have outside := outer_boundary call context.machine context.bindingsSupported
  obtain ⟨k,a,ha,ra,_,ea⟩ := save_registers (returnBoundary initial) outside s
    (readyToStep entry.machine entry.bindingsSupported)
    (programText_slice (programLoaded_codeIn entry.loaded) 0x23c0 saveRegisterBytes
      (by decide) (by decide +kernel)) entry.rip
  have ag : AgreesExcept [.reg 14,.reg 3,.reg 13,.rip] s a := ea.agrees
  have sa : State initial a 520 := entry.toState.after_effect call ha ra ag
    (by simp [WritesWithin,Component.Covers])
    ((ag.read (n := 64) (r := 4) (by simp)).trans entry.rsp) (by simp)
  have source : a.regValue .rax = memLoad initial.external (initial.regValue .rdi) 64 :=
    (ag.read (n := 64) (r := 0) (by simp)).trans entry.sourceAddress
  have count : a.regValue .r13 = 2 := ea.writes.2.2.trans entry.count
  obtain ⟨t,result⟩ := copy_correct ra sa.loaded outside (copy_pre call sa ea.rip source)
  obtain ⟨n,run⟩ := result.execution
  have dst : stackPtr a + 336 = stackPtr initial - 184 := by
    rw [sa.rsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  have st : State initial t 520 := sa.after_effect call run result.ready result.agrees
    (by
      intro c hc x hx
      simp only [copyComponents,List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals try exact hx.elim
      refine ⟨workRegion initial,by simp,?_⟩
      rw [dst] at hx
      exact work_contains call.stackAvailable.1 (offset := 184) (by decide) (by decide) hx)
    (result.rsp.trans sa.rsp) (by simp [copyComponents])
  refine ⟨k+n,t,ha.trans run,st,result.rip,?_,?_,?_,?_,?_,?_⟩
  · exact ((ag.trans result.agrees).read (n := 64) (r := 12)
      (by simp [copyComponents])).trans entry.pointers
  · exact ((ag.trans result.agrees).read (n := 64) (r := 15)
      (by simp [copyComponents])).trans entry.lengths
  · exact (result.agrees.read (n := 64) (r := 13) (by simp [copyComponents])).trans count
  · simpa only [dst] using result.bytes
  · exact (result.agrees.read (n := 64) (r := 3) (by simp [copyComponents])).trans
      (ea.writes.2.1.trans entry.output)
  · exact (result.agrees.read (n := 64) (r := 14) (by simp [copyComponents])).trans
      (ea.writes.1.trans entry.capacity)

end P256.Proofs.Signing.Wrapper.Entry.Decode
