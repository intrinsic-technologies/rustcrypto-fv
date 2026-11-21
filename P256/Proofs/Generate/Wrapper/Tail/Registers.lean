import P256.Proofs.Generate.Wrapper.State

set_option autoImplicit false

namespace P256.Proofs.Generate.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program

theorem State.after_registers [Bindings] {initial s t : RamState} {offset fuel : Nat}
    {written : Option MemoryRegion} {cs : List Component}
    (state : State initial s offset written)
    (run : Advances (returnBoundary initial) fuel s t) (ready : ReadyToStep t)
    (agrees : AgreesExcept cs s t)
    (noMem : ∀ c ∈ cs, ∀ a, ¬ c.Covers a)
    (kept : ∀ r ∈ [4,14,3,5,12,13], Component.reg r ∉ cs)
    (df : Component.df ∉ cs) : State initial t offset written := by
  have memory := agrees.external noMem
  obtain ⟨n,previous⟩ := state.execution
  refine ⟨⟨n+fuel,previous.trans run⟩,
    bindingsSupported_of_ready_agrees state.bindingsSupported ready agrees,
    supportedMachine_of_ready_agrees state.machine ready agrees,?_,
    agrees.directionFlagClear df state.directionFlag,
    (agrees.read (n := 64) (kept 4 (by simp))).trans state.rsp,
    (agrees.read (n := 64) (kept 14 (by simp))).trans state.output,
    (agrees.read (n := 64) (kept 3 (by simp))).trans state.capacity,
    ?_,?_,?_,?_,?_,fun a ha => agrees.grow a (state.allocated a ha),?_⟩
  · simpa only [ProgramLoaded,memory] using state.loaded
  · simpa only [memory] using state.savedRbx
  · simpa only [memory] using state.savedR14
  · simpa only [memory] using state.savedR15
  · simpa only [memory] using state.returnAddress
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (agrees.read (n := 64) (kept 5 (by simp))).trans (state.otherRegisters .rbp (by simp))
    · exact (agrees.read (n := 64) (kept 12 (by simp))).trans (state.otherRegisters .r12 (by simp))
    · exact (agrees.read (n := 64) (kept 13 (by simp))).trans (state.otherRegisters .r13 (by simp))
  · cases written <;> intro a ha <;> rw [memory] <;> exact state.frame a ha

end P256.Proofs.Generate.Wrapper
