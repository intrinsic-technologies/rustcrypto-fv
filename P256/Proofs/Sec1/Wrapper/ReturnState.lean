import P256.Proofs.Program.WrapperReturn.State

set_option autoImplicit false

namespace P256.Proofs.Sec1.Wrapper

open P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure ReturnState [bindings : Bindings] (initial s : RamState) : Prop where
  bindingsSupported : MachineRamUnitStrideDecodable bindings s
  machine : SupportedIntegerMachineState bindings.processor s
  loaded : ProgramLoaded s
  directionFlag : DirectionFlagUnset s
  rsp : stackPtr s = stackPtr initial - 232
  savedRbx : memLoad s.external (stackPtr initial - 24) 64 = initial.regValue .rbx
  savedR14 : memLoad s.external (stackPtr initial - 16) 64 = initial.regValue .r14
  savedR15 : memLoad s.external (stackPtr initial - 8) 64 = initial.regValue .r15
  returnAddress : memLoad s.external (stackPtr initial) 64 = (returnBoundary initial).rip
  otherRegisters : ∀ r ∈ [Syntax.Reg.rbp, .r12, .r13], s.regValue r = initial.regValue r
  allocated : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome

theorem ReturnState.after_registers [Bindings] {initial s t : RamState} {cs : List Component}
    (state : ReturnState initial s) (ready : ReadyToStep t) (agrees : AgreesExcept cs s t)
    (memory : ∀ c ∈ cs, ∀ a, ¬ c.Covers a)
    (registers : ∀ r ∈ [4,5,12,13], Component.reg r ∉ cs)
    (df : Component.df ∉ cs) : ReturnState initial t := by
  have hm := agrees.external memory
  refine ⟨bindingsSupported_of_ready_agrees state.bindingsSupported ready agrees,
    supportedMachine_of_ready_agrees state.machine ready agrees, ?_,
    agrees.directionFlagClear df state.directionFlag,
    (agrees.read (n := 64) (registers 4 (by simp))).trans state.rsp,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [ProgramLoaded, hm] using state.loaded
  · simpa only [hm] using state.savedRbx
  · simpa only [hm] using state.savedR14
  · simpa only [hm] using state.savedR15
  · simpa only [hm] using state.returnAddress
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (agrees.read (n := 64) (registers 5 (by simp))).trans (state.otherRegisters .rbp (by simp))
    · exact (agrees.read (n := 64) (registers 12 (by simp))).trans (state.otherRegisters .r12 (by simp))
    · exact (agrees.read (n := 64) (registers 13 (by simp))).trans (state.otherRegisters .r13 (by simp))
  · intro a ha
    rw [hm]
    exact state.allocated a ha

end P256.Proofs.Sec1.Wrapper
