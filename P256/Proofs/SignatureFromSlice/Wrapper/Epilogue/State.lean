import P256.Proofs.Program.Interface
import P256.Proofs.Program.State
import P256.Proofs.Program.Code
import P256.Proofs.Program.Stack

set_option autoImplicit false

namespace P256.Proofs.SignatureFromSlice.Wrapper.Return

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure State [bindings : Bindings] (initial t : RamState) (stackOffset : Nat) : Prop where
  bindingsSupported : MachineRamUnitStrideDecodable bindings t
  machine : SupportedIntegerMachineState bindings.processor t
  loaded : ProgramLoaded t
  directionFlag : DirectionFlagUnset t
  rsp : stackPtr t = stackPtr initial - BitVec.ofNat 64 stackOffset
  output : t.regValue .rbx = initial.regValue .rcx
  capacity : t.regValue .r14 = initial.regValue .r8
  savedRbx : memLoad t.external (stackPtr initial - 16) 64 = initial.regValue .rbx
  savedR14 : memLoad t.external (stackPtr initial - 8) 64 = initial.regValue .r14
  returnAddress : memLoad t.external (stackPtr initial) 64 = (returnBoundary initial).rip
  otherRegisters : ∀ r ∈ [Syntax.Reg.rbp, .r12, .r13, .r15],
    t.regValue r = initial.regValue r
  allocated : ∀ a : BitVec 64, (initial.external[a]?).isSome → (t.external[a]?).isSome

theorem State.after_registers [Bindings] {initial t u : RamState} {cs : List Component} {stackOffset : Nat}
    (state : State initial t stackOffset) (ready : ReadyToStep u) (agrees : AgreesExcept cs t u)
    (memory : ∀ c ∈ cs, ∀ a, ¬ c.Covers a)
    (registers : ∀ r ∈ [4, 14, 3, 5, 12, 13, 15], Component.reg r ∉ cs)
    (df : Component.df ∉ cs) : State initial u stackOffset := by
  have hm := agrees.external memory
  refine ⟨bindingsSupported_of_ready_agrees state.bindingsSupported ready agrees,
    supportedMachine_of_ready_agrees state.machine ready agrees,
    ?_, agrees.directionFlagClear df state.directionFlag,
    (agrees.read (n := 64) (registers 4 (by simp))).trans state.rsp,
    (agrees.read (n := 64) (registers 3 (by simp))).trans state.output,
    (agrees.read (n := 64) (registers 14 (by simp))).trans state.capacity,
    ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [ProgramLoaded, hm] using state.loaded
  · simpa only [hm] using state.savedRbx
  · simpa only [hm] using state.savedR14
  · simpa only [hm] using state.returnAddress
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (agrees.read (n := 64) (registers 5 (by simp))).trans (state.otherRegisters .rbp (by simp))
    · exact (agrees.read (n := 64) (registers 12 (by simp))).trans (state.otherRegisters .r12 (by simp))
    · exact (agrees.read (n := 64) (registers 13 (by simp))).trans (state.otherRegisters .r13 (by simp))
    · exact (agrees.read (n := 64) (registers 15 (by simp))).trans (state.otherRegisters .r15 (by simp))
  · intro a ha
    rw [hm]
    exact state.allocated a ha

theorem State.after_callee [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    {offset outputBytes reserve : Nat} (state : State initial s (offset + 8))
    (result : CalleeResult s t boundary outputBytes reserve)
    (words : ∀ off ∈ ([0,8,16] : List Nat),
      memLoad t.external (stackPtr initial - BitVec.ofNat 64 off) 64 =
        memLoad s.external (stackPtr initial - BitVec.ofNat 64 off) 64) :
    State initial t offset := by
  refine ⟨result.bindingsSupported, result.machine, result.loaded, result.directionFlag,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha => result.allocated a (state.allocated a ha)⟩
  · change t.regValue .rsp = _
    rw [result.rsp]
    change stackPtr s + 8 = _
    rw [state.rsp, BitVec.ofNat_add, ← BitVec.sub_sub]
    exact BitVec.sub_add_cancel _ _
  · exact (result.calleeSaved .rbx (by simp)).trans state.output
  · exact (result.calleeSaved .r14 (by simp)).trans state.capacity
  · exact (words 16 (by simp)).trans state.savedRbx
  · exact (words 8 (by simp)).trans state.savedR14
  · have he := words 0 (by simp)
    simp only [BitVec.sub_zero] at he
    exact he.trans state.returnAddress
  · intro r hr
    apply (result.calleeSaved r ?_).trans (state.otherRegisters r hr)
    simp only [List.mem_cons] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | hr <;> simp_all

end P256.Proofs.SignatureFromSlice.Wrapper.Return

namespace P256.Proofs.SignatureFromSlice.Wrapper.Epilogue
abbrev State [X86.Machine.Bindings] (initial t : X86.Machine.RamState) :=
  P256.Proofs.SignatureFromSlice.Wrapper.Return.State initial t 88
end P256.Proofs.SignatureFromSlice.Wrapper.Epilogue
