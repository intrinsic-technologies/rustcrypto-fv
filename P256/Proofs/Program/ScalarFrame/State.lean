import P256.Proofs.Program.Interface
import P256.Proofs.Program.State
import P256.Proofs.Program.SaveRegisters
import P256.Proofs.Common.Machine.CallReturn

set_option autoImplicit false

namespace P256.Proofs.Program.ScalarFrame

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

structure FrameState [bindings : Bindings] (s t : RamState) (outputBytes stackReserve : Nat)
    (stackOffset : BitVec 64) (outputRegister : Syntax.Reg := .rdi) : Prop where
  bindingsSupported : MachineRamUnitStrideDecodable bindings t
  machine : SupportedIntegerMachineState bindings.processor t
  loaded : ProgramLoaded t
  directionFlag : DirectionFlagUnset t
  allocated : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome
  frame : MemoryWriteFrame s t
    #v[registerRegion s outputRegister outputBytes, Stack.region s stackReserve]
  rsp : stackPtr t = stackPtr s - stackOffset
  saved : ∀ entry ∈ savedRegisters,
    memLoad t.external (stackPtr s - BitVec.ofNat 64 entry.2) 64 = s.regValue entry.1
  returnAddress : (Operand.mem (stackPtr s) : Operand 64).read t =
    (Operand.mem (stackPtr s) : Operand 64).read s
  mxcsr : t.MXCSR = s.MXCSR
  fp87 : t.FP87_Control = s.FP87_Control

theorem FrameState.after_registers [Bindings] {s u t : RamState} {cs : List Component}
    {outputBytes stackReserve : Nat} {stackOffset : BitVec 64} {outputRegister : Syntax.Reg}
    (state : FrameState s u outputBytes stackReserve stackOffset outputRegister) (ready : ReadyToStep t)
    (h : AgreesExcept cs u t) (hm : ∀ c ∈ cs, ∀ a, ¬ c.Covers a) (hsp : .reg 4 ∉ cs)
    (hdf : Component.df ∉ cs := by component_not_mem) (hmxcsr : Component.mxcsr ∉ cs := by component_not_mem)
    (hfcw : Component.fcw ∉ cs := by component_not_mem) :
    FrameState s t outputBytes stackReserve stackOffset outputRegister := by
  have memory := h.external hm
  refine ⟨bindingsSupported_of_ready_agrees state.bindingsSupported ready h,
    supportedMachine_of_ready_agrees state.machine ready h,
    ?_, h.directionFlagClear hdf state.directionFlag,
    fun a ha => h.grow a (state.allocated a ha), ?_,
    (h.read (n := 64) (r := 4) hsp).trans state.rsp, ?_, ?_,
    (h.mxcsr hmxcsr).trans state.mxcsr, (h.fcw hfcw).trans state.fp87⟩
  · intro a b hb
    rw [memory]
    exact state.loaded a b hb
  · intro a ha
    rw [memory]
    exact state.frame a ha
  · intro i hi
    rw [memory]
    exact state.saved i hi
  · change memLoad t.external _ 64 = _
    rw [memory]
    exact state.returnAddress

end P256.Proofs.Program.ScalarFrame
