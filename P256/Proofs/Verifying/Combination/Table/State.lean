import P256.Proofs.Verifying.Combination.Table.Interface
import P256.Proofs.Program.State
import P256.Proofs.Common.Machine.CallReturn

set_option autoImplicit false

open P256.Proofs.Program (supportedMachine_of_ready_agrees)

namespace P256.Proofs.Verifying.Combination.Table

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def savedRegisters : List (Syntax.Reg × Nat) :=
  [(.r15, 8), (.r14, 16), (.r12, 24), (.rbx, 32)]

structure FrameState [bindings : Bindings] (s t : RamState) (cursor : BitVec 64) (stackOffset : BitVec 64 := 1096) : Prop where
  bindingsSupported : MachineRamUnitStrideDecodable bindings t
  machine : SupportedIntegerMachineState bindings.processor t
  loaded : ProgramLoaded t
  directionFlag : Prelude.RFLAGS.DirectionFlagClear t.RFLAGS
  allocated : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome
  frame : MemoryWriteFrame s t #v[registerRegion s .rdi 768, cursorRegion cursor, Stack.region s 2120]
  rsp : stackPtr t = stackPtr s - stackOffset
  saved : ∀ entry ∈ savedRegisters,
    (Operand.mem (stackPtr s - BitVec.ofNat 64 entry.2) : Operand 64).read t =
      s.regValue entry.1
  rbp : t.regValue .rbp = s.regValue .rbp
  r13 : t.regValue .r13 = s.regValue .r13
  returnAddress : (Operand.mem (stackPtr s) : Operand 64).read t =
    (Operand.mem (stackPtr s) : Operand 64).read s
  mxcsr : t.MXCSR = s.MXCSR
  fp87 : t.FP87_Control = s.FP87_Control

theorem FrameState.after_registers [Bindings] {s u t : RamState} {cs : List Component}
    {cursor stackOffset : BitVec 64} (state : FrameState s u cursor stackOffset) (ready : ReadyToStep t) (h : AgreesExcept cs u t)
    (hm : ∀ c ∈ cs, ∀ a, ¬ c.Covers a) (hsp : .reg 4 ∉ cs) (hbp : .reg 5 ∉ cs) (h13 : .reg 13 ∉ cs)
    (hdf : Component.df ∉ cs := by component_not_mem)
    (hmxcsr : Component.mxcsr ∉ cs := by component_not_mem)
    (hfcw : Component.fcw ∉ cs := by component_not_mem) : FrameState s t cursor stackOffset := by
  have memory := h.external hm
  refine ⟨P256.Proofs.Program.bindingsSupported_of_ready_agrees state.bindingsSupported ready h,
    supportedMachine_of_ready_agrees state.machine ready h,
    ?_, h.directionFlagClear (by component_not_mem) state.directionFlag,
    fun a ha => h.grow a (state.allocated a ha), ?_,
    (h.read (n := 64) (r := 4) hsp).trans state.rsp, ?_,
    (h.read (n := 64) (r := 5) hbp).trans state.rbp,
    (h.read (n := 64) (r := 13) h13).trans state.r13, ?_,
    (h.mxcsr (by component_not_mem)).trans state.mxcsr,
    (h.fcw (by component_not_mem)).trans state.fp87⟩
  · intro a b hb
    rw [memory]
    exact state.loaded a b hb
  · intro a ha
    rw [memory]
    exact state.frame a ha
  · intro entry he
    change memLoad t.external _ 64 = _
    rw [memory]
    exact state.saved entry he
  · change memLoad t.external _ 64 = _
    rw [memory]
    exact state.returnAddress

end P256.Proofs.Verifying.Combination.Table
