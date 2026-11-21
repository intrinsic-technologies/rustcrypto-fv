import P256.Proofs.Field.Inverse.Setup.Saved
import P256.Proofs.Program.ScalarFrame.Memory

set_option autoImplicit false

namespace P256.Proofs.Field.Inverse

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program

abbrev workRegion (s : RamState) := ScalarFrame.Work.region s 880 16

structure SavedState [bindings : Bindings] (s t : RamState) : Prop where
  bindingsSupported : MachineRamUnitStrideDecodable bindings t
  machine : SupportedIntegerMachineState bindings.processor t
  loaded : ProgramLoaded t
  directionFlag : DirectionFlagUnset t
  allocated : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome
  frame : MemoryWriteFrame s t #v[registerRegion s .rdi 40, Stack.region s 880]
  registers : ∀ r ∈ [Syntax.Reg.r12, .r13, .r14, .r15], t.regValue r = s.regValue r
  rbx : t.regValue .rbx = s.regValue .rdi
  mxcsr : t.MXCSR = s.MXCSR
  fp87 : t.FP87_Control = s.FP87_Control
  saved : SavedWords s t

structure FrameState [Bindings] (s t : RamState) : Prop extends SavedState s t where
  rsp : stackPtr t = stackPtr s - 168

theorem FrameState.stack_address [Bindings] {s t : RamState} (state : FrameState s t)
    (i : BitVec 64) :
    (Operand.reg 4 : Operand 64).read t + i = stackPtr s - (168-i) := by
  change stackPtr t + i = _
  rw [state.rsp]
  simp only [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.neg_neg, BitVec.add_assoc]

theorem SavedState.after_result [Bindings] {s entry t : RamState} {boundary : ReturnBoundary}
    {outputBytes reserve : Nat} (pre : Pre s boundary) (state : SavedState s entry)
    (result : CalleeResult entry t boundary outputBytes reserve)
    (frame : MemoryWriteFrame entry t #v[registerRegion s .rdi 40, workRegion s]) :
    SavedState s t := by
  refine ⟨result.bindingsSupported, result.machine, result.loaded, result.directionFlag,
    fun a ha => result.allocated a (state.allocated a ha),
    memoryWriteFrame_trans state.frame (ScalarFrame.Work.frame pre frame), ?_,
    (result.calleeSaved .rbx (by simp)).trans state.rbx,
    result.mxcsr.trans state.mxcsr, result.fp87.trans state.fp87,
    state.saved.after_frame pre frame⟩
  intro r hr
  apply (result.calleeSaved r ?_).trans (state.registers r hr)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> simp

theorem SavedState.after_agrees [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {cs : List Component} (pre : Pre s boundary) (state : SavedState s t)
    (ready : ReadyToStep u) (agrees : AgreesExcept cs t u)
    (frame : MemoryWriteFrame t u #v[registerRegion s .rdi 40, workRegion s])
    (registers : ∀ r ∈ ([3,12,13,14,15] : List (BitVec 5)), .reg r ∉ cs)
    (hdf : Component.df ∉ cs := by component_not_mem)
    (hmxcsr : Component.mxcsr ∉ cs := by component_not_mem)
    (hfcw : Component.fcw ∉ cs := by component_not_mem) : SavedState s u := by
  have total := memoryWriteFrame_trans state.frame (ScalarFrame.Work.frame pre frame)
  refine ⟨bindingsSupported_of_ready_agrees state.bindingsSupported ready agrees,
    supportedMachine_of_ready_agrees state.machine ready agrees,
    ScalarFrame.loaded_of_frame pre total,
    agrees.directionFlagClear hdf state.directionFlag,
    fun a ha => agrees.grow a (state.allocated a ha), total, ?_,
    (agrees.read (r := 3) (n := 64) (registers 3 (by simp))).trans state.rbx,
    (agrees.mxcsr hmxcsr).trans state.mxcsr, (agrees.fcw hfcw).trans state.fp87,
    state.saved.after_frame pre frame⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (agrees.read (r := 12) (n := 64) (registers 12 (by simp))).trans
      (state.registers .r12 (by simp))
  · exact (agrees.read (r := 13) (n := 64) (registers 13 (by simp))).trans
      (state.registers .r13 (by simp))
  · exact (agrees.read (r := 14) (n := 64) (registers 14 (by simp))).trans
      (state.registers .r14 (by simp))
  · exact (agrees.read (r := 15) (n := 64) (registers 15 (by simp))).trans
      (state.registers .r15 (by simp))

theorem FrameState.of_registers [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {cs : List Component} (pre : Pre s boundary) (state : FrameState s t)
    (ready : ReadyToStep u) (agrees : AgreesExcept cs t u)
    (registers : ∀ r ∈ ([3,4,12,13,14,15] : List (BitVec 5)), .reg r ∉ cs)
    (memory : ∀ c ∈ cs, ∀ a, ¬ c.Covers a)
    (hdf : Component.df ∉ cs := by component_not_mem)
    (hmxcsr : Component.mxcsr ∉ cs := by component_not_mem)
    (hfcw : Component.fcw ∉ cs := by component_not_mem) : FrameState s u := by
  refine ⟨state.toSavedState.after_agrees pre ready agrees ?_ ?_ hdf hmxcsr hfcw,
    (agrees.read (r := 4) (n := 64) (registers 4 (by simp))).trans state.rsp⟩
  · intro a _
    exact congrArg (fun m : Ram => m[a]?) (agrees.external memory)
  · intro r hr
    apply registers
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp

end P256.Proofs.Field.Inverse
