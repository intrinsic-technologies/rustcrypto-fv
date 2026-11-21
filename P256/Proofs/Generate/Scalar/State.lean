import P256.Proofs.Generate.Scalar.Interface
import P256.Proofs.Program.ScalarFrame.Memory

set_option autoImplicit false

namespace P256.Proofs.Generate.Scalar

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program

def savedRegisters : List (Syntax.Reg × Nat) :=
  [(.rbx, 40), (.r12, 32), (.r13, 24), (.r14, 16), (.r15, 8)]

abbrev workRegion (s : RamState) := ScalarFrame.Work.region s 72 40

structure State [bindings : Bindings] (s t : RamState) : Prop where
  bindingsSupported : MachineRamUnitStrideDecodable bindings t
  machine : SupportedIntegerMachineState bindings.processor t
  loaded : ProgramLoaded t
  directionFlag : DirectionFlagUnset t
  allocated : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome
  frame : MemoryWriteFrame s t #v[registerRegion s .rdi 33, Stack.region s 72]
  rbp : t.regValue .rbp = s.regValue .rbp
  saved : ∀ entry ∈ savedRegisters,
    memLoad t.external (stackPtr s - BitVec.ofNat 64 entry.2) 64 = s.regValue entry.1
  returnAddress : memLoad t.external (stackPtr s) 64 = (returnBoundary s).rip
  mxcsr : t.MXCSR = s.MXCSR
  fp87 : t.FP87_Control = s.FP87_Control

theorem State.after_agrees [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {cs : List Component} (pre : Pre s boundary) (state : State s t)
    (ready : ReadyToStep u) (agrees : AgreesExcept cs t u)
    (frame : MemoryWriteFrame t u #v[registerRegion s .rdi 33, workRegion s])
    (hbp : Component.reg 5 ∉ cs)
    (hdf : Component.df ∉ cs := by component_not_mem)
    (hmxcsr : Component.mxcsr ∉ cs := by component_not_mem)
    (hfcw : Component.fcw ∉ cs := by component_not_mem) : State s u := by
  have total := memoryWriteFrame_trans state.frame (ScalarFrame.Work.frame pre frame)
  have read (offset : Nat) (bound : offset ≤ 40) :
      memLoad u.external (stackPtr s - BitVec.ofNat 64 offset) 64 =
        memLoad t.external (stackPtr s - BitVec.ofNat 64 offset) 64 :=
    ScalarFrame.Work.read pre (by decide) frame bound (by omega)
  refine ⟨bindingsSupported_of_ready_agrees state.bindingsSupported ready agrees,
    supportedMachine_of_ready_agrees state.machine ready agrees,
    ScalarFrame.loaded_of_frame pre total,
    agrees.directionFlagClear hdf state.directionFlag,
    fun a ha => agrees.grow a (state.allocated a ha), total,
    (agrees.read (n := 64) (r := 5) hbp).trans state.rbp, ?_, ?_,
    (agrees.mxcsr hmxcsr).trans state.mxcsr, (agrees.fcw hfcw).trans state.fp87⟩
  · intro entry member
    exact (read entry.2 (by
      simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl <;> decide)).trans (state.saved entry member)
  · have ret := read 0 (by decide)
    simp only [BitVec.sub_zero] at ret
    exact ret.trans state.returnAddress

theorem State.after_registers [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {cs : List Component} (pre : Pre s boundary) (state : State s t)
    (ready : ReadyToStep u) (agrees : AgreesExcept cs t u)
    (memory : ∀ c ∈ cs, ∀ a, ¬ c.Covers a) (hbp : Component.reg 5 ∉ cs)
    (hdf : Component.df ∉ cs := by component_not_mem)
    (hmxcsr : Component.mxcsr ∉ cs := by component_not_mem)
    (hfcw : Component.fcw ∉ cs := by component_not_mem) : State s u :=
  state.after_agrees pre ready agrees
    (fun a _ => congrArg (fun m : Ram => m[a]?) (agrees.external memory)) hbp hdf hmxcsr hfcw

theorem stack_code_apart [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) {offset len codeOffset codeLen : Nat}
    (hoff : offset ≤ 72) (hlen : len ≤ offset + 8)
    (hcode : codeOffset + codeLen ≤ 118431) :
    RangeApart (stackPtr s - BitVec.ofNat 64 offset) len
      (Extracted.textAddress + BitVec.ofNat 64 codeOffset) codeLen := by
  intro i hi j hj he
  apply pre.avoids (Stack.region s 72) (by simp) _
    (ScalarFrame.stack_contains pre hoff hlen ⟨i, hi, rfl⟩) (.inl ?_)
  rw [he, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact inProgram_of_textOffset (codeOffset + j) (by omega)

end P256.Proofs.Generate.Scalar
