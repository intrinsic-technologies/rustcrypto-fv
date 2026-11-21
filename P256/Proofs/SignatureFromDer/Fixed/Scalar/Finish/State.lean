import P256.Proofs.SignatureFromDer.Fixed.Scalar.RangeState

set_option autoImplicit false

namespace P256.Proofs.SignatureFromDer.Fixed.Scalar.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Program.ScalarFrame hiding FrameState

structure Stage [Bindings] (s t : RamState) (boundary : ReturnBoundary) : Prop
    extends FrameState s t where
  execution : ∃ fuel, Advances boundary fuel s t
  output : t.regValue .rbx = s.regValue .rdi

theorem Stage.after [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {cs : List Component} {fuel : Nat}
    (pre : CalleePre s boundary 0x10fa20 32 40 288) (state : Stage s t boundary)
    (run : Advances boundary fuel t u) (ready : ReadyToStep u)
    (agrees : AgreesExcept cs t u)
    (writes : WritesWithin cs #v[registerRegion s .rdi 40, Program.ScalarFrame.workRegion s 288])
    (rsp : stackPtr u = stackPtr s - 152) (rbx : .reg 3 ∉ cs)
    (hdf : Component.df ∉ cs := by component_not_mem)
    (hmxcsr : Component.mxcsr ∉ cs := by component_not_mem)
    (hfcw : Component.fcw ∉ cs := by component_not_mem) : Stage s u boundary := by
  have memory := agrees.memoryWriteFrame writes
  have total := memoryWriteFrame_trans state.frame (output_work_frame pre memory)
  obtain ⟨n, hn⟩ := state.execution
  refine { bindingsSupported := P256.Proofs.Program.bindingsSupported_of_ready_agrees state.bindingsSupported ready agrees
           machine := supportedMachine_of_ready_agrees state.machine ready agrees
           loaded := loaded_of_frame pre total
           directionFlag := agrees.directionFlagClear (by component_not_mem) state.directionFlag
           allocated := fun a ha => agrees.grow a (state.allocated a ha)
           frame := total
           rsp := rsp
           saved := ?_
           returnAddress := ?_
           mxcsr := (agrees.mxcsr (by component_not_mem)).trans state.mxcsr
           fp87 := (agrees.fcw (by component_not_mem)).trans state.fp87
           execution := ⟨n + fuel, hn.trans run⟩
           output := (agrees.read (n := 64) (r := 3) rbx).trans state.output }
  · intro entry he
    have bound : entry.2 ≤ 48 := by
      simp only [P256.Proofs.Program.savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (output_work_read pre (by decide) memory bound (by omega)).trans (state.saved entry he)
  · have h := output_work_read pre (by decide) memory (offset := 0) (n := 64) (by decide) (by decide)
    simp only [BitVec.sub_zero] at h
    exact h.trans state.returnAddress

theorem Stage.after_registers [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {cs : List Component} {fuel : Nat} (state : Stage s t boundary)
    (run : Advances boundary fuel t u) (ready : ReadyToStep u)
    (agrees : AgreesExcept cs t u)
    (memory : ∀ c ∈ cs, ∀ a, ¬ c.Covers a) (rsp : .reg 4 ∉ cs) (rbx : .reg 3 ∉ cs)
    (hdf : Component.df ∉ cs := by component_not_mem)
    (hmxcsr : Component.mxcsr ∉ cs := by component_not_mem)
    (hfcw : Component.fcw ∉ cs := by component_not_mem) :
    Stage s u boundary := by
  obtain ⟨n, hn⟩ := state.execution
  exact ⟨state.toFrameState.after_registers ready agrees memory rsp,
    ⟨n + fuel, hn.trans run⟩, (agrees.read (n := 64) (r := 3) rbx).trans state.output⟩

end P256.Proofs.SignatureFromDer.Fixed.Scalar.Finish
