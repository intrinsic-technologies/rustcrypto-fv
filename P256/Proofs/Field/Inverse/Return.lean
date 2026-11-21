import P256.Proofs.Field.Inverse.State
import P256.Proofs.Field.Inverse.Epilogue

set_option autoImplicit false

namespace P256.Proofs.Field.Inverse

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program

theorem finish_return [Bindings] {s t : RamState} {boundary : ReturnBoundary} {n : Nat}
    (pre : Pre s boundary) (state : FrameState s t)
    (rip : t.RIP = 0x11422d) (run : Advances boundary n s t) :
    ∃ u, CalleeResult s u boundary 40 880 ∧ u.external = t.external := by
  have words := state.saved
  have ret : (Operand.mem ((Operand.reg 4 : Operand 64).read t+168) : Operand 64).read t =
      stackTop s := by
    rw [state.stack_address]
    simp only [BitVec.reduceSub, BitVec.sub_zero]
    exact words.2.2
  have preE : EpiloguePre t := by
    refine ⟨rip, ?_, ?_⟩
    · intro i hi
      rw [state.stack_address]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl
      all_goals simp only [BitVec.reduceSub]
      all_goals exact readable_of_grow (stack_sub_readable pre.stack (by decide) (by decide)) state.allocated
    · rw [ret]
      exact pre.returnInProgram
  obtain ⟨u,runE,ready,agrees,ip,sp,bx,bp⟩ := epilogue boundary pre.outerBoundary
    (readyToStep state.machine state.bindingsSupported) (epilogue_code state.loaded) preE
  have mem : u.external = t.external := agrees.external (by simp [Component.Covers])
  have frame : MemoryWriteFrame s u #v[registerRegion s .rdi 40, Stack.region s 880] := by
    intro a ha
    rw [mem]
    exact state.frame a ha
  refine ⟨u, ⟨⟨n+4,run.trans runE⟩, ip.trans ret, ?_,
    bindingsSupported_of_ready_agrees state.bindingsSupported ready agrees,
    supportedMachine_of_ready_agrees state.machine ready agrees, ?_,
    agrees.directionFlagClear (by simp) state.directionFlag,
    (agrees.mxcsr (by simp)).trans state.mxcsr,
    (agrees.fcw (by simp)).trans state.fp87, frame,
    ScalarFrame.loaded_of_frame pre frame,
    fun a ha => agrees.grow a (state.allocated a ha)⟩, mem⟩
  · change stackPtr u = stackPtr s+8
    rw [sp, state.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · apply bx.trans
      rw [state.stack_address]
      exact words.1
    · apply bp.trans
      rw [state.stack_address]
      exact words.2.1
    · exact (agrees.read (r := 12) (n := 64) (by simp)).trans (state.registers .r12 (by simp))
    · exact (agrees.read (r := 13) (n := 64) (by simp)).trans (state.registers .r13 (by simp))
    · exact (agrees.read (r := 14) (n := 64) (by simp)).trans (state.registers .r14 (by simp))
    · exact (agrees.read (r := 15) (n := 64) (by simp)).trans (state.registers .r15 (by simp))

end P256.Proofs.Field.Inverse
