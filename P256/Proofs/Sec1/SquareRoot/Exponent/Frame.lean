import P256.Proofs.Sec1.SquareRoot.Exponent.State
import P256.Proofs.Program.ScalarFrame.Memory

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot

open P256.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem ExponentFrame.scalarFrame [Bindings] {s t : RamState} (h : ExponentFrame s t) :
    ScalarFrame.FrameState s t 32 1584 1416 := by
  refine ⟨h.bindingsSupported, h.machine, h.loaded, h.directionFlag, h.allocated,
    h.frame, h.rsp, ?_, h.returnAddress, h.mxcsr, h.fp87⟩
  intro entry he
  simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h.saved 0 (by decide)
  · exact h.saved 1 (by decide)
  · exact h.saved 2 (by decide)
  · exact h.saved 3 (by decide)
  · exact h.saved 4 (by decide)
  · exact h.saved 5 (by decide)

theorem ExponentFrame.of_scalarFrame [Bindings] {s t : RamState}
    (h : ScalarFrame.FrameState s t 32 1584 1416)
    (output : exponentWordAt t (exponentFrameBase s + 0x2a0) (s.regValue .rdi)) :
    ExponentFrame s t := by
  refine ⟨h.rsp, h.machine, h.bindingsSupported, h.directionFlag, h.mxcsr, h.fp87,
    h.frame, h.loaded, h.allocated, h.returnAddress, ?_, output⟩
  intro i hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h.saved (.rbp, 8) (by simp [savedRegisters])
  · exact h.saved (.r15, 16) (by simp [savedRegisters])
  · exact h.saved (.r14, 24) (by simp [savedRegisters])
  · exact h.saved (.r13, 32) (by simp [savedRegisters])
  · exact h.saved (.r12, 40) (by simp [savedRegisters])
  · exact h.saved (.rbx, 48) (by simp [savedRegisters])

end P256.Proofs.Sec1.SquareRoot
