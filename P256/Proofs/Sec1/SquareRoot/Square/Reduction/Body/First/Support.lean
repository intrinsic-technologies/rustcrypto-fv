import P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Stages
import P256.Proofs.Common.Memory.Readable
import P256.Proofs.Program.ScalarFrame.Memory
import P256.Proofs.Common.Encoding.Serialize.Convert.SavePointer
import P256.Proofs.Common.Field.Montgomery.Schoolbook.CarryCompose
import P256.Proofs.Common.Instructions.Imul.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.FirstRound

open P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem imulR64R64Effect_components (p : BitVec 64) (dst src : BitVec 5) (t : RamState) :
    (P256.Proofs.Common.Instructions.imulR64R64Effect p dst src t).components =
      [.reg dst, .flags, .rip] := rfl

variable [Bindings] {s t u : RamState} {boundary : ReturnBoundary}

theorem after_store (pre : ReductionPre s boundary)
    (frame : ScalarFrame.FrameState s t 32 112 112) (ready : ReadyToStep u)
    {offset : Nat} (ho : offset + 8 ≤ 64)
    (agrees : AgreesExcept [.mem (stackPtr t + BitVec.ofNat 64 offset) 8, .rip] t u) :
    ScalarFrame.FrameState s u 32 112 112 := by
  apply frame.after_effect pre.toCalleePre (by decide) ready agrees ?_ (by simp)
  intro c hc a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · refine ⟨ScalarFrame.workRegion s 112, by simp, ?_⟩
    apply ScalarFrame.work_contains pre.toCalleePre (offset := 112-offset) (len := 8)
      (by omega) (by omega)
    rw [ScalarFrame.scalar_stack_address (frameOffset := 112) frame.rsp (offset := offset) (by decide) (by omega)] at ha
    exact ha
  · exact ha.elim

theorem input_readable (pre : ReductionPre s boundary)
    (frame : ScalarFrame.FrameState s t 32 112 112) {j : Nat} (hj : j < 8) :
    MemReadable t (s.regValue .rsi + BitVec.ofNat 64 (8*j)) 8 := by
  apply readable_of_grow _ frame.allocated
  exact P256.Proofs.Common.Memory.memReadable_sub
    (memoryRegion_memReadable pre.inputBounded pre.inputAllocated (Nat.le_refl _) (Nat.le_refl _))
    (8*j) 8 (by change 8*j+8 ≤ 64; omega)

theorem modulus_readable (pre : ReductionPre s boundary)
    (frame : ScalarFrame.FrameState s t 32 112 112) {j : Nat} (hj : j < 4) :
    MemReadable t (s.regValue .rdx + BitVec.ofNat 64 (8*j)) 8 := by
  apply readable_of_grow _ frame.allocated
  exact P256.Proofs.Common.Memory.memReadable_sub
    (memoryRegion_memReadable pre.modulusBounded pre.modulusAllocated (Nat.le_refl _) (Nat.le_refl _))
    (8*j) 8 (by change 8*j+8 ≤ 32; omega)

end P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.FirstRound
