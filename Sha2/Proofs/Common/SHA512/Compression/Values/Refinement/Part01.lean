import Sha2.Proofs.Common.SHA512.Compression.Values.Simulation
import Sha2.Proofs.Common.SHA512.Compression.Values.Refinement.Part00
import Sha2.Proofs.Common.SHA512.Compression.Values.Refinement.Basic
import Sha2.Proofs.Common.SHA512.Compression.Values.Program
import Sha2.Proofs.Common.SHA512.Compression.Safety.Positions
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part01

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Values.Refinement

open X86 X86.Machine X86.UserProcess X86Proofs

set_option maxRecDepth 4096 in
theorem part01 [Bindings] (initial : RamState) :
    TraceRefinement initial Decoded.part01 Program.part01
      Safety.before01 Safety.after01 Safety.positions01 := by
  unfold Decoded.part01 Program.part01 Safety.before01 Safety.after01 Safety.positions01
  apply TraceRefinement.cons
  · apply step (by decide) (by decide)
    intro model state
    simp only [writes, contextOfRam]
    rw [← state.rsp]
    first | rfl | simp only [BitVec.add_zero]
  apply TraceRefinement.cons
  · apply step (by decide) (by decide)
    intro model state
    simp only [writes, source64, contextOfRam, Address.value]
    rw [← state.pointers 6 (by decide)]
    first | rfl | simp only [BitVec.add_zero]
  apply TraceRefinement.cons
  · apply step (by decide) (by decide)
    intro model state
    rfl
  apply TraceRefinement.cons
  · apply step (by decide) (by decide)
    intro model state
    simp only [writes, contextOfRam]
    rw [← state.rsp]
    first | rfl | simp only [BitVec.add_zero]
  apply TraceRefinement.cons
  · apply step (by decide) (by decide)
    intro model state
    simp only [writes, source64, contextOfRam, Address.value]
    rw [← state.pointers 6 (by decide)]
    first | rfl | simp only [BitVec.add_zero]
  apply TraceRefinement.cons
  · apply step (by decide) (by decide)
    intro model state
    rfl
  apply TraceRefinement.cons
  · apply step (by decide) (by decide)
    intro model state
    rfl
  apply TraceRefinement.cons
  · apply step (by decide) (by decide)
    intro model state
    simp only [writes, source64, contextOfRam, Address.value]
    rw [← state.pointers 6 (by decide)]
    first | rfl | simp only [BitVec.add_zero]
  apply TraceRefinement.cons
  · apply step (by decide) (by decide)
    intro model state
    simp only [writes, contextOfRam]
    rw [← state.rsp]
    first | rfl | simp only [BitVec.add_zero]
  apply TraceRefinement.cons
  · apply step (by decide) (by decide)
    intro model state
    rfl
  apply TraceRefinement.cons
  · apply step (by decide) (by decide)
    intro model state
    rfl
  apply TraceRefinement.cons
  · apply step (by decide) (by decide)
    intro model state
    simp only [writes, source64, contextOfRam, Address.value]
    rw [← state.pointers 6 (by decide)]
    first | rfl | simp only [BitVec.add_zero]
  apply TraceRefinement.cons
  · apply step (by decide) (by decide)
    intro model state
    simp only [writes, contextOfRam]
    rw [← state.rsp]
    first | rfl | simp only [BitVec.add_zero]
  exact TraceRefinement.nil _

end Sha2.Proofs.Common.SHA512.Compression.Values.Refinement
