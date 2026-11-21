import Hkdf.Proofs.Common.SHA256.Compression.Values.Refinement.Basic
import Hkdf.Proofs.Common.SHA256.Compression.Values.Program
import Hkdf.Proofs.Common.SHA256.Compression.Safety.Positions
import Hkdf.Proofs.Common.SHA256.Compression.Decoded.Part38

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Values.Refinement

open X86 X86.Machine X86.UserProcess X86Proofs

set_option maxRecDepth 4096 in
theorem part38 [Bindings] (initial : RamState) :
    TraceRefinement initial Decoded.part38 Program.part38
      Safety.before38 Safety.after38 Safety.positions38 := by
  unfold Decoded.part38 Program.part38 Safety.before38 Safety.after38 Safety.positions38
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
    rfl
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
    rfl
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
    rfl
  apply TraceRefinement.cons
  · apply step (by decide) (by decide)
    intro model state
    rfl
  apply TraceRefinement.cons
  · apply step (by decide) (by decide)
    intro model state
    simp only [writes, source32, contextOfRam, Address.value]
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
    rfl
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
    rfl
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
    rfl
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
    rfl
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
    rfl
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
    rfl
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
    rfl
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
    rfl
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
    rfl
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
    rfl
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
    rfl
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
    rfl
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
    rfl
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
    rfl
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
    rfl
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
    rfl
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
    rfl
  exact .nil _

end Hkdf.Proofs.Common.SHA256.Compression.Values.Refinement
