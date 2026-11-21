import Sha2.Proofs.Common.SHA512.Compression.Values.Simulation
import Sha2.Proofs.Common.SHA512.Compression.Values.Refinement.Part07
import Sha2.Proofs.Common.SHA512.Compression.Values.Refinement.Basic
import Sha2.Proofs.Common.SHA512.Compression.Values.Program
import Sha2.Proofs.Common.SHA512.Compression.Safety.Positions
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part08

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Values.Refinement

open X86 X86.Machine X86.UserProcess X86Proofs

set_option maxRecDepth 4096 in
theorem part08 [Bindings] (initial : RamState) :
    TraceRefinement initial Decoded.part08 Program.part08
      Safety.before08 Safety.after08 Safety.positions08 := by
  unfold Decoded.part08 Program.part08 Safety.before08 Safety.after08 Safety.positions08
  apply TraceRefinement.cons
  · apply step (by decide) (by decide)
    intro model state
    rfl
  apply TraceRefinement.cons
  · apply step (by decide) (by decide)
    intro model state
    simp only [writes, source64, contextOfRam, Address.value]
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
    simp only [writes, contextOfRam]
    rw [← state.rsp]
    first | rfl | simp only [BitVec.add_zero]
  exact TraceRefinement.nil _

end Sha2.Proofs.Common.SHA512.Compression.Values.Refinement
