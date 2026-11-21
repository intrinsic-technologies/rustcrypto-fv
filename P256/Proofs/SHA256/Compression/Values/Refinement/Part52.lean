import P256.Proofs.SHA256.Compression.Values.Refinement.Basic
import P256.Proofs.SHA256.Compression.Values.Program
import P256.Proofs.SHA256.Compression.Safety.Positions
import P256.Proofs.SHA256.Compression.Decoded.Part52

set_option autoImplicit false

namespace P256.Proofs.SHA256.Compression.Values.Refinement

open P256.Proofs.Common.SHA256.Compression

open X86 X86.Machine X86.UserProcess X86Proofs

set_option maxRecDepth 4096 in
theorem part52 [Bindings] (initial : RamState) :
    TraceRefinement initial Decoded.part52 Program.part52
      Safety.before52 Safety.after52 Safety.positions52 := by
  unfold Decoded.part52 Program.part52 Safety.before52 Safety.after52 Safety.positions52
  apply TraceRefinement.cons
  · apply step (by decide) (by decide)
    intro model state
    simp only [writes, source32, contextOfRam, Address.value]
    rw [← state.rsp]
    first | rfl | simp only [BitVec.add_zero]
  exact .nil _

end P256.Proofs.SHA256.Compression.Values.Refinement
