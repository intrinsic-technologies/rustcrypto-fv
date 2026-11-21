import Sha2.Proofs.Common.SHA512.Compression.Values.Simulation
import Sha2.Proofs.Common.SHA512.Compression.Values.Refinement.Part19
import Sha2.Proofs.Common.SHA512.Compression.Values.Refinement.Basic
import Sha2.Proofs.Common.SHA512.Compression.Values.Program
import Sha2.Proofs.Common.SHA512.Compression.Safety.Positions
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part20

set_option autoImplicit false
namespace Sha2.Proofs.Common.SHA512.Compression.Values.Refinement
open X86 X86.Machine X86.UserProcess X86Proofs
set_option maxRecDepth 4096 in
set_option maxHeartbeats 500000 in
theorem part20_prefix10 [Bindings] (initial : RamState) :
    TraceRefinement initial ((Decoded.part20.drop 0).take 10) ((Program.part20.drop 0).take 10)
      Safety.before20 (Safety.positionOfNoRsi (0x10e719, 5)) ((Safety.positions20.drop 0).take 10) := by
  unfold Decoded.part20 Program.part20 Safety.positions20
  unfold Safety.before20
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
  simpa only [List.take] using TraceRefinement.nil _

end Sha2.Proofs.Common.SHA512.Compression.Values.Refinement
