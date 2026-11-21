import Sha2.Proofs.Common.SHA512.Compression.Values.Simulation
import Sha2.Proofs.Common.SHA512.Compression.Values.Refinement.Part02
import Sha2.Proofs.Common.SHA512.Compression.Values.Refinement.Basic
import Sha2.Proofs.Common.SHA512.Compression.Values.Program
import Sha2.Proofs.Common.SHA512.Compression.Safety.Positions
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part03

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Values.Refinement

open X86 X86.Machine X86.UserProcess X86Proofs

set_option maxRecDepth 4096 in
theorem part03 [Bindings] (initial : RamState) :
    TraceRefinement initial Decoded.part03 Program.part03
      Safety.before03 Safety.after03 Safety.positions03 := by
  unfold Decoded.part03 Program.part03 Safety.before03 Safety.after03 Safety.positions03
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
  exact TraceRefinement.nil _

end Sha2.Proofs.Common.SHA512.Compression.Values.Refinement
