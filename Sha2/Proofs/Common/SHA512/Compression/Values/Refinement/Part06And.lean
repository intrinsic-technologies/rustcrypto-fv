import Sha2.Proofs.Common.SHA512.Compression.Values.Simulation
import Sha2.Proofs.Common.SHA512.Compression.Values.Refinement.Part06
import Sha2.Proofs.Common.SHA512.Compression.Values.Refinement.Basic
import Sha2.Proofs.Common.SHA512.Compression.Values.Program
import Sha2.Proofs.Common.SHA512.Compression.Safety.Positions
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part06And

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Values.Refinement

open X86 X86.Machine X86.UserProcess X86Proofs

set_option maxRecDepth 4096 in
theorem part06And [Bindings] (initial : RamState) :
    TraceRefinement initial Decoded.part06And Program.part06And
      Safety.before06And Safety.after06And Safety.positions06And := by
  unfold Decoded.part06And Program.part06And Safety.before06And Safety.after06And Safety.positions06And
  apply TraceRefinement.cons
  · apply step (by decide) (by decide)
    intro model state
    simp only [writes, source64, contextOfRam, Address.value]
    rw [← state.rsp]
    first | rfl | simp only [BitVec.add_zero]
  exact TraceRefinement.nil _

end Sha2.Proofs.Common.SHA512.Compression.Values.Refinement
