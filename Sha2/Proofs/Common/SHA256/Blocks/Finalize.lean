import Sha2.Proofs.Common.SHA256.Finalize.Contract
import Sha2.Proofs.Common.SHA256.Blocks.Finalize.Heads
import Sha2.Proofs.Common.SHA256.Blocks.Finalize.Lower
import Sha2.Proofs.Common.SHA256.Blocks.Finalize.Mark
import Sha2.Proofs.Common.SHA256.Blocks.Finalize.Branch
import Sha2.Proofs.Common.SHA256.Blocks.Finalize.Setup

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Finalize

open Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

theorem blockContracts [Bindings] (L : Layout) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) (flow : Flow L) (code : CodeFacts L) :
    BlockContracts L boundary := by
  refine ⟨Mark.run L.entry L.variant boundary outside (code.inside .mark),
    Branch.run L.branch L.variant L.branchDisp boundary outside (code.inside .branch) ?_,
    FirstHead.run L.firstHead L.variant boundary outside (code.inside .firstHead),
    fun p inside => Lower.run p L.variant boundary outside inside,
    LastHead.run L.lastHead L.variant boundary outside (code.inside .lastHead),
    fun p last inside => Setup.run p L.variant last boundary outside inside⟩
  rw [flow.branchTaken]
  have lengthInProgram := code.inside .length 0 (Nat.zero_le _)
  change InProgram (L.length + 0#64) at lengthInProgram
  simpa only [BitVec.add_zero] using lengthInProgram

end Sha2.Proofs.Common.SHA256.Finalize
