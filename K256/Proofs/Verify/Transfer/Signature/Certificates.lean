import K256.Proofs.Verify.Transfer.Signature.Blocks
import K256.Proofs.Verify.Transfer.Signature.Labels
import K256.Proofs.LIR.Program
import K256.Proofs.Verify.LIR.Program

namespace K256.Proofs.Verify.Transfer.Signature

open K256.Proofs.CFG K256.Proofs.Lift X86.Machine

abbrev ParserBlock (x : Proofs.LIR.Label) (y : Verify.LIR.Label) : Prop :=
  ∀ (d : Dialect Op Value Ram), BlockMatches Verify.LIR.program d labelPair Proofs.LIR.live
    Proofs.LIR.retLive 0 (Proofs.LIR.live x) (Proofs.LIR.program.blocks x) (Verify.LIR.program.blocks y)


set_option maxRecDepth 4096 in
set_option maxHeartbeats 6000000 in
theorem matchedAt (x : Proofs.LIR.Label) :
    ∀ t, labelTest x = some t → ParserBlock x t.target := by
  obtain ⟨g⟩ := x
  cases g <;> intro t ht <;> cases ht <;> intro d
  case l127e94 =>
    apply matchesLet rfl (by decide) (by decide)
    apply matchesLet rfl (by decide) (by decide)
    apply matchesJumpBoundary (skip := 2) (by decide +kernel)
    exact matchesBlocks rfl (by decide) rfl (by decide +kernel)
  case l12962f =>
    apply matchesLet rfl (by decide) (by decide)
    apply matchesJumpBoundary (skip := 1) (by decide +kernel)
    exact matchesBlocks rfl (by decide) rfl (by decide +kernel)
  case l12974b =>
    apply matchesLet rfl (by decide) (by decide)
    apply matchesJumpBoundary (skip := 1) (by decide +kernel)
    exact matchesBlocks rfl (by decide) rfl (by decide +kernel)
  all_goals exact matchesBlocks rfl (by decide) rfl (by decide +kernel)

end K256.Proofs.Verify.Transfer.Signature
