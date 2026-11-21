import K256.Proofs.Generate.Generator.Multiply.Split.Multiplication.Reduction.Layout

namespace K256.Proofs.Generate.Generator.Multiply.Split.Reduction.Replay

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR K256.Proofs.Common.Tactic
  K256.Proofs.Common.Tactic.Replay K256.Proofs.Common.Point
  K256.Proofs.Sec1.Affine.Uncompressed

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1200000 in
theorem segment0 {a : Registers} {fr : Activation} {w : Vector (BitVec 64) 8}
    (rsp : a[4] = ⟨64, fr.rsp - 120⟩) (rsi : a[6] = ⟨64, fr.rsi⟩)
    (constant : a[9] = ⟨64, 0x402da1732fc9bebf⟩)
    (lo : 129 ≤ fr.rsp.toNat) (hi : fr.rsp.toNat + 8 ≤ fr.rsi.toNat)
    (upper : fr.rsi.toNat + 64 ≤ 2^64) :
    Segment a fr w b_l11b5ba b_l11b5ba_1 := by
  replay_segment using code_l11b5ba from 53 to 98
    atoms (memoryAtoms fr w) unfold memoryAtoms framed_by writeRegions
    registers [4 => ⟨64, fr.rsp - 120⟩, 6 => ⟨64, fr.rsi⟩, 9 => ⟨64, 0x402da1732fc9bebf⟩, 10 => a[10]]
    normalize [v53, v55, v57, v59, v60, v62, v64, v66, v68, v69, v71, v73, v75, v77, v79, v81, v82, v84, v85, v88, v89, v91, v93, v95, v96]

end K256.Proofs.Generate.Generator.Multiply.Split.Reduction.Replay
