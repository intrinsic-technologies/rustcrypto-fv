import K256.Proofs.Generate.Generator.Multiply.Split.Multiplication.Reduction.Layout

namespace K256.Proofs.Generate.Generator.Multiply.Split.Reduction.Replay

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR K256.Proofs.Common.Tactic
  K256.Proofs.Common.Tactic.Replay K256.Proofs.Common.Point
  K256.Proofs.Sec1.Affine.Uncompressed

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1200000 in
theorem segment1 {a : Registers} {fr : Activation} {w : Vector (BitVec 64) 8}
    (rsi : a[6] = ⟨64, fr.rsi⟩) :
    Segment a fr w b_l11b5ba_1 b_l11b5ba_2 := by
  replay_segment using code_l11b5ba_1 from 98 to 144
    atoms (memoryAtoms fr w) unfold memoryAtoms framed_by writeRegions
    registers [6 => ⟨64, fr.rsi⟩, 15 => a[15], 55 => ⟨64, v55 w⟩, 73 => ⟨64, v73 w⟩,
      77 => ⟨64, v77 w⟩, 81 => ⟨64, v81 w⟩, 91 => ⟨64, v91 w⟩, 93 => ⟨64, v93 w⟩,
      95 => ⟨64, v95 w⟩, 96 => Value.ofBool (v96 w)]
    normalize [v98, v100, v101, v103, v105, v107, v109, v110, v112, v114, v116, v117, v119, v121, v123,
      v125, v126, v128, v130, v131, v133, v135, v137, v138, v140, v142]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1200000 in
theorem segment2 {a : Registers} {fr : Activation} {w : Vector (BitVec 64) 8}
    (rsi : a[6] = ⟨64, fr.rsi⟩) :
    Segment a fr w b_l11b5ba_2 b_l11b5ba_3 := by
  replay_segment using code_l11b5ba_2 from 144 to 191
    atoms (memoryAtoms fr w) unfold memoryAtoms framed_by writeRegions
    registers [6 => ⟨64, fr.rsi⟩, 53 => ⟨64, v53 w⟩, 55 => ⟨64, v55 w⟩, 73 => ⟨64, v73 w⟩,
      77 => ⟨64, v77 w⟩, 105 => ⟨64, v105 w⟩, 112 => ⟨64, v112 w⟩, 133 => ⟨64, v133 w⟩,
      137 => ⟨64, v137 w⟩, 140 => ⟨64, v140 w⟩, 142 => ⟨64, v142 w⟩]
    normalize [v144, v145, v147, v149, v151, v152, v154, v156, v158, v159, v161, v163, v165, v167, v168,
      v170, v172, v173, v175, v177, v179, v180, v182, v184, v185, v187, v189]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1200000 in
theorem segment3 {a : Registers} {fr : Activation} {w : Vector (BitVec 64) 8}
    (rsp : a[4] = ⟨64, fr.rsp - 120⟩)
    (lo : 129 ≤ fr.rsp.toNat) (hi : fr.rsp.toNat + 8 ≤ fr.rsi.toNat)
    (upper : fr.rsi.toNat + 64 ≤ 2^64) :
    Segment a fr w b_l11b5ba_3 b_l11b5ba_4 := by
  replay_segment using code_l11b5ba_3 from 191 to 236
    atoms (memoryAtoms fr w) unfold memoryAtoms framed_by writeRegions
    registers [4 => ⟨64, fr.rsp - 120⟩, 73 => ⟨64, v73 w⟩, 77 => ⟨64, v77 w⟩, 105 => ⟨64, v105 w⟩,
      140 => ⟨64, v140 w⟩, 161 => ⟨64, v161 w⟩, 187 => ⟨64, v187 w⟩, 189 => ⟨64, v189 w⟩]
    normalize [v191, v192, v194, v196, v198, v199, v201, v203, v204, v206, v208, v210, v213, v214, v216,
      v218, v220, v222, v223, v225, v227, v229, v231, v232, v234]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1200000 in
theorem segment4 {a : Registers} {fr : Activation} {w : Vector (BitVec 64) 8}
    (rsp : a[4] = ⟨64, fr.rsp - 120⟩)
    (lo : 129 ≤ fr.rsp.toNat) (hi : fr.rsp.toNat + 8 ≤ fr.rsi.toNat)
    (upper : fr.rsi.toNat + 64 ≤ 2^64) :
    Segment a fr w b_l11b5ba_4 b_l11b5ba_5 := by
  replay_segment using code_l11b5ba_4 from 236 to 283
    atoms (memoryAtoms fr w) unfold memoryAtoms framed_by writeRegions
    registers [4 => ⟨64, fr.rsp - 120⟩, 100 => ⟨64, v100 w⟩, 144 => ⟨64, v144 w⟩,
      203 => ⟨64, v203 w⟩, 210 => ⟨64, v210 w⟩, 216 => ⟨64, v216 w⟩, 218 => ⟨64, v218 w⟩,
      222 => ⟨64, v222 w⟩, 227 => ⟨64, v227 w⟩, 231 => ⟨64, v231 w⟩, 234 => ⟨64, v234 w⟩]
    normalize [v236, v238, v240, v242, v243, v245, v246, v249, v250, v252, v254, v256, v257, v259, v261,
      v262, v264, v266, v268, v269, v271, v273, v275, v277, v278, v280, v281]

end K256.Proofs.Generate.Generator.Multiply.Split.Reduction.Replay
