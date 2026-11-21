import ChaCha20Poly1305.Proofs.Poly1305.Callee101e30.Defs

namespace ChaCha20Poly1305.Proofs.Poly1305.Callee101e30

set_option linter.unusedSimpArgs false

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Standards.RFC.ChaCha20Poly1305
open ChaCha20Poly1305.Spec.Program ChaCha20Poly1305.Proofs.Poly1305State
  ChaCha20Poly1305.Proofs.Common
open ChaCha20Poly1305.Proofs.MemoryRoutines.Machine ChaCha20Poly1305.Proofs.Poly1305.BlockArith

def bytes124 : List UInt8 :=
  [0x89, 0xc2, 0x48, 0x01, 0xda, 0x48, 0x89, 0xd0, 0x48, 0xc1, 0xe8, 0x1a, 0x89, 0xc0, 0x48, 0x01,
    0xf8, 0x48, 0x89, 0xc1, 0x48, 0xc1, 0xe9, 0x1a, 0x8d, 0x0c, 0x89, 0x44, 0x01, 0xd9, 0x89,
    0xce, 0xc1, 0xee, 0x1a, 0x44, 0x01, 0xc6, 0x81, 0xe1, 0xff, 0xff, 0xff, 0x03]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seg124 [Bindings] (boundary : ReturnBoundary) (e : Env)
    (hne : ∀ pc : BitVec 64, 0x101ab0 ≤ pc.toNat → pc.toNat < 0x101cd2 → pc ≠ boundary.rip) :
    Seg boundary e 0x101c71 0x101c9d (cut124 e) (cut138 e) := by
  refine Seg.of_block (bytes := bytes124) (E := ?E) ?blk ?hsub ?post
  case blk =>
    refine AdvancesBlock.block_first ?k (mov_r32_r32_effect_step 0x101c71 0xc2 (by e30_dec)) ?sub ?pre ?av ?boundary
    case sub => exact codeRange_mem_of_take (by decide +kernel)
    case pre =>
      intro s hP
      exact hP.1
    case av =>
      intro s hP
      x86_avoid
    case boundary => intro _ _; exact hne 0x101c73 (by decide) (by decide)
    e30_then (add_r64_r64_effect_step 0x101c73 0x48 0xda (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101c71) (all := bytes124) 2 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101c76 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (mov_r64_r64_effect_step 0x101c76 0x48 0xd0 (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101c71) (all := bytes124) 5 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101c79 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (shr_r64_imm8_effect_step 0x101c79 0x48 0xe8 0x1a (by e30_dec) (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101c71) (all := bytes124) 8 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101c7d (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (mov_r32_r32_effect_step 0x101c7d 0xc0 (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101c71) (all := bytes124) 12 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101c7f (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (add_r64_r64_effect_step 0x101c7f 0x48 0xf8 (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101c71) (all := bytes124) 14 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101c82 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (mov_r64_r64_effect_step 0x101c82 0x48 0xc1 (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101c71) (all := bytes124) 17 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101c85 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (shr_r64_imm8_effect_step 0x101c85 0x48 0xe9 0x1a (by e30_dec) (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101c71) (all := bytes124) 20 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101c89 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (lea_r32_effect_step 0x101c89 1 (.sib 1 (some 1) 2 .none) (by e30_dec) (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101c71) (all := bytes124) 24 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101c8c (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (add_r32_r32_rex_effect_step 0x101c8c 0x44 0xd9 (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101c71) (all := bytes124) 27 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101c8f (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (mov_r32_r32_effect_step 0x101c8f 0xce (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101c71) (all := bytes124) 30 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101c91 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (shr_r32_imm8_effect_step 0x101c91 0xee 0x1a (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101c71) (all := bytes124) 32 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101c94 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (add_r32_r32_rex_effect_step 0x101c94 0x44 0xc6 (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101c71) (all := bytes124) 35 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101c97 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (and_r32_imm32_effect_step 0x101c97 0xe1 0x3ffffff (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101c71) (all := bytes124) 38 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101c9d (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    exact id
  case hsub => exact program_text_subset (bytes := bytes124) 0x1c71 (by decide +kernel) (by decide +kernel)
  case post =>
    intro s t hP hH
    obtain ⟨_, hF, hW⟩ := hP
    simp only [cut124, Write.AllHold] at hW
    obtain ⟨hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8, hw9, hw10, hw11, hw12, hw13⟩ := hW
    e30_norm at hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8 hw9 hw10 hw11 hw12 hw13
    have ho := hH.obsAfter (by e30_norm [List.forall_mem_cons, List.forall_mem_nil, List.forall_mem_append]) true
    refine ⟨?_, ?_, ?_⟩
    · rw [hH.rip]; e30_norm
    · simp only [cut138, c138_r6, c138_r0, c138_r1, c138_r2, Write.AllHold, ← ho.read_reg, ← ho.read_mem]
      e30_norm
      try simp only [← Operand.setWidth_read_reg64 (m := 32), ← Operand.setWidth_read_reg64 (m := 8)]
      try simp only [hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8, hw9, hw10, hw11, hw12, hw13]
      try e30_clean
      all_goals have hsp := hF.spNat; have hstn := hF.stNat; have hbpn := hF.bpNat
      all_goals have hsta := hF.stApart; have hbpa := hF.bpApart
      all_goals try simp (disch := e30_apart) only [memLoad_memStore_of_rangeApart]
      all_goals have rv0 := hF.rv0; have rv1 := hF.rv1; have rv2 := hF.rv2; have rv3 := hF.rv3; have rv4 := hF.rv4; have hv0 := hF.hv0; have hv1 := hF.hv1; have hv2 := hF.hv2; have hv3 := hF.hv3; have hv4 := hF.hv4; have wv0 := hF.wv0; have wv1 := hF.wv1; have wv2 := hF.wv2; have wv3 := hF.wv3; have wv4 := hF.wv4
      all_goals try e30_norm at rv0 rv1 rv2 rv3 rv4 hv0 hv1 hv2 hv3 hv4 wv0 wv1 wv2 wv3 wv4
      all_goals try simp only [memLoad_external, rv0, rv1, rv2, rv3, rv4, hv0, hv1, hv2, hv3, hv4, wv0, wv1, wv2, wv3, wv4, hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8, hw9, hw10, hw11, hw12, hw13]
      all_goals try e30_clean
      all_goals (repeat' apply And.intro)
      all_goals clear hH ho
      all_goals first | rfl | ac_rfl | bv_decide
    · have hsp := hF.spNat; have hstn := hF.stNat
      refine hH.agrees.widen ?_ ?_
      · e30_norm [Effect.components]
        simp (config := { decide := true }) only [bodyChanges, Component.isMem, List.mem_cons, Component.reg.injEq, reduceCtorEq, true_or, or_true, false_or, or_false, imp_self, implies_true, and_self, true_and, and_true, List.not_mem_nil, false_implies]
      · intro x
        e30_norm [Effect.components]
        try simp only [hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8, hw9, hw10, hw11, hw12, hw13]
        try e30_norm
        repeat' apply And.intro
        all_goals first
          | exact fun h => cover_stack hsp (by bv_omega) h
          | exact fun h => absurd h (by simp only [Component.Covers, not_false_eq_true])

end ChaCha20Poly1305.Proofs.Poly1305.Callee101e30
