import ChaCha20Poly1305.Proofs.Poly1305.Callee101e30.Defs

namespace ChaCha20Poly1305.Proofs.Poly1305.Callee101e30

set_option linter.unusedSimpArgs false

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Standards.RFC.ChaCha20Poly1305
open ChaCha20Poly1305.Spec.Program ChaCha20Poly1305.Proofs.Poly1305State
  ChaCha20Poly1305.Proofs.Common
open ChaCha20Poly1305.Proofs.MemoryRoutines.Machine ChaCha20Poly1305.Proofs.Poly1305.BlockArith

def bytes112 : List UInt8 :=
  [0x4c, 0x89, 0xd8, 0x48, 0xc1, 0xe8, 0x1a, 0x41, 0x81, 0xe3, 0xff, 0xff, 0xff, 0x03, 0x41, 0x89,
    0xc0, 0x4c, 0x03, 0x44, 0x24, 0x08, 0x4c, 0x89, 0xc0, 0x48, 0xc1, 0xe8, 0x1a, 0x41, 0x81,
    0xe0, 0xff, 0xff, 0xff, 0x03, 0x41, 0x89, 0xc1, 0x4c, 0x03, 0x0c, 0x24, 0x4c, 0x89, 0xc8,
    0x48, 0xc1, 0xe8, 0x1a]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seg112 [Bindings] (boundary : ReturnBoundary) (e : Env)
    (hne : ∀ pc : BitVec 64, 0x101ab0 ≤ pc.toNat → pc.toNat < 0x101cd2 → pc ≠ boundary.rip) :
    Seg boundary e 0x101c3f 0x101c71 (cut112 e) (cut124 e) := by
  refine Seg.of_block (bytes := bytes112) (E := ?E) ?blk ?hsub ?post
  case blk =>
    refine AdvancesBlock.block_first ?k (mov_r64_r64_effect_step 0x101c3f 0x4c 0xd8 (by e30_dec) (by e30_dec)) ?sub ?pre ?av ?boundary
    case sub => exact codeRange_mem_of_take (by decide +kernel)
    case pre =>
      intro s hP
      exact hP.1
    case av =>
      intro s hP
      x86_avoid
    case boundary => intro _ _; exact hne 0x101c42 (by decide) (by decide)
    e30_then (shr_r64_imm8_effect_step 0x101c42 0x48 0xe8 0x1a (by e30_dec) (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101c3f) (all := bytes112) 3 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101c46 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (and_r32_imm32_rex_effect_step 0x101c46 0x41 0xe3 0x3ffffff (by e30_dec) (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101c3f) (all := bytes112) 7 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101c4d (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (mov_r32_r32_rex_effect_step 0x101c4d 0x41 0xc0 (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101c3f) (all := bytes112) 14 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101c50 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (add_r64_m64_effect_step 0x101c50 0x4c (by e30_dec) 0 (.sib 4 none 0 (.d8 0x8)) (by e30_dec) (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101c3f) (all := bytes112) 17 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101c55 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by e30_norm) (by x86_addr_obs) ?_,
        Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
      try e30_norm
      exact readable_at hP.2.1.stack.readable 8 8 (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); (try e30_norm at h0); (try simp only [h0]) <;> e30_addr)
    e30_then (mov_r64_r64_effect_step 0x101c55 0x4c 0xc0 (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101c3f) (all := bytes112) 22 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101c58 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (shr_r64_imm8_effect_step 0x101c58 0x48 0xe8 0x1a (by e30_dec) (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101c3f) (all := bytes112) 25 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101c5c (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (and_r32_imm32_rex_effect_step 0x101c5c 0x41 0xe0 0x3ffffff (by e30_dec) (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101c3f) (all := bytes112) 29 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101c63 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (mov_r32_r32_rex_effect_step 0x101c63 0x41 0xc1 (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101c3f) (all := bytes112) 36 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101c66 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (add_r64_m64_effect_step 0x101c66 0x4c (by e30_dec) 1 (.sib 4 none 0 .none) (by e30_dec) (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101c3f) (all := bytes112) 39 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101c6a (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by e30_norm) (by x86_addr_obs) ?_,
        Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
      try e30_norm
      exact readable_at hP.2.1.stack.readable 0 8 (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); (try e30_norm at h0); (try simp only [h0]) <;> e30_addr)
    e30_then (mov_r64_r64_effect_step 0x101c6a 0x4c 0xc8 (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101c3f) (all := bytes112) 43 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101c6d (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (shr_r64_imm8_effect_step 0x101c6d 0x48 0xe8 0x1a (by e30_dec) (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101c3f) (all := bytes112) 46 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101c71 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    exact id
  case hsub => exact program_text_subset (bytes := bytes112) 0x1c3f (by decide +kernel) (by decide +kernel)
  case post =>
    intro s t hP hH
    obtain ⟨_, hF, hW⟩ := hP
    simp only [cut112, Write.AllHold] at hW
    obtain ⟨hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8, hw9, hw10, hw11, hw12⟩ := hW
    e30_norm at hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8 hw9 hw10 hw11 hw12
    have ho := hH.obsAfter (by e30_norm [List.forall_mem_cons, List.forall_mem_nil, List.forall_mem_append]) true
    refine ⟨?_, ?_, ?_⟩
    · rw [hH.rip]; e30_norm
    · simp only [cut124, c124_r0, c124_r8, c124_r9, c124_r11, Write.AllHold, ← ho.read_reg, ← ho.read_mem]
      e30_norm
      try simp only [← Operand.setWidth_read_reg64 (m := 32), ← Operand.setWidth_read_reg64 (m := 8)]
      try simp only [hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8, hw9, hw10, hw11, hw12]
      try e30_clean
      all_goals have hsp := hF.spNat; have hstn := hF.stNat; have hbpn := hF.bpNat
      all_goals have hsta := hF.stApart; have hbpa := hF.bpApart
      all_goals try simp (disch := e30_apart) only [memLoad_memStore_of_rangeApart]
      all_goals have rv0 := hF.rv0; have rv1 := hF.rv1; have rv2 := hF.rv2; have rv3 := hF.rv3; have rv4 := hF.rv4; have hv0 := hF.hv0; have hv1 := hF.hv1; have hv2 := hF.hv2; have hv3 := hF.hv3; have hv4 := hF.hv4; have wv0 := hF.wv0; have wv1 := hF.wv1; have wv2 := hF.wv2; have wv3 := hF.wv3; have wv4 := hF.wv4
      all_goals try e30_norm at rv0 rv1 rv2 rv3 rv4 hv0 hv1 hv2 hv3 hv4 wv0 wv1 wv2 wv3 wv4
      all_goals try simp only [memLoad_external, rv0, rv1, rv2, rv3, rv4, hv0, hv1, hv2, hv3, hv4, wv0, wv1, wv2, wv3, wv4, hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8, hw9, hw10, hw11, hw12]
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
        try simp only [hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8, hw9, hw10, hw11, hw12]
        try e30_norm
        repeat' apply And.intro
        all_goals first
          | exact fun h => cover_stack hsp (by bv_omega) h
          | exact fun h => absurd h (by simp only [Component.Covers, not_false_eq_true])

end ChaCha20Poly1305.Proofs.Poly1305.Callee101e30
