import ChaCha20Poly1305.Proofs.Poly1305.Callee101e30.Defs

namespace ChaCha20Poly1305.Proofs.Poly1305.Callee101e30

set_option linter.unusedSimpArgs false

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Standards.RFC.ChaCha20Poly1305
open ChaCha20Poly1305.Spec.Program ChaCha20Poly1305.Proofs.Poly1305State
  ChaCha20Poly1305.Proofs.Common
open ChaCha20Poly1305.Proofs.MemoryRoutines.Machine ChaCha20Poly1305.Proofs.Poly1305.BlockArith

def bytes24 : List UInt8 :=
  [0x44, 0x23, 0x3e, 0x45, 0x03, 0x7a, 0x24, 0x8b, 0x56, 0x03, 0x44, 0x8b, 0x66, 0x06, 0xc1, 0xea,
    0x02, 0x81, 0xe2, 0xff, 0xff, 0xff, 0x03, 0x41, 0x03, 0x52, 0x28, 0x41, 0xc1, 0xec, 0x04,
    0x41, 0x81, 0xe4, 0xff, 0xff, 0xff, 0x03, 0x45, 0x03, 0x62, 0x2c, 0x8b, 0x4e, 0x09, 0xc1,
    0xe9, 0x06, 0x41, 0x03, 0x4a, 0x30, 0x8b, 0x76, 0x0c, 0xc1, 0xee, 0x08, 0x41, 0x03, 0x7a,
    0x34, 0x01, 0xf7]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seg24 [Bindings] (boundary : ReturnBoundary) (e : Env)
    (hne : ∀ pc : BitVec 64, 0x101ab0 ≤ pc.toNat → pc.toNat < 0x101cd2 → pc ≠ boundary.rip) :
    Seg boundary e 0x101b02 0x101b42 (cut24 e) (cut41 e) := by
  refine Seg.of_block (bytes := bytes24) (E := ?E) ?blk ?hsub ?post
  case blk =>
    refine AdvancesBlock.block_first ?k (and_r32_m32_rex_effect_step 0x101b02 0x44 (by e30_dec) 7 (.base 6 .none) (by e30_dec) (by e30_dec) (by e30_dec)) ?sub ?pre ?av ?boundary
    case sub => exact codeRange_mem_of_take (by decide +kernel)
    case pre =>
      intro s hP
      refine ⟨hP.1, ?_⟩
      exact readable_at hP.2.1.blockRead 0 4 (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); have h1 := (snap_reg (snap_drop (snap_drop (snap_drop hP.2.2)))); (try e30_norm at h0 h1); (try simp only [h0, h1]) <;> e30_addr)
    case av =>
      intro s hP
      x86_avoid
    case boundary => intro _ _; exact hne 0x101b05 (by decide) (by decide)
    e30_then (add_r32_m32_rex_effect_step 0x101b05 0x45 (by e30_dec) 7 (.base 10 (.d8 0x24)) (by e30_dec) (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101b02) (all := bytes24) 3 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101b09 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by e30_norm) (by x86_addr_obs) ?_,
        Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
      try e30_norm
      exact readable_at hP.2.1.hWrite.readable 0 4 (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); have h1 := (snap_reg (snap_drop hP.2.2)); (try e30_norm at h0 h1); (try simp only [h0, h1]) <;> e30_addr)
    e30_then (mov_r32_m32_low_effect_step 0x101b09 2 (.base 6 (.d8 0x3)) (by e30_dec) (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101b02) (all := bytes24) 7 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101b0c (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by e30_norm) (by x86_addr_obs) ?_,
        Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
      try e30_norm
      exact readable_at hP.2.1.blockRead 3 4 (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); have h1 := (snap_reg (snap_drop (snap_drop (snap_drop hP.2.2)))); (try e30_norm at h0 h1); (try simp only [h0, h1]) <;> e30_addr)
    e30_then (mov_r32_m32_effect_step 0x101b0c 0x44 (by e30_dec) 4 (.base 6 (.d8 0x6)) (by e30_dec) (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101b02) (all := bytes24) 10 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101b10 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by e30_norm) (by x86_addr_obs) ?_,
        Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
      try e30_norm
      exact readable_at hP.2.1.blockRead 6 4 (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); have h1 := (snap_reg (snap_drop (snap_drop (snap_drop hP.2.2)))); (try e30_norm at h0 h1); (try simp only [h0, h1]) <;> e30_addr)
    e30_then (shr_r32_imm8_effect_step 0x101b10 0xea 0x2 (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101b02) (all := bytes24) 14 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101b13 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (and_r32_imm32_effect_step 0x101b13 0xe2 0x3ffffff (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101b02) (all := bytes24) 17 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101b19 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (add_r32_m32_rex_effect_step 0x101b19 0x41 (by e30_dec) 2 (.base 10 (.d8 0x28)) (by e30_dec) (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101b02) (all := bytes24) 23 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101b1d (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by e30_norm) (by x86_addr_obs) ?_,
        Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
      try e30_norm
      exact readable_at hP.2.1.hWrite.readable 4 4 (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); have h1 := (snap_reg (snap_drop hP.2.2)); (try e30_norm at h0 h1); (try simp only [h0, h1]) <;> e30_addr)
    e30_then (shr_r32_imm8_rex_effect_step 0x101b1d 0x41 0xec 0x4 (by e30_dec) (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101b02) (all := bytes24) 27 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101b21 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (and_r32_imm32_rex_effect_step 0x101b21 0x41 0xe4 0x3ffffff (by e30_dec) (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101b02) (all := bytes24) 31 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101b28 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (add_r32_m32_rex_effect_step 0x101b28 0x45 (by e30_dec) 4 (.base 10 (.d8 0x2c)) (by e30_dec) (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101b02) (all := bytes24) 38 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101b2c (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by e30_norm) (by x86_addr_obs) ?_,
        Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
      try e30_norm
      exact readable_at hP.2.1.hWrite.readable 8 4 (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); have h1 := (snap_reg (snap_drop hP.2.2)); (try e30_norm at h0 h1); (try simp only [h0, h1]) <;> e30_addr)
    e30_then (mov_r32_m32_low_effect_step 0x101b2c 1 (.base 6 (.d8 0x9)) (by e30_dec) (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101b02) (all := bytes24) 42 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101b2f (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by e30_norm) (by x86_addr_obs) ?_,
        Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
      try e30_norm
      exact readable_at hP.2.1.blockRead 9 4 (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); have h1 := (snap_reg (snap_drop (snap_drop (snap_drop hP.2.2)))); (try e30_norm at h0 h1); (try simp only [h0, h1]) <;> e30_addr)
    e30_then (shr_r32_imm8_effect_step 0x101b2f 0xe9 0x6 (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101b02) (all := bytes24) 45 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101b32 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (add_r32_m32_rex_effect_step 0x101b32 0x41 (by e30_dec) 1 (.base 10 (.d8 0x30)) (by e30_dec) (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101b02) (all := bytes24) 48 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101b36 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by e30_norm) (by x86_addr_obs) ?_,
        Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
      try e30_norm
      exact readable_at hP.2.1.hWrite.readable 12 4 (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); have h1 := (snap_reg (snap_drop hP.2.2)); (try e30_norm at h0 h1); (try simp only [h0, h1]) <;> e30_addr)
    e30_then (mov_r32_m32_low_effect_step 0x101b36 6 (.base 6 (.d8 0xc)) (by e30_dec) (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101b02) (all := bytes24) 52 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101b39 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by e30_norm) (by x86_addr_obs) ?_,
        Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
      try e30_norm
      exact readable_at hP.2.1.blockRead 12 4 (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); have h1 := (snap_reg (snap_drop (snap_drop (snap_drop hP.2.2)))); (try e30_norm at h0 h1); (try simp only [h0, h1]) <;> e30_addr)
    e30_then (shr_r32_imm8_effect_step 0x101b39 0xee 0x8 (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101b02) (all := bytes24) 55 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101b3c (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (add_r32_m32_rex_effect_step 0x101b3c 0x41 (by e30_dec) 7 (.base 10 (.d8 0x34)) (by e30_dec) (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101b02) (all := bytes24) 58 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101b40 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by e30_norm) (by x86_addr_obs) ?_,
        Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
      try e30_norm
      exact readable_at hP.2.1.hWrite.readable 16 4 (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); have h1 := (snap_reg (snap_drop hP.2.2)); (try e30_norm at h0 h1); (try simp only [h0, h1]) <;> e30_addr)
    e30_then (add_r32_r32_effect_step 0x101b40 0xf7 (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101b02) (all := bytes24) 62 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101b42 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    exact id
  case hsub => exact program_text_subset (bytes := bytes24) 0x1b02 (by decide +kernel) (by decide +kernel)
  case post =>
    intro s t hP hH
    obtain ⟨_, hF, hW⟩ := hP
    simp only [cut24, Write.AllHold] at hW
    obtain ⟨hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8, hw9, hw10, hw11, hw12, hw13, hw14, hw15, hw16, hw17, hw18, hw19⟩ := hW
    e30_norm at hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8 hw9 hw10 hw11 hw12 hw13 hw14 hw15 hw16 hw17 hw18 hw19
    have ho := hH.obsAfter (by e30_norm [List.forall_mem_cons, List.forall_mem_nil, List.forall_mem_append]) true
    refine ⟨?_, ?_, ?_⟩
    · rw [hH.rip]; e30_norm
    · simp only [cut41, c41_r7, c41_r1, c41_r2, c41_r12, c41_r15, Write.AllHold, ← ho.read_reg, ← ho.read_mem]
      e30_norm
      try simp only [← Operand.setWidth_read_reg64 (m := 32), ← Operand.setWidth_read_reg64 (m := 8)]
      try simp only [hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8, hw9, hw10, hw11, hw12, hw13, hw14, hw15, hw16, hw17, hw18, hw19]
      try e30_clean
      all_goals have hsp := hF.spNat; have hstn := hF.stNat; have hbpn := hF.bpNat
      all_goals have hsta := hF.stApart; have hbpa := hF.bpApart
      all_goals try simp (disch := e30_apart) only [memLoad_memStore_of_rangeApart]
      all_goals have rv0 := hF.rv0; have rv1 := hF.rv1; have rv2 := hF.rv2; have rv3 := hF.rv3; have rv4 := hF.rv4; have hv0 := hF.hv0; have hv1 := hF.hv1; have hv2 := hF.hv2; have hv3 := hF.hv3; have hv4 := hF.hv4; have wv0 := hF.wv0; have wv1 := hF.wv1; have wv2 := hF.wv2; have wv3 := hF.wv3; have wv4 := hF.wv4
      all_goals try e30_norm at rv0 rv1 rv2 rv3 rv4 hv0 hv1 hv2 hv3 hv4 wv0 wv1 wv2 wv3 wv4
      all_goals try simp only [memLoad_external, rv0, rv1, rv2, rv3, rv4, hv0, hv1, hv2, hv3, hv4, wv0, wv1, wv2, wv3, wv4, hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8, hw9, hw10, hw11, hw12, hw13, hw14, hw15, hw16, hw17, hw18, hw19]
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
        try simp only [hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8, hw9, hw10, hw11, hw12, hw13, hw14, hw15, hw16, hw17, hw18, hw19]
        try e30_norm
        repeat' apply And.intro
        all_goals first
          | exact fun h => cover_stack hsp (by bv_omega) h
          | exact fun h => absurd h (by simp only [Component.Covers, not_false_eq_true])

end ChaCha20Poly1305.Proofs.Poly1305.Callee101e30
