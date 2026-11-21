import ChaCha20Poly1305.Proofs.Poly1305.Callee101e30.Defs

namespace ChaCha20Poly1305.Proofs.Poly1305.Callee101e30

set_option linter.unusedSimpArgs false

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Standards.RFC.ChaCha20Poly1305
open ChaCha20Poly1305.Spec.Program ChaCha20Poly1305.Proofs.Poly1305State
  ChaCha20Poly1305.Proofs.Common
open ChaCha20Poly1305.Proofs.MemoryRoutines.Machine ChaCha20Poly1305.Proofs.Poly1305.BlockArith

def bytes41 : List UInt8 :=
  [0x4c, 0x89, 0xfe, 0x49, 0x0f, 0xaf, 0xf0, 0x48, 0x89, 0xd5, 0x48, 0x0f, 0xaf, 0xeb, 0x48, 0x01,
    0xf5, 0x4c, 0x89, 0xe6, 0x49, 0x0f, 0xaf, 0xf1, 0x49, 0x89, 0xcd, 0x4c, 0x0f, 0xaf, 0xe8,
    0x49, 0x01, 0xf5, 0x49, 0x01, 0xed, 0x41, 0x8b, 0x6a, 0x14, 0x44, 0x8d, 0x5c, 0xad, 0x00,
    0x4c, 0x0f, 0xaf, 0xdf, 0x4d, 0x01, 0xeb]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seg41 [Bindings] (boundary : ReturnBoundary) (e : Env)
    (hne : ∀ pc : BitVec 64, 0x101ab0 ≤ pc.toNat → pc.toNat < 0x101cd2 → pc ≠ boundary.rip) :
    Seg boundary e 0x101b42 0x101b77 (cut41 e) (cut56 e) := by
  refine Seg.of_block (bytes := bytes41) (E := ?E) ?blk ?hsub ?post
  case blk =>
    refine AdvancesBlock.block_first ?k (mov_r64_r64_effect_step 0x101b42 0x4c 0xfe (by e30_dec) (by e30_dec)) ?sub ?pre ?av ?boundary
    case sub => exact codeRange_mem_of_take (by decide +kernel)
    case pre =>
      intro s hP
      exact hP.1
    case av =>
      intro s hP
      x86_avoid
    case boundary => intro _ _; exact hne 0x101b45 (by decide) (by decide)
    e30_then (imul_r64_r64_effect_step 0x101b45 0x49 (by e30_dec) 0xf0 (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101b42) (all := bytes41) 3 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101b49 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (mov_r64_r64_effect_step 0x101b49 0x48 0xd5 (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101b42) (all := bytes41) 7 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101b4c (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (imul_r64_r64_effect_step 0x101b4c 0x48 (by e30_dec) 0xeb (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101b42) (all := bytes41) 10 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101b50 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (add_r64_r64_effect_step 0x101b50 0x48 0xf5 (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101b42) (all := bytes41) 14 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101b53 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (mov_r64_r64_effect_step 0x101b53 0x4c 0xe6 (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101b42) (all := bytes41) 17 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101b56 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (imul_r64_r64_effect_step 0x101b56 0x49 (by e30_dec) 0xf1 (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101b42) (all := bytes41) 20 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101b5a (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (mov_r64_r64_effect_step 0x101b5a 0x49 0xcd (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101b42) (all := bytes41) 24 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101b5d (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (imul_r64_r64_effect_step 0x101b5d 0x4c (by e30_dec) 0xe8 (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101b42) (all := bytes41) 27 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101b61 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (add_r64_r64_effect_step 0x101b61 0x49 0xf5 (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101b42) (all := bytes41) 31 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101b64 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (add_r64_r64_effect_step 0x101b64 0x49 0xed (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101b42) (all := bytes41) 34 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101b67 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (mov_r32_m32_effect_step 0x101b67 0x41 (by e30_dec) 5 (.base 10 (.d8 0x14)) (by e30_dec) (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101b42) (all := bytes41) 37 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101b6b (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by e30_norm) (by x86_addr_obs) ?_,
        Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
      try e30_norm
      exact readable_at hP.2.1.rRead 4 4 (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); have h1 := (snap_reg (snap_drop hP.2.2)); (try e30_norm at h0 h1); (try simp only [h0, h1]) <;> e30_addr)
    e30_then (lea_r32_rex_effect_step 0x101b6b 0x44 (by e30_dec) 3 (.sib 5 (some 5) 2 (.d8 0x0)) (by e30_dec) (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101b42) (all := bytes41) 41 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101b70 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (imul_r64_r64_effect_step 0x101b70 0x4c (by e30_dec) 0xdf (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101b42) (all := bytes41) 46 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101b74 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (add_r64_r64_effect_step 0x101b74 0x4d 0xeb (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101b42) (all := bytes41) 50 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101b77 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    exact id
  case hsub => exact program_text_subset (bytes := bytes41) 0x1b42 (by decide +kernel) (by decide +kernel)
  case post =>
    intro s t hP hH
    obtain ⟨_, hF, hW⟩ := hP
    simp only [cut41, Write.AllHold] at hW
    obtain ⟨hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8, hw9, hw10, hw11, hw12, hw13, hw14, hw15, hw16, hw17, hw18, hw19, hw20, hw21⟩ := hW
    e30_norm at hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8 hw9 hw10 hw11 hw12 hw13 hw14 hw15 hw16 hw17 hw18 hw19 hw20 hw21
    have ho := hH.obsAfter (by e30_norm [List.forall_mem_cons, List.forall_mem_nil, List.forall_mem_append]) true
    refine ⟨?_, ?_, ?_⟩
    · rw [hH.rip]; e30_norm
    · simp only [cut56, c56_r5, c56_r11, Write.AllHold, ← ho.read_reg, ← ho.read_mem]
      e30_norm
      try simp only [← Operand.setWidth_read_reg64 (m := 32), ← Operand.setWidth_read_reg64 (m := 8)]
      try simp only [hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8, hw9, hw10, hw11, hw12, hw13, hw14, hw15, hw16, hw17, hw18, hw19, hw20, hw21]
      try e30_clean
      all_goals have hsp := hF.spNat; have hstn := hF.stNat; have hbpn := hF.bpNat
      all_goals have hsta := hF.stApart; have hbpa := hF.bpApart
      all_goals try simp (disch := e30_apart) only [memLoad_memStore_of_rangeApart]
      all_goals have rv0 := hF.rv0; have rv1 := hF.rv1; have rv2 := hF.rv2; have rv3 := hF.rv3; have rv4 := hF.rv4; have hv0 := hF.hv0; have hv1 := hF.hv1; have hv2 := hF.hv2; have hv3 := hF.hv3; have hv4 := hF.hv4; have wv0 := hF.wv0; have wv1 := hF.wv1; have wv2 := hF.wv2; have wv3 := hF.wv3; have wv4 := hF.wv4
      all_goals try e30_norm at rv0 rv1 rv2 rv3 rv4 hv0 hv1 hv2 hv3 hv4 wv0 wv1 wv2 wv3 wv4
      all_goals try simp only [memLoad_external, rv0, rv1, rv2, rv3, rv4, hv0, hv1, hv2, hv3, hv4, wv0, wv1, wv2, wv3, wv4, hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8, hw9, hw10, hw11, hw12, hw13, hw14, hw15, hw16, hw17, hw18, hw19, hw20, hw21]
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
        try simp only [hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8, hw9, hw10, hw11, hw12, hw13, hw14, hw15, hw16, hw17, hw18, hw19, hw20, hw21]
        try e30_norm
        repeat' apply And.intro
        all_goals first
          | exact fun h => cover_stack hsp (by bv_omega) h
          | exact fun h => absurd h (by simp only [Component.Covers, not_false_eq_true])

end ChaCha20Poly1305.Proofs.Poly1305.Callee101e30
