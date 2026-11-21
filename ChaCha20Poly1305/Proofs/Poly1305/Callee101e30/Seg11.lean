import ChaCha20Poly1305.Proofs.Poly1305.Callee101e30.Defs

namespace ChaCha20Poly1305.Proofs.Poly1305.Callee101e30

set_option linter.unusedSimpArgs false

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Standards.RFC.ChaCha20Poly1305
open ChaCha20Poly1305.Spec.Program ChaCha20Poly1305.Proofs.Poly1305State
  ChaCha20Poly1305.Proofs.Common
open ChaCha20Poly1305.Proofs.MemoryRoutines.Machine ChaCha20Poly1305.Proofs.Poly1305.BlockArith

def bytes11 : List UInt8 :=
  [0x45, 0x8b, 0x42, 0x10, 0x41, 0x8b, 0x42, 0x18, 0x48, 0x89, 0x44, 0x24, 0x10, 0x41, 0x8b, 0x4a,
    0x1c, 0x48, 0x89, 0x4c, 0x24, 0x18, 0x41, 0x8b, 0x52, 0x20, 0x48, 0x89, 0x54, 0x24, 0x20,
    0x8d, 0x04, 0x80, 0x48, 0x89, 0x44, 0x24, 0x08, 0x44, 0x8d, 0x0c, 0x89, 0x4c, 0x89, 0x0c,
    0x24, 0x8d, 0x1c, 0x92, 0x41, 0xbf, 0xff, 0xff, 0xff, 0x03]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seg11 [Bindings] (boundary : ReturnBoundary) (e : Env)
    (hne : ∀ pc : BitVec 64, 0x101ab0 ≤ pc.toNat → pc.toNat < 0x101cd2 → pc ≠ boundary.rip) :
    Seg boundary e 0x101aca 0x101b02 (cut11 e) (cut24 e) := by
  refine Seg.of_block (bytes := bytes11) (E := ?E) ?blk ?hsub ?post
  case blk =>
    refine AdvancesBlock.block_first ?k (mov_r32_m32_effect_step 0x101aca 0x45 (by e30_dec) 0 (.base 10 (.d8 0x10)) (by e30_dec) (by e30_dec) (by e30_dec)) ?sub ?pre ?av ?boundary
    case sub => exact codeRange_mem_of_take (by decide +kernel)
    case pre =>
      intro s hP
      refine ⟨hP.1, ?_⟩
      exact readable_at hP.2.1.rRead 0 4 (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); have h1 := (snap_reg (snap_drop hP.2.2)); (try e30_norm at h0 h1); (try simp only [h0, h1]) <;> e30_addr)
    case av =>
      intro s hP
      x86_avoid
    case boundary => intro _ _; exact hne 0x101ace (by decide) (by decide)
    e30_then (mov_r32_m32_effect_step 0x101ace 0x41 (by e30_dec) 0 (.base 10 (.d8 0x18)) (by e30_dec) (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101aca) (all := bytes11) 4 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101ad2 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by e30_norm) (by x86_addr_obs) ?_,
        Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
      try e30_norm
      exact readable_at hP.2.1.rRead 8 4 (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); have h1 := (snap_reg (snap_drop hP.2.2)); (try e30_norm at h0 h1); (try simp only [h0, h1]) <;> e30_addr)
    e30_then (mov_m64_r64_effect_step 0x101ad2 0x48 (by e30_dec) 0 (.sib 4 none 0 (.d8 0x10)) (by e30_dec) (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101aca) (all := bytes11) 8 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101ad7 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      refine ⟨StorePre.of_holds hH (hO true) (by e30_norm) (by x86_addr_obs) ?_ ?_,
        Effect.Local.avoids (by x86_local) (hO true) ?_⟩
      · (try e30_norm); exact writable_at hP.2.1.stack 16 8 (by decide) (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); (try e30_norm at h0); (try simp only [h0]) <;> e30_addr)
      · (try e30_norm); exact apart_at hP.2.1.stack 16 8 (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); (try e30_norm at h0); (try simp only [h0]) <;> e30_addr) 0x101ad2 34 5 (by decide) (by decide)
      · x86_avoid
        all_goals ((try e30_norm); exact apart_at hP.2.1.stack 16 8 (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); (try e30_norm at h0); (try simp only [h0]) <;> e30_addr) 0x101aca 26 56 (by decide) (by decide))
    e30_then (mov_r32_m32_effect_step 0x101ad7 0x41 (by e30_dec) 1 (.base 10 (.d8 0x1c)) (by e30_dec) (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101aca) (all := bytes11) 13 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101adb (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by e30_norm) (by x86_addr_obs) ?_,
        Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
      try e30_norm
      exact readable_at hP.2.1.rRead 12 4 (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); have h1 := (snap_reg (snap_drop hP.2.2)); (try e30_norm at h0 h1); (try simp only [h0, h1]) <;> e30_addr)
    e30_then (mov_m64_r64_effect_step 0x101adb 0x48 (by e30_dec) 1 (.sib 4 none 0 (.d8 0x18)) (by e30_dec) (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101aca) (all := bytes11) 17 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101ae0 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      refine ⟨StorePre.of_holds hH (hO true) (by e30_norm) (by x86_addr_obs) ?_ ?_,
        Effect.Local.avoids (by x86_local) (hO true) ?_⟩
      · (try e30_norm); exact writable_at hP.2.1.stack 24 8 (by decide) (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); (try e30_norm at h0); (try simp only [h0]) <;> e30_addr)
      · (try e30_norm); exact apart_at hP.2.1.stack 24 8 (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); (try e30_norm at h0); (try simp only [h0]) <;> e30_addr) 0x101adb 43 5 (by decide) (by decide)
      · x86_avoid
        all_goals ((try e30_norm); exact apart_at hP.2.1.stack 24 8 (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); (try e30_norm at h0); (try simp only [h0]) <;> e30_addr) 0x101aca 26 56 (by decide) (by decide))
    e30_then (mov_r32_m32_effect_step 0x101ae0 0x41 (by e30_dec) 2 (.base 10 (.d8 0x20)) (by e30_dec) (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101aca) (all := bytes11) 22 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101ae4 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by e30_norm) (by x86_addr_obs) ?_,
        Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
      try e30_norm
      exact readable_at hP.2.1.rRead 16 4 (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); have h1 := (snap_reg (snap_drop hP.2.2)); (try e30_norm at h0 h1); (try simp only [h0, h1]) <;> e30_addr)
    e30_then (mov_m64_r64_effect_step 0x101ae4 0x48 (by e30_dec) 2 (.sib 4 none 0 (.d8 0x20)) (by e30_dec) (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101aca) (all := bytes11) 26 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101ae9 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      refine ⟨StorePre.of_holds hH (hO true) (by e30_norm) (by x86_addr_obs) ?_ ?_,
        Effect.Local.avoids (by x86_local) (hO true) ?_⟩
      · (try e30_norm); exact writable_at hP.2.1.stack 32 8 (by decide) (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); (try e30_norm at h0); (try simp only [h0]) <;> e30_addr)
      · (try e30_norm); exact apart_at hP.2.1.stack 32 8 (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); (try e30_norm at h0); (try simp only [h0]) <;> e30_addr) 0x101ae4 52 5 (by decide) (by decide)
      · x86_avoid
        all_goals ((try e30_norm); exact apart_at hP.2.1.stack 32 8 (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); (try e30_norm at h0); (try simp only [h0]) <;> e30_addr) 0x101aca 26 56 (by decide) (by decide))
    e30_then (lea_r32_effect_step 0x101ae9 0 (.sib 0 (some 0) 2 .none) (by e30_dec) (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101aca) (all := bytes11) 31 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101aec (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (mov_m64_r64_effect_step 0x101aec 0x48 (by e30_dec) 0 (.sib 4 none 0 (.d8 0x8)) (by e30_dec) (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101aca) (all := bytes11) 34 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101af1 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      refine ⟨StorePre.of_holds hH (hO true) (by e30_norm) (by x86_addr_obs) ?_ ?_,
        Effect.Local.avoids (by x86_local) (hO true) ?_⟩
      · (try e30_norm); exact writable_at hP.2.1.stack 8 8 (by decide) (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); (try e30_norm at h0); (try simp only [h0]) <;> e30_addr)
      · (try e30_norm); exact apart_at hP.2.1.stack 8 8 (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); (try e30_norm at h0); (try simp only [h0]) <;> e30_addr) 0x101aec 60 5 (by decide) (by decide)
      · x86_avoid
        all_goals ((try e30_norm); exact apart_at hP.2.1.stack 8 8 (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); (try e30_norm at h0); (try simp only [h0]) <;> e30_addr) 0x101aca 26 56 (by decide) (by decide))
    e30_then (lea_r32_rex_effect_step 0x101af1 0x44 (by e30_dec) 1 (.sib 1 (some 1) 2 .none) (by e30_dec) (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101aca) (all := bytes11) 39 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101af5 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (mov_m64_r64_effect_step 0x101af5 0x4c (by e30_dec) 1 (.sib 4 none 0 .none) (by e30_dec) (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101aca) (all := bytes11) 43 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101af9 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      refine ⟨StorePre.of_holds hH (hO true) (by e30_norm) (by x86_addr_obs) ?_ ?_,
        Effect.Local.avoids (by x86_local) (hO true) ?_⟩
      · (try e30_norm); exact writable_at hP.2.1.stack 0 8 (by decide) (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); (try e30_norm at h0); (try simp only [h0]) <;> e30_addr)
      · (try e30_norm); exact apart_at hP.2.1.stack 0 8 (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); (try e30_norm at h0); (try simp only [h0]) <;> e30_addr) 0x101af5 69 4 (by decide) (by decide)
      · x86_avoid
        all_goals ((try e30_norm); exact apart_at hP.2.1.stack 0 8 (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); (try e30_norm at h0); (try simp only [h0]) <;> e30_addr) 0x101aca 26 56 (by decide) (by decide))
    e30_then (lea_r32_effect_step 0x101af9 3 (.sib 2 (some 2) 2 .none) (by e30_dec) (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101aca) (all := bytes11) 47 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101afc (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (mov_r32_imm32_rex_effect_step 0x101afc 0x41 0xbf (by e30_dec) (by e30_dec) 0x3ffffff)
    case sub => exact codeRange_mem_of_drop (p := 0x101aca) (all := bytes11) 50 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101b02 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    exact id
  case hsub => exact program_text_subset (bytes := bytes11) 0x1aca (by decide +kernel) (by decide +kernel)
  case post =>
    intro s t hP hH
    obtain ⟨_, hF, hW⟩ := hP
    simp only [cut11, Write.AllHold] at hW
    obtain ⟨hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8, hw9⟩ := hW
    e30_norm at hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8 hw9
    have ho := hH.obsAfter (by e30_norm [List.forall_mem_cons, List.forall_mem_nil, List.forall_mem_append]) true
    refine ⟨?_, ?_, ?_⟩
    · rw [hH.rip]; e30_norm
    · simp only [cut24, c24_r0, c24_r3, c24_r8, c24_r9, c24_s56, c24_s64, c24_s72, c24_s80, c24_s88, Write.AllHold, ← ho.read_reg, ← ho.read_mem]
      e30_norm
      try simp only [← Operand.setWidth_read_reg64 (m := 32), ← Operand.setWidth_read_reg64 (m := 8)]
      try simp only [hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8, hw9]
      try e30_clean
      all_goals have hsp := hF.spNat; have hstn := hF.stNat; have hbpn := hF.bpNat
      all_goals have hsta := hF.stApart; have hbpa := hF.bpApart
      all_goals try simp (disch := e30_apart) only [memLoad_memStore_of_rangeApart]
      all_goals have rv0 := hF.rv0; have rv1 := hF.rv1; have rv2 := hF.rv2; have rv3 := hF.rv3; have rv4 := hF.rv4; have hv0 := hF.hv0; have hv1 := hF.hv1; have hv2 := hF.hv2; have hv3 := hF.hv3; have hv4 := hF.hv4; have wv0 := hF.wv0; have wv1 := hF.wv1; have wv2 := hF.wv2; have wv3 := hF.wv3; have wv4 := hF.wv4
      all_goals try e30_norm at rv0 rv1 rv2 rv3 rv4 hv0 hv1 hv2 hv3 hv4 wv0 wv1 wv2 wv3 wv4
      all_goals try simp only [memLoad_external, rv0, rv1, rv2, rv3, rv4, hv0, hv1, hv2, hv3, hv4, wv0, wv1, wv2, wv3, wv4, hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8, hw9]
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
        try simp only [hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8, hw9]
        try e30_norm
        repeat' apply And.intro
        all_goals first
          | exact fun h => cover_stack hsp (by bv_omega) h
          | exact fun h => absurd h (by simp only [Component.Covers, not_false_eq_true])

end ChaCha20Poly1305.Proofs.Poly1305.Callee101e30
