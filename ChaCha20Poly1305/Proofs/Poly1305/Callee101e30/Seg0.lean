import ChaCha20Poly1305.Proofs.Poly1305.Callee101e30.Defs

namespace ChaCha20Poly1305.Proofs.Poly1305.Callee101e30

set_option linter.unusedSimpArgs false

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Standards.RFC.ChaCha20Poly1305
open ChaCha20Poly1305.Spec.Program ChaCha20Poly1305.Proofs.Poly1305State
  ChaCha20Poly1305.Proofs.Common
open ChaCha20Poly1305.Proofs.MemoryRoutines.Machine ChaCha20Poly1305.Proofs.Poly1305.BlockArith

def bytes0 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x83, 0xec, 0x28, 0x49, 0x89,
    0xfa, 0x80, 0xf2, 0x01, 0x0f, 0xb6, 0xfa, 0xc1, 0xe7, 0x18]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seg0 [Bindings] (boundary : ReturnBoundary) (e : Env)
    (hne : ∀ pc : BitVec 64, 0x101ab0 ≤ pc.toNat → pc.toNat < 0x101cd2 → pc ≠ boundary.rip) :
    Seg boundary e 0x101ab0 0x101aca (cut0 e) (cut11 e) := by
  refine Seg.of_block (bytes := bytes0) (E := ?E) ?blk ?hsub ?post
  case blk =>
    refine AdvancesBlock.block_first ?k (push_r64_effect_step 0x101ab0 0x55 (by e30_dec)) ?sub ?pre ?av ?boundary
    case sub => exact codeRange_mem_of_take (by decide +kernel)
    case pre =>
      intro s hP
      refine ⟨hP.1, ?_, ?_⟩
      · exact writable_at hP.2.1.stack 80 8 (by decide) (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); (try e30_norm at h0); (try simp only [h0]) <;> e30_addr)
      · exact apart_at hP.2.1.stack 80 8 (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); (try e30_norm at h0); (try simp only [h0]) <;> e30_addr) 0x101ab0 0 1 (by decide) (by decide)
    case av =>
      intro s hP
      x86_avoid
      all_goals exact apart_at hP.2.1.stack 80 8 (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); (try e30_norm at h0); (try simp only [h0]) <;> e30_addr) 0x101ab0 0 26 (by decide) (by decide)
    case boundary => intro _ _; exact hne 0x101ab1 (by decide) (by decide)
    e30_then (push_r64_rex_effect_step 0x101ab1 0x41 0x57 (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101ab0) (all := bytes0) 1 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101ab3 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      refine ⟨StorePre.of_holds hH (hO true) (by e30_norm) (by x86_addr_obs) ?_ ?_,
        Effect.Local.avoids (by x86_local) (hO true) ?_⟩
      · (try e30_norm); exact writable_at hP.2.1.stack 72 8 (by decide) (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); (try e30_norm at h0); (try simp only [h0]) <;> e30_addr)
      · (try e30_norm); exact apart_at hP.2.1.stack 72 8 (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); (try e30_norm at h0); (try simp only [h0]) <;> e30_addr) 0x101ab1 1 2 (by decide) (by decide)
      · x86_avoid
        all_goals ((try e30_norm); exact apart_at hP.2.1.stack 72 8 (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); (try e30_norm at h0); (try simp only [h0]) <;> e30_addr) 0x101ab0 0 26 (by decide) (by decide))
    e30_then (push_r64_rex_effect_step 0x101ab3 0x41 0x56 (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101ab0) (all := bytes0) 3 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101ab5 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      refine ⟨StorePre.of_holds hH (hO true) (by e30_norm) (by x86_addr_obs) ?_ ?_,
        Effect.Local.avoids (by x86_local) (hO true) ?_⟩
      · (try e30_norm); exact writable_at hP.2.1.stack 64 8 (by decide) (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); (try e30_norm at h0); (try simp only [h0]) <;> e30_addr)
      · (try e30_norm); exact apart_at hP.2.1.stack 64 8 (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); (try e30_norm at h0); (try simp only [h0]) <;> e30_addr) 0x101ab3 3 2 (by decide) (by decide)
      · x86_avoid
        all_goals ((try e30_norm); exact apart_at hP.2.1.stack 64 8 (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); (try e30_norm at h0); (try simp only [h0]) <;> e30_addr) 0x101ab0 0 26 (by decide) (by decide))
    e30_then (push_r64_rex_effect_step 0x101ab5 0x41 0x55 (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101ab0) (all := bytes0) 5 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101ab7 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      refine ⟨StorePre.of_holds hH (hO true) (by e30_norm) (by x86_addr_obs) ?_ ?_,
        Effect.Local.avoids (by x86_local) (hO true) ?_⟩
      · (try e30_norm); exact writable_at hP.2.1.stack 56 8 (by decide) (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); (try e30_norm at h0); (try simp only [h0]) <;> e30_addr)
      · (try e30_norm); exact apart_at hP.2.1.stack 56 8 (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); (try e30_norm at h0); (try simp only [h0]) <;> e30_addr) 0x101ab5 5 2 (by decide) (by decide)
      · x86_avoid
        all_goals ((try e30_norm); exact apart_at hP.2.1.stack 56 8 (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); (try e30_norm at h0); (try simp only [h0]) <;> e30_addr) 0x101ab0 0 26 (by decide) (by decide))
    e30_then (push_r64_rex_effect_step 0x101ab7 0x41 0x54 (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101ab0) (all := bytes0) 7 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101ab9 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      refine ⟨StorePre.of_holds hH (hO true) (by e30_norm) (by x86_addr_obs) ?_ ?_,
        Effect.Local.avoids (by x86_local) (hO true) ?_⟩
      · (try e30_norm); exact writable_at hP.2.1.stack 48 8 (by decide) (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); (try e30_norm at h0); (try simp only [h0]) <;> e30_addr)
      · (try e30_norm); exact apart_at hP.2.1.stack 48 8 (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); (try e30_norm at h0); (try simp only [h0]) <;> e30_addr) 0x101ab7 7 2 (by decide) (by decide)
      · x86_avoid
        all_goals ((try e30_norm); exact apart_at hP.2.1.stack 48 8 (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); (try e30_norm at h0); (try simp only [h0]) <;> e30_addr) 0x101ab0 0 26 (by decide) (by decide))
    e30_then (push_r64_effect_step 0x101ab9 0x53 (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101ab0) (all := bytes0) 9 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101aba (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      refine ⟨StorePre.of_holds hH (hO true) (by e30_norm) (by x86_addr_obs) ?_ ?_,
        Effect.Local.avoids (by x86_local) (hO true) ?_⟩
      · (try e30_norm); exact writable_at hP.2.1.stack 40 8 (by decide) (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); (try e30_norm at h0); (try simp only [h0]) <;> e30_addr)
      · (try e30_norm); exact apart_at hP.2.1.stack 40 8 (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); (try e30_norm at h0); (try simp only [h0]) <;> e30_addr) 0x101ab9 9 1 (by decide) (by decide)
      · x86_avoid
        all_goals ((try e30_norm); exact apart_at hP.2.1.stack 40 8 (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); (try e30_norm at h0); (try simp only [h0]) <;> e30_addr) 0x101ab0 0 26 (by decide) (by decide))
    e30_then (sub_r64_imm8_effect_step 0x101aba 0x48 0xec 0x28 (by e30_dec) (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101ab0) (all := bytes0) 10 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101abe (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (mov_r64_r64_effect_step 0x101abe 0x49 0xfa (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101ab0) (all := bytes0) 14 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101ac1 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (xor_r8_imm8_effect_step 0x101ac1 0xf2 0x1 (by e30_dec) (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101ab0) (all := bytes0) 17 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101ac4 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (movzx_r32_r8_effect_step 0x101ac4 0xfa (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101ab0) (all := bytes0) 20 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101ac7 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (shl_r32_imm8_effect_step 0x101ac7 0xe7 0x18 (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101ab0) (all := bytes0) 23 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101aca (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    exact id
  case hsub => exact program_text_subset (bytes := bytes0) 0x1ab0 (by decide +kernel) (by decide +kernel)
  case post =>
    intro s t hP hH
    obtain ⟨_, hF, hW⟩ := hP
    simp only [cut0, Write.AllHold] at hW
    obtain ⟨hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8, hw9⟩ := hW
    e30_norm at hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8 hw9
    have ho := hH.obsAfter (by e30_norm [List.forall_mem_cons, List.forall_mem_nil, List.forall_mem_append]) true
    refine ⟨?_, ?_, ?_⟩
    · rw [hH.rip]; e30_norm
    · simp only [cut11, Write.AllHold, ← ho.read_reg, ← ho.read_mem]
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
