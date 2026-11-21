import ChaCha20Poly1305.Proofs.Poly1305.Callee101e30.Defs

namespace ChaCha20Poly1305.Proofs.Poly1305.Callee101e30

set_option linter.unusedSimpArgs false

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Standards.RFC.ChaCha20Poly1305
open ChaCha20Poly1305.Spec.Program ChaCha20Poly1305.Proofs.Poly1305State
  ChaCha20Poly1305.Proofs.Common
open ChaCha20Poly1305.Proofs.MemoryRoutines.Machine ChaCha20Poly1305.Proofs.Poly1305.BlockArith

def bytes138 : List UInt8 :=
  [0x41, 0x89, 0x4a, 0x24, 0x41, 0x89, 0x72, 0x28, 0x41, 0x81, 0xe1, 0xff, 0xff, 0xff, 0x03, 0x45,
    0x89, 0x4a, 0x2c, 0x81, 0xe2, 0xff, 0xff, 0xff, 0x03, 0x41, 0x89, 0x52, 0x30, 0x25, 0xff,
    0xff, 0xff, 0x03, 0x41, 0x89, 0x42, 0x34, 0x48, 0x83, 0xc4, 0x28, 0x5b, 0x41, 0x5c, 0x41,
    0x5d, 0x41, 0x5e, 0x41, 0x5f, 0x5d]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seg138 [Bindings] (boundary : ReturnBoundary) (e : Env)
    (hne : ∀ pc : BitVec 64, 0x101ab0 ≤ pc.toNat → pc.toNat < 0x101cd2 → pc ≠ boundary.rip) :
    SegF boundary e 0x101c9d 0x101cd1 (cut138 e) (cut153 e) := by
  refine SegF.of_block (bytes := bytes138) (E := ?E) ?blk ?hsub ?post
  case blk =>
    refine AdvancesBlock.block_first ?k (mov_m32_r32_effect_step 0x101c9d 0x41 (by e30_dec) 1 (.base 10 (.d8 0x24)) (by e30_dec) (by e30_dec) (by e30_dec)) ?sub ?pre ?av ?boundary
    case sub => exact codeRange_mem_of_take (by decide +kernel)
    case pre =>
      intro s hP
      refine ⟨hP.1, ?_, ?_⟩
      · exact writable_at hP.2.1.hWrite 0 4 (by decide) (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); have h1 := (snap_reg (snap_drop hP.2.2)); (try e30_norm at h0 h1); (try simp only [h0, h1]) <;> e30_addr)
      · exact apart_at hP.2.1.hWrite 0 4 (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); have h1 := (snap_reg (snap_drop hP.2.2)); (try e30_norm at h0 h1); (try simp only [h0, h1]) <;> e30_addr) 0x101c9d 493 4 (by decide) (by decide)
    case av =>
      intro s hP
      x86_avoid
      all_goals exact apart_at hP.2.1.hWrite 0 4 (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); have h1 := (snap_reg (snap_drop hP.2.2)); (try e30_norm at h0 h1); (try simp only [h0, h1]) <;> e30_addr) 0x101c9d 493 52 (by decide) (by decide)
    case boundary => intro _ _; exact hne 0x101ca1 (by decide) (by decide)
    e30_then (mov_m32_r32_effect_step 0x101ca1 0x41 (by e30_dec) 6 (.base 10 (.d8 0x28)) (by e30_dec) (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101c9d) (all := bytes138) 4 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101ca5 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      refine ⟨StorePre.of_holds hH (hO true) (by e30_norm) (by x86_addr_obs) ?_ ?_,
        Effect.Local.avoids (by x86_local) (hO true) ?_⟩
      · (try e30_norm); exact writable_at hP.2.1.hWrite 4 4 (by decide) (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); have h1 := (snap_reg (snap_drop hP.2.2)); (try e30_norm at h0 h1); (try simp only [h0, h1]) <;> e30_addr)
      · (try e30_norm); exact apart_at hP.2.1.hWrite 4 4 (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); have h1 := (snap_reg (snap_drop hP.2.2)); (try e30_norm at h0 h1); (try simp only [h0, h1]) <;> e30_addr) 0x101ca1 497 4 (by decide) (by decide)
      · x86_avoid
        all_goals ((try e30_norm); exact apart_at hP.2.1.hWrite 4 4 (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); have h1 := (snap_reg (snap_drop hP.2.2)); (try e30_norm at h0 h1); (try simp only [h0, h1]) <;> e30_addr) 0x101c9d 493 52 (by decide) (by decide))
    e30_then (and_r32_imm32_rex_effect_step 0x101ca5 0x41 0xe1 0x3ffffff (by e30_dec) (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101c9d) (all := bytes138) 8 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101cac (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (mov_m32_r32_effect_step 0x101cac 0x45 (by e30_dec) 1 (.base 10 (.d8 0x2c)) (by e30_dec) (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101c9d) (all := bytes138) 15 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101cb0 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      refine ⟨StorePre.of_holds hH (hO true) (by e30_norm) (by x86_addr_obs) ?_ ?_,
        Effect.Local.avoids (by x86_local) (hO true) ?_⟩
      · (try e30_norm); exact writable_at hP.2.1.hWrite 8 4 (by decide) (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); have h1 := (snap_reg (snap_drop hP.2.2)); (try e30_norm at h0 h1); (try simp only [h0, h1]) <;> e30_addr)
      · (try e30_norm); exact apart_at hP.2.1.hWrite 8 4 (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); have h1 := (snap_reg (snap_drop hP.2.2)); (try e30_norm at h0 h1); (try simp only [h0, h1]) <;> e30_addr) 0x101cac 508 4 (by decide) (by decide)
      · x86_avoid
        all_goals ((try e30_norm); exact apart_at hP.2.1.hWrite 8 4 (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); have h1 := (snap_reg (snap_drop hP.2.2)); (try e30_norm at h0 h1); (try simp only [h0, h1]) <;> e30_addr) 0x101c9d 493 52 (by decide) (by decide))
    e30_then (and_r32_imm32_effect_step 0x101cb0 0xe2 0x3ffffff (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101c9d) (all := bytes138) 19 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101cb6 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (mov_m32_r32_effect_step 0x101cb6 0x41 (by e30_dec) 2 (.base 10 (.d8 0x30)) (by e30_dec) (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101c9d) (all := bytes138) 25 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101cba (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      refine ⟨StorePre.of_holds hH (hO true) (by e30_norm) (by x86_addr_obs) ?_ ?_,
        Effect.Local.avoids (by x86_local) (hO true) ?_⟩
      · (try e30_norm); exact writable_at hP.2.1.hWrite 12 4 (by decide) (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); have h1 := (snap_reg (snap_drop hP.2.2)); (try e30_norm at h0 h1); (try simp only [h0, h1]) <;> e30_addr)
      · (try e30_norm); exact apart_at hP.2.1.hWrite 12 4 (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); have h1 := (snap_reg (snap_drop hP.2.2)); (try e30_norm at h0 h1); (try simp only [h0, h1]) <;> e30_addr) 0x101cb6 518 4 (by decide) (by decide)
      · x86_avoid
        all_goals ((try e30_norm); exact apart_at hP.2.1.hWrite 12 4 (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); have h1 := (snap_reg (snap_drop hP.2.2)); (try e30_norm at h0 h1); (try simp only [h0, h1]) <;> e30_addr) 0x101c9d 493 52 (by decide) (by decide))
    e30_then (and_eax_imm32_effect_step 0x101cba 0x3ffffff)
    case sub => exact codeRange_mem_of_drop (p := 0x101c9d) (all := bytes138) 29 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101cbf (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (mov_m32_r32_effect_step 0x101cbf 0x41 (by e30_dec) 0 (.base 10 (.d8 0x34)) (by e30_dec) (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101c9d) (all := bytes138) 34 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101cc3 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      refine ⟨StorePre.of_holds hH (hO true) (by e30_norm) (by x86_addr_obs) ?_ ?_,
        Effect.Local.avoids (by x86_local) (hO true) ?_⟩
      · (try e30_norm); exact writable_at hP.2.1.hWrite 16 4 (by decide) (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); have h1 := (snap_reg (snap_drop hP.2.2)); (try e30_norm at h0 h1); (try simp only [h0, h1]) <;> e30_addr)
      · (try e30_norm); exact apart_at hP.2.1.hWrite 16 4 (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); have h1 := (snap_reg (snap_drop hP.2.2)); (try e30_norm at h0 h1); (try simp only [h0, h1]) <;> e30_addr) 0x101cbf 527 4 (by decide) (by decide)
      · x86_avoid
        all_goals ((try e30_norm); exact apart_at hP.2.1.hWrite 16 4 (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); have h1 := (snap_reg (snap_drop hP.2.2)); (try e30_norm at h0 h1); (try simp only [h0, h1]) <;> e30_addr) 0x101c9d 493 52 (by decide) (by decide))
    e30_then (add_r64_imm8_effect_step 0x101cc3 0x48 0xc4 0x28 (by e30_dec) (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101c9d) (all := bytes138) 38 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101cc7 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (pop_r64_effect_step 0x101cc7 0x5b (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101c9d) (all := bytes138) 42 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101cc8 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by e30_norm) (by x86_addr_obs) ?_,
        Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
      try e30_norm
      exact readable_at hP.2.1.stack.readable 40 8 (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); (try e30_norm at h0); (try simp only [h0]) <;> e30_addr)
    e30_then (pop_r64_rex_effect_step 0x101cc8 0x41 0x5c (by e30_dec) (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101c9d) (all := bytes138) 43 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101cca (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by e30_norm) (by x86_addr_obs) ?_,
        Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
      try e30_norm
      exact readable_at hP.2.1.stack.readable 48 8 (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); (try e30_norm at h0); (try simp only [h0]) <;> e30_addr)
    e30_then (pop_r64_rex_effect_step 0x101cca 0x41 0x5d (by e30_dec) (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101c9d) (all := bytes138) 45 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101ccc (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by e30_norm) (by x86_addr_obs) ?_,
        Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
      try e30_norm
      exact readable_at hP.2.1.stack.readable 56 8 (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); (try e30_norm at h0); (try simp only [h0]) <;> e30_addr)
    e30_then (pop_r64_rex_effect_step 0x101ccc 0x41 0x5e (by e30_dec) (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101c9d) (all := bytes138) 47 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101cce (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by e30_norm) (by x86_addr_obs) ?_,
        Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
      try e30_norm
      exact readable_at hP.2.1.stack.readable 64 8 (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); (try e30_norm at h0); (try simp only [h0]) <;> e30_addr)
    e30_then (pop_r64_rex_effect_step 0x101cce 0x41 0x5f (by e30_dec) (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101c9d) (all := bytes138) 49 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101cd0 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by e30_norm) (by x86_addr_obs) ?_,
        Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
      try e30_norm
      exact readable_at hP.2.1.stack.readable 72 8 (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); (try e30_norm at h0); (try simp only [h0]) <;> e30_addr)
    e30_then (pop_r64_effect_step 0x101cd0 0x5d (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101c9d) (all := bytes138) 51 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101cd1 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by e30_norm) (by x86_addr_obs) ?_,
        Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
      try e30_norm
      exact readable_at hP.2.1.stack.readable 80 8 (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); (try e30_norm at h0); (try simp only [h0]) <;> e30_addr)
    exact id
  case hsub => exact program_text_subset (bytes := bytes138) 0x1c9d (by decide +kernel) (by decide +kernel)
  case post =>
    intro s t hP hH
    obtain ⟨_, hF, hW⟩ := hP
    simp only [cut138, Write.AllHold] at hW
    obtain ⟨hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8, hw9, hw10, hw11, hw12⟩ := hW
    e30_norm at hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8 hw9 hw10 hw11 hw12
    have ho := hH.obsAfter (by e30_norm [List.forall_mem_cons, List.forall_mem_nil, List.forall_mem_append]) true
    refine ⟨?_, ?_, ?_⟩
    · rw [hH.rip]; e30_norm
    · simp only [cut153, fin_h0, fin_h1, fin_h2, fin_h3, fin_h4, Write.AllHold, ← ho.read_reg, ← ho.read_mem]
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
        simp (config := { decide := true }) only [finalChanges, List.cons_append, List.nil_append, bodyChanges, Component.isMem, List.mem_cons, Component.reg.injEq, reduceCtorEq, true_or, or_true, false_or, or_false, imp_self, implies_true, and_self, true_and, and_true, List.not_mem_nil, false_implies]
      · intro x
        e30_norm [Effect.components]
        try simp only [hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8, hw9, hw10, hw11, hw12]
        try e30_norm
        repeat' apply And.intro
        all_goals first
          | exact fun h => cover_final_h (by bv_omega) (by bv_omega) h
          | exact fun h => cover_final_stack hsp (by bv_omega) h
          | exact fun h => absurd h (by simp only [Component.Covers, not_false_eq_true])

end ChaCha20Poly1305.Proofs.Poly1305.Callee101e30
