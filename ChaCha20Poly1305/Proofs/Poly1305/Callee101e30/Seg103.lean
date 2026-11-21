import ChaCha20Poly1305.Proofs.Poly1305.Callee101e30.Defs

namespace ChaCha20Poly1305.Proofs.Poly1305.Callee101e30

set_option linter.unusedSimpArgs false

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Standards.RFC.ChaCha20Poly1305
open ChaCha20Poly1305.Spec.Program ChaCha20Poly1305.Proofs.Poly1305State
  ChaCha20Poly1305.Proofs.Common
open ChaCha20Poly1305.Proofs.MemoryRoutines.Machine ChaCha20Poly1305.Proofs.Poly1305.BlockArith

def bytes103 : List UInt8 :=
  [0x4c, 0x0f, 0xaf, 0x7c, 0x24, 0x20, 0x49, 0x0f, 0xaf, 0xd0, 0x4c, 0x01, 0xfa, 0x4c, 0x0f, 0xaf,
    0xe6, 0x48, 0x0f, 0xaf, 0xcd, 0x4c, 0x01, 0xe1, 0x48, 0x01, 0xd1, 0x49, 0x0f, 0xaf, 0xf9,
    0x48, 0x01, 0xcf]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seg103 [Bindings] (boundary : ReturnBoundary) (e : Env)
    (hne : ∀ pc : BitVec 64, 0x101ab0 ≤ pc.toNat → pc.toNat < 0x101cd2 → pc ≠ boundary.rip) :
    Seg boundary e 0x101c1d 0x101c3f (cut103 e) (cut112 e) := by
  refine Seg.of_block (bytes := bytes103) (E := ?E) ?blk ?hsub ?post
  case blk =>
    refine AdvancesBlock.block_first ?k (imul_r64_m64_effect_step 0x101c1d 0x4c (by e30_dec) 7 (.sib 4 none 0 (.d8 0x20)) (by e30_dec) (by e30_dec) (by e30_dec)) ?sub ?pre ?av ?boundary
    case sub => exact codeRange_mem_of_take (by decide +kernel)
    case pre =>
      intro s hP
      refine ⟨hP.1, ?_⟩
      exact readable_at hP.2.1.stack.readable 32 8 (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); (try e30_norm at h0); (try simp only [h0]) <;> e30_addr)
    case av =>
      intro s hP
      x86_avoid
    case boundary => intro _ _; exact hne 0x101c23 (by decide) (by decide)
    e30_then (imul_r64_r64_effect_step 0x101c23 0x49 (by e30_dec) 0xd0 (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101c1d) (all := bytes103) 6 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101c27 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (add_r64_r64_effect_step 0x101c27 0x4c 0xfa (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101c1d) (all := bytes103) 10 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101c2a (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (imul_r64_r64_effect_step 0x101c2a 0x4c (by e30_dec) 0xe6 (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101c1d) (all := bytes103) 13 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101c2e (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (imul_r64_r64_effect_step 0x101c2e 0x48 (by e30_dec) 0xcd (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101c1d) (all := bytes103) 17 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101c32 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (add_r64_r64_effect_step 0x101c32 0x4c 0xe1 (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101c1d) (all := bytes103) 21 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101c35 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (add_r64_r64_effect_step 0x101c35 0x48 0xd1 (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101c1d) (all := bytes103) 24 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101c38 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (imul_r64_r64_effect_step 0x101c38 0x49 (by e30_dec) 0xf9 (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101c1d) (all := bytes103) 27 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101c3c (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (add_r64_r64_effect_step 0x101c3c 0x48 0xcf (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101c1d) (all := bytes103) 31 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101c3f (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    exact id
  case hsub => exact program_text_subset (bytes := bytes103) 0x1c1d (by decide +kernel) (by decide +kernel)
  case post =>
    intro s t hP hH
    obtain ⟨_, hF, hW⟩ := hP
    simp only [cut103, Write.AllHold] at hW
    obtain ⟨hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8, hw9, hw10, hw11, hw12, hw13, hw14, hw15, hw16, hw17, hw18, hw19, hw20, hw21⟩ := hW
    e30_norm at hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8 hw9 hw10 hw11 hw12 hw13 hw14 hw15 hw16 hw17 hw18 hw19 hw20 hw21
    have ho := hH.obsAfter (by e30_norm [List.forall_mem_cons, List.forall_mem_nil, List.forall_mem_append]) true
    refine ⟨?_, ?_, ?_⟩
    · rw [hH.rip]; e30_norm
    · simp only [cut112, c112_r7, Write.AllHold, ← ho.read_reg, ← ho.read_mem]
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
