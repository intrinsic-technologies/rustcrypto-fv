import ChaCha20Poly1305.Proofs.Poly1305.Callee101e30.Defs

namespace ChaCha20Poly1305.Proofs.Poly1305.Callee101e30

set_option linter.unusedSimpArgs false

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Standards.RFC.ChaCha20Poly1305
open ChaCha20Poly1305.Spec.Program ChaCha20Poly1305.Proofs.Poly1305State
  ChaCha20Poly1305.Proofs.Common
open ChaCha20Poly1305.Proofs.MemoryRoutines.Machine ChaCha20Poly1305.Proofs.Poly1305.BlockArith

def bytes89 : List UInt8 :=
  [0x4c, 0x89, 0xf8, 0x4c, 0x8b, 0x44, 0x24, 0x18, 0x49, 0x0f, 0xaf, 0xc0, 0x49, 0x89, 0xd6, 0x4c,
    0x0f, 0xaf, 0xf6, 0x49, 0x01, 0xc6, 0x4c, 0x89, 0xe0, 0x48, 0x0f, 0xaf, 0xc5, 0x49, 0x89,
    0xcd, 0x4d, 0x0f, 0xaf, 0xe9, 0x49, 0x01, 0xc5, 0x4d, 0x01, 0xf5, 0x48, 0x0f, 0xaf, 0xdf,
    0x4c, 0x01, 0xeb]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seg89 [Bindings] (boundary : ReturnBoundary) (e : Env)
    (hne : ∀ pc : BitVec 64, 0x101ab0 ≤ pc.toNat → pc.toNat < 0x101cd2 → pc ≠ boundary.rip) :
    Seg boundary e 0x101bec 0x101c1d (cut89 e) (cut103 e) := by
  refine Seg.of_block (bytes := bytes89) (E := ?E) ?blk ?hsub ?post
  case blk =>
    refine AdvancesBlock.block_first ?k (mov_r64_r64_effect_step 0x101bec 0x4c 0xf8 (by e30_dec) (by e30_dec)) ?sub ?pre ?av ?boundary
    case sub => exact codeRange_mem_of_take (by decide +kernel)
    case pre =>
      intro s hP
      exact hP.1
    case av =>
      intro s hP
      x86_avoid
    case boundary => intro _ _; exact hne 0x101bef (by decide) (by decide)
    e30_then (mov_r64_m64_effect_step 0x101bef 0x4c (by e30_dec) 0 (.sib 4 none 0 (.d8 0x18)) (by e30_dec) (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101bec) (all := bytes89) 3 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101bf4 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by e30_norm) (by x86_addr_obs) ?_,
        Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
      try e30_norm
      exact readable_at hP.2.1.stack.readable 24 8 (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); (try e30_norm at h0); (try simp only [h0]) <;> e30_addr)
    e30_then (imul_r64_r64_effect_step 0x101bf4 0x49 (by e30_dec) 0xc0 (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101bec) (all := bytes89) 8 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101bf8 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (mov_r64_r64_effect_step 0x101bf8 0x49 0xd6 (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101bec) (all := bytes89) 12 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101bfb (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (imul_r64_r64_effect_step 0x101bfb 0x4c (by e30_dec) 0xf6 (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101bec) (all := bytes89) 15 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101bff (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (add_r64_r64_effect_step 0x101bff 0x49 0xc6 (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101bec) (all := bytes89) 19 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101c02 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (mov_r64_r64_effect_step 0x101c02 0x4c 0xe0 (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101bec) (all := bytes89) 22 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101c05 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (imul_r64_r64_effect_step 0x101c05 0x48 (by e30_dec) 0xc5 (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101bec) (all := bytes89) 25 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101c09 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (mov_r64_r64_effect_step 0x101c09 0x49 0xcd (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101bec) (all := bytes89) 29 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101c0c (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (imul_r64_r64_effect_step 0x101c0c 0x4d (by e30_dec) 0xe9 (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101bec) (all := bytes89) 32 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101c10 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (add_r64_r64_effect_step 0x101c10 0x49 0xc5 (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101bec) (all := bytes89) 36 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101c13 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (add_r64_r64_effect_step 0x101c13 0x4d 0xf5 (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101bec) (all := bytes89) 39 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101c16 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (imul_r64_r64_effect_step 0x101c16 0x48 (by e30_dec) 0xdf (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101bec) (all := bytes89) 42 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101c1a (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (add_r64_r64_effect_step 0x101c1a 0x4c 0xeb (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101bec) (all := bytes89) 46 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101c1d (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    exact id
  case hsub => exact program_text_subset (bytes := bytes89) 0x1bec (by decide +kernel) (by decide +kernel)
  case post =>
    intro s t hP hH
    obtain ⟨_, hF, hW⟩ := hP
    simp only [cut89, Write.AllHold] at hW
    obtain ⟨hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8, hw9, hw10, hw11, hw12, hw13, hw14, hw15, hw16, hw17, hw18, hw19, hw20, hw21⟩ := hW
    e30_norm at hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8 hw9 hw10 hw11 hw12 hw13 hw14 hw15 hw16 hw17 hw18 hw19 hw20 hw21
    have ho := hH.obsAfter (by e30_norm [List.forall_mem_cons, List.forall_mem_nil, List.forall_mem_append]) true
    refine ⟨?_, ?_, ?_⟩
    · rw [hH.rip]; e30_norm
    · simp only [cut103, c103_r3, Write.AllHold, ← ho.read_reg, ← ho.read_mem]
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
