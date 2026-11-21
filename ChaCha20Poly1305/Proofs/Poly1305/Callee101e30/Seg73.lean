import ChaCha20Poly1305.Proofs.Poly1305.Callee101e30.Defs

namespace ChaCha20Poly1305.Proofs.Poly1305.Callee101e30

set_option linter.unusedSimpArgs false

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Standards.RFC.ChaCha20Poly1305
open ChaCha20Poly1305.Spec.Program ChaCha20Poly1305.Proofs.Poly1305State
  ChaCha20Poly1305.Proofs.Common
open ChaCha20Poly1305.Proofs.MemoryRoutines.Machine ChaCha20Poly1305.Proofs.Poly1305.BlockArith

def bytes73 : List UInt8 :=
  [0x4c, 0x89, 0xf8, 0x48, 0x8b, 0x74, 0x24, 0x10, 0x48, 0x0f, 0xaf, 0xc6, 0x49, 0x89, 0xd6, 0x4c,
    0x0f, 0xaf, 0xf5, 0x49, 0x01, 0xc6, 0x4c, 0x89, 0xe0, 0x49, 0x0f, 0xaf, 0xc1, 0x49, 0x89,
    0xcd, 0x4c, 0x0f, 0xaf, 0xeb, 0x49, 0x01, 0xc5, 0x4d, 0x01, 0xf5, 0x4c, 0x89, 0xc0, 0x48,
    0x0f, 0xaf, 0xc7, 0x4c, 0x01, 0xe8, 0x48, 0x89, 0x04, 0x24]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seg73 [Bindings] (boundary : ReturnBoundary) (e : Env)
    (hne : ∀ pc : BitVec 64, 0x101ab0 ≤ pc.toNat → pc.toNat < 0x101cd2 → pc ≠ boundary.rip) :
    Seg boundary e 0x101bb4 0x101bec (cut73 e) (cut89 e) := by
  refine Seg.of_block (bytes := bytes73) (E := ?E) ?blk ?hsub ?post
  case blk =>
    refine AdvancesBlock.block_first ?k (mov_r64_r64_effect_step 0x101bb4 0x4c 0xf8 (by e30_dec) (by e30_dec)) ?sub ?pre ?av ?boundary
    case sub => exact codeRange_mem_of_take (by decide +kernel)
    case pre =>
      intro s hP
      exact hP.1
    case av =>
      intro s hP
      x86_avoid
    case boundary => intro _ _; exact hne 0x101bb7 (by decide) (by decide)
    e30_then (mov_r64_m64_effect_step 0x101bb7 0x48 (by e30_dec) 6 (.sib 4 none 0 (.d8 0x10)) (by e30_dec) (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101bb4) (all := bytes73) 3 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101bbc (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by e30_norm) (by x86_addr_obs) ?_,
        Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
      try e30_norm
      exact readable_at hP.2.1.stack.readable 16 8 (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); (try e30_norm at h0); (try simp only [h0]) <;> e30_addr)
    e30_then (imul_r64_r64_effect_step 0x101bbc 0x48 (by e30_dec) 0xc6 (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101bb4) (all := bytes73) 8 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101bc0 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (mov_r64_r64_effect_step 0x101bc0 0x49 0xd6 (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101bb4) (all := bytes73) 12 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101bc3 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (imul_r64_r64_effect_step 0x101bc3 0x4c (by e30_dec) 0xf5 (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101bb4) (all := bytes73) 15 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101bc7 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (add_r64_r64_effect_step 0x101bc7 0x49 0xc6 (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101bb4) (all := bytes73) 19 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101bca (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (mov_r64_r64_effect_step 0x101bca 0x4c 0xe0 (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101bb4) (all := bytes73) 22 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101bcd (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (imul_r64_r64_effect_step 0x101bcd 0x49 (by e30_dec) 0xc1 (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101bb4) (all := bytes73) 25 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101bd1 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (mov_r64_r64_effect_step 0x101bd1 0x49 0xcd (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101bb4) (all := bytes73) 29 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101bd4 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (imul_r64_r64_effect_step 0x101bd4 0x4c (by e30_dec) 0xeb (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101bb4) (all := bytes73) 32 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101bd8 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (add_r64_r64_effect_step 0x101bd8 0x49 0xc5 (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101bb4) (all := bytes73) 36 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101bdb (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (add_r64_r64_effect_step 0x101bdb 0x4d 0xf5 (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101bb4) (all := bytes73) 39 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101bde (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (mov_r64_r64_effect_step 0x101bde 0x4c 0xc0 (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101bb4) (all := bytes73) 42 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101be1 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (imul_r64_r64_effect_step 0x101be1 0x48 (by e30_dec) 0xc7 (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101bb4) (all := bytes73) 45 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101be5 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (add_r64_r64_effect_step 0x101be5 0x4c 0xe8 (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101bb4) (all := bytes73) 49 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101be8 (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      exact ⟨hH.rip_of (by e30_norm), Effect.Local.avoids (by x86_local) (hO true) (by x86_avoid)⟩
    e30_then (mov_m64_r64_effect_step 0x101be8 0x48 (by e30_dec) 0 (.sib 4 none 0 .none) (by e30_dec) (by e30_dec) (by e30_dec))
    case sub => exact codeRange_mem_of_drop (p := 0x101bb4) (all := bytes73) 52 (by decide +kernel)
    case boundary => intro _ _; exact hne 0x101bec (by decide) (by decide)
    case mid =>
      intro s s' hP hH hO
      refine ⟨StorePre.of_holds hH (hO true) (by e30_norm) (by x86_addr_obs) ?_ ?_,
        Effect.Local.avoids (by x86_local) (hO true) ?_⟩
      · (try e30_norm); exact writable_at hP.2.1.stack 0 8 (by decide) (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); (try e30_norm at h0); (try simp only [h0]) <;> e30_addr)
      · (try e30_norm); exact apart_at hP.2.1.stack 0 8 (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); (try e30_norm at h0); (try simp only [h0]) <;> e30_addr) 0x101be8 312 4 (by decide) (by decide)
      · x86_avoid
        all_goals ((try e30_norm); exact apart_at hP.2.1.stack 0 8 (by decide) (by (try e30_norm); have h0 := (snap_reg hP.2.2); (try e30_norm at h0); (try simp only [h0]) <;> e30_addr) 0x101bb4 260 56 (by decide) (by decide))
    exact id
  case hsub => exact program_text_subset (bytes := bytes73) 0x1bb4 (by decide +kernel) (by decide +kernel)
  case post =>
    intro s t hP hH
    obtain ⟨_, hF, hW⟩ := hP
    simp only [cut73, Write.AllHold] at hW
    obtain ⟨hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8, hw9, hw10, hw11, hw12, hw13, hw14, hw15, hw16, hw17, hw18, hw19, hw20, hw21⟩ := hW
    e30_norm at hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8 hw9 hw10 hw11 hw12 hw13 hw14 hw15 hw16 hw17 hw18 hw19 hw20 hw21
    have ho := hH.obsAfter (by e30_norm [List.forall_mem_cons, List.forall_mem_nil, List.forall_mem_append]) true
    refine ⟨?_, ?_, ?_⟩
    · rw [hH.rip]; e30_norm
    · simp only [cut89, c89_s88, Write.AllHold, ← ho.read_reg, ← ho.read_mem]
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
