import P256.Proofs.HMAC.Finalize.Digest

open P256.Proofs.Program
open P256.Proofs.Program.ScalarFrame (workRegion)

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice)
open P256.Proofs.Common.SHA256.Compression (bswap32 bswap_r32_effect_step)
open P256.Proofs.Common.Instructions.LegacyLoad (mov_r32_m32_legacy_effect_step)

namespace P256.Proofs.HMAC.Finalize.Digest.Outer

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

attribute [local x86_compose] P256.Proofs.Common.SHA256.Compression.encodeBswapR32
  BitVec.setWidth_setWidth_of_le BitVec.setWidth_eq gprNumber

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x1013af
  readable : ∀ i ∈ ([136,140,144,148,152,156,160,164] : List (BitVec 64)),
    MemReadable s (rspOf s + i) 4
  writable : ∀ i ∈ ([0,4,8,12,16,20,24,28] : List (BitVec 64)),
    Common.Instructions.CrossPageStore.Writable s ((Operand.reg 3 : Operand 64).read s + i) 4
  codeApart : ∀ i ∈ ([0,4,8,12,16,20,24,28] : List (BitVec 64)),
    RangeApart ((Operand.reg 3 : Operand 64).read s + i) 4 0x1013af 104

theorem Pre.codeApart_slice {s : RamState} (h : Pre s)
    (i : BitVec 64) (hi : i ∈ [0,4,8,12,16,20,24,28])
    (offset len : Nat) (bound : offset + len ≤ 104) :
    RangeApart ((Operand.reg 3 : Operand 64).read s + i) 4 (0x1013af + BitVec.ofNat 64 offset) len := by
  intro j hj k hk
  simpa only [BitVec.ofNat_add, BitVec.add_assoc] using
    h.codeApart i hi j hj (offset + k) (by omega)

def bytes : List UInt8 :=
  [0x8b, 0x84, 0x24, 0x88, 0x0, 0x0, 0x0, 0x8b, 0x8c, 0x24, 0x8c, 0x0, 0x0, 0x0, 0xf, 0xc8, 0xf, 0xc9, 0x8b, 0x94, 0x24, 0x90, 0x0, 0x0, 0x0, 0xf, 0xca, 0x8b, 0xb4, 0x24, 0x94, 0x0, 0x0, 0x0, 0xf, 0xce, 0x8b, 0xbc, 0x24, 0x98, 0x0, 0x0, 0x0, 0xf, 0xcf, 0x44, 0x8b, 0x84, 0x24, 0x9c, 0x0, 0x0, 0x0, 0x41, 0xf, 0xc8, 0x44, 0x8b, 0x8c, 0x24, 0xa0, 0x0, 0x0, 0x0, 0x41, 0xf, 0xc9, 0x44, 0x8b, 0x94, 0x24, 0xa4, 0x0, 0x0, 0x0, 0x41, 0xf, 0xca, 0x89, 0x3, 0x89, 0x4b, 0x4, 0x89, 0x53, 0x8, 0x89, 0x73, 0xc, 0x89, 0x7b, 0x10, 0x44, 0x89, 0x43, 0x14, 0x44, 0x89, 0x4b, 0x18, 0x44, 0x89, 0x53, 0x1c]

def effect (s : RamState) : Effect :=
  serializeEffect 0x101417 ((Operand.reg 3 : Operand 64).read s) s

theorem code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x1013af bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0x13af bytes
    (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 2000000 in
theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x1013af bytes) (Effect.post effect) := by
  advance_begin (mov_r32_m32_legacy_effect_step 0x1013af 0 (.sib 4 none 0 (.d32 136)) (by decide +kernel) rfl rfl)
  case pre => intro s h; exact ⟨h.rip, h.readable 136 (by simp)⟩
  case next =>
    intro s h
    exact boundary_ne_program outside (inProgram_of_textOffset 0x13b6 (by decide))
  advance_then (mov_r32_m32_legacy_effect_step 0x1013b6 1 (.sib 4 none 0 (.d32 140)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1013af bytes 7 7
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 140 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, P256.Proofs.Common.Instructions.LegacyLoad.movR32M32LegacyEffect_components]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x13bd (by decide))
  advance_then (bswap_r32_effect_step 0x1013bd 0)
  case sub => exact codeRange_slice_subset 0x1013af bytes 14 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, P256.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x13bf (by decide))
  advance_then (bswap_r32_effect_step 0x1013bf 1)
  case sub => exact codeRange_slice_subset 0x1013af bytes 16 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, P256.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x13c1 (by decide))
  advance_then (mov_r32_m32_legacy_effect_step 0x1013c1 2 (.sib 4 none 0 (.d32 144)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1013af bytes 18 7
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 144 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, P256.Proofs.Common.Instructions.LegacyLoad.movR32M32LegacyEffect_components]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x13c8 (by decide))
  advance_then (bswap_r32_effect_step 0x1013c8 2)
  case sub => exact codeRange_slice_subset 0x1013af bytes 25 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, P256.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x13ca (by decide))
  advance_then (mov_r32_m32_legacy_effect_step 0x1013ca 6 (.sib 4 none 0 (.d32 148)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1013af bytes 27 7
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 148 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, P256.Proofs.Common.Instructions.LegacyLoad.movR32M32LegacyEffect_components]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x13d1 (by decide))
  advance_then (bswap_r32_effect_step 0x1013d1 6)
  case sub => exact codeRange_slice_subset 0x1013af bytes 34 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, P256.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x13d3 (by decide))
  advance_then (mov_r32_m32_legacy_effect_step 0x1013d3 7 (.sib 4 none 0 (.d32 152)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1013af bytes 36 7
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 152 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, P256.Proofs.Common.Instructions.LegacyLoad.movR32M32LegacyEffect_components]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x13da (by decide))
  advance_then (bswap_r32_effect_step 0x1013da 7)
  case sub => exact codeRange_slice_subset 0x1013af bytes 43 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, P256.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x13dc (by decide))
  advance_then (mov_r32_m32_effect_step 0x1013dc 0x44 (by simp [RexNoWPrefix]) 0 (.sib 4 none 0 (.d32 156)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1013af bytes 45 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 156 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x13e4 (by decide))
  advance_then (bswap_r32_effect_step 0x1013e4 8)
  case sub => exact codeRange_slice_subset 0x1013af bytes 53 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, P256.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x13e7 (by decide))
  advance_then (mov_r32_m32_effect_step 0x1013e7 0x44 (by simp [RexNoWPrefix]) 1 (.sib 4 none 0 (.d32 160)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1013af bytes 56 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 160 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x13ef (by decide))
  advance_then (bswap_r32_effect_step 0x1013ef 9)
  case sub => exact codeRange_slice_subset 0x1013af bytes 64 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, P256.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x13f2 (by decide))
  advance_then (mov_r32_m32_effect_step 0x1013f2 0x44 (by simp [RexNoWPrefix]) 2 (.sib 4 none 0 (.d32 164)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1013af bytes 67 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 164 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x13fa (by decide))
  advance_then (bswap_r32_effect_step 0x1013fa 10)
  case sub => exact codeRange_slice_subset 0x1013af bytes 75 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, P256.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x13fd (by decide))
  advance_then (Common.Instructions.CrossPageStore.mov_m32_r32_legacy_effect_step_any 0x1013fd 0 (.base 3 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1013af bytes 78 2
  case mid =>
    intro s t hP hH hO
    refine ⟨Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 0 (by simp)
    · x86_norm
      exact hP.codeApart_slice 0 (by simp) 78 2 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 0 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x13ff (by decide))
  advance_then (Common.Instructions.CrossPageStore.mov_m32_r32_legacy_effect_step_any 0x1013ff 1 (.base 3 (.d8 4)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1013af bytes 80 3
  case mid =>
    intro s t hP hH hO
    refine ⟨Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 4 (by simp)
    · x86_norm
      exact hP.codeApart_slice 4 (by simp) 80 3 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 4 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1402 (by decide))
  advance_then (Common.Instructions.CrossPageStore.mov_m32_r32_legacy_effect_step_any 0x101402 2 (.base 3 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1013af bytes 83 3
  case mid =>
    intro s t hP hH hO
    refine ⟨Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 8 (by simp)
    · x86_norm
      exact hP.codeApart_slice 8 (by simp) 83 3 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 8 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1405 (by decide))
  advance_then (Common.Instructions.CrossPageStore.mov_m32_r32_legacy_effect_step_any 0x101405 6 (.base 3 (.d8 12)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1013af bytes 86 3
  case mid =>
    intro s t hP hH hO
    refine ⟨Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 12 (by simp)
    · x86_norm
      exact hP.codeApart_slice 12 (by simp) 86 3 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 12 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1408 (by decide))
  advance_then (Common.Instructions.CrossPageStore.mov_m32_r32_legacy_effect_step_any 0x101408 7 (.base 3 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1013af bytes 89 3
  case mid =>
    intro s t hP hH hO
    refine ⟨Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 16 (by simp)
    · x86_norm
      exact hP.codeApart_slice 16 (by simp) 89 3 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 16 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x140b (by decide))
  advance_then (Common.Instructions.CrossPageStore.mov_m32_r32_effect_step_any 0x10140b 0x44 (by simp [RexNoWPrefix]) 0 (.base 3 (.d8 20)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1013af bytes 92 4
  case mid =>
    intro s t hP hH hO
    refine ⟨Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 20 (by simp)
    · x86_norm
      exact hP.codeApart_slice 20 (by simp) 92 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 20 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x140f (by decide))
  advance_then (Common.Instructions.CrossPageStore.mov_m32_r32_effect_step_any 0x10140f 0x44 (by simp [RexNoWPrefix]) 1 (.base 3 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1013af bytes 96 4
  case mid =>
    intro s t hP hH hO
    refine ⟨Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 24 (by simp)
    · x86_norm
      exact hP.codeApart_slice 24 (by simp) 96 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 24 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1413 (by decide))
  advance_then (Common.Instructions.CrossPageStore.mov_m32_r32_effect_step_any 0x101413 0x44 (by simp [RexNoWPrefix]) 2 (.base 3 (.d8 28)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1013af bytes 100 4
  case mid =>
    intro s t hP hH hO
    refine ⟨Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 28 (by simp)
    · x86_norm
      exact hP.codeApart_slice 28 (by simp) 100 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 28 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1417 (by decide))
  advance_finish [effect, serializeEffect]

theorem output {s t : RamState} {hash : Array UInt32}
    (pre : Pre s)
    (state : SHA256.HashStateAt s (stackPtr s + 136) hash)
    (h : (effect s).Holds s t) :
    (registerRegion s .rbx 32).HasBytes
      t.external (SHA256.serializeHash hash) := by

  have allocated : ∀ i < 32, (t.external[(Operand.reg 3 : Operand 64).read s + BitVec.ofNat 64 i]?).isSome := by
    intro i hi
    have writable : Common.Instructions.CrossPageStore.Writable s
        ((Operand.reg 3 : Operand 64).read s + BitVec.ofNat 64 (4 * (i / 4))) 4 := by
      have hj : i / 4 < 8 := by omega
      rcases (by omega : i / 4 = 0 ∨ i / 4 = 1 ∨ i / 4 = 2 ∨ i / 4 = 3 ∨
        i / 4 = 4 ∨ i / 4 = 5 ∨ i / 4 = 6 ∨ i / 4 = 7) with
        hj | hj | hj | hj | hj | hj | hj | hj
      all_goals simp only [hj, Nat.reduceMul, BitVec.ofNat_eq_ofNat]
      all_goals first
        | exact pre.writable 0 (by decide)
        | exact pre.writable 4 (by decide)
        | exact pre.writable 8 (by decide)
        | exact pre.writable 12 (by decide)
        | exact pre.writable 16 (by decide)
        | exact pre.writable 20 (by decide)
        | exact pre.writable 24 (by decide)
        | exact pre.writable 28 (by decide)
    have byte := (writable.of_holds h).mem (i % 4) (by omega)
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 4 * (i / 4) + i % 4 = i by omega] at byte
    exact byte
  exact serializeEffect_output pre.readable allocated state h

end P256.Proofs.HMAC.Finalize.Digest.Outer
