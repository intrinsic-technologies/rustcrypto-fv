import P256.Proofs.Nonce.Update.Absorb.Prefix.Head
import P256.Proofs.Nonce.Update.Absorb.Seeded.Increment
open P256.Proofs.Nonce.Update.Absorb.Seeded.Increment

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Seeded.Absorb.CompressionSetup

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Field P256.Proofs.Common.Instructions

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10a7c0
  writable : MemWritable s (rspOf s + 416) 8
  codeApart : ∀ pc len : Nat, pc + len ≤ 118431 →
    RangeApart (rspOf s + 416) 8 (Extracted.textAddress + BitVec.ofNat 64 pc) len

def bytes : List UInt8 := [0x48, 0xff, 0x84, 0x24, 0xa0, 0x1, 0x0, 0x0, 0xba, 0x1, 0x0, 0x0, 0x0, 0x4c, 0x89, 0xf7, 0x4c, 0x89, 0xe6]

def effect (s : RamState) : Effect :=
  { rip := 0x10a7d3
    writes := [⟨(.mem (rspOf s + 416) : Operand 64),memLoad s.external (rspOf s + 416) 64 + 1⟩,
      ⟨(.reg 2 : Operand 64),1⟩, ⟨(.reg 7 : Operand 64),(Operand.reg 14 : Operand 64).read s⟩,
      ⟨(.reg 6 : Operand 64),(Operand.reg 12 : Operand 64).read s⟩]
    flags := some ⟨none,none,none,none,none,none⟩ }

theorem code {s : RamState} (loaded : ProgramLoaded s) : CodeIn (codeRange 0x10a7c0 bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xa7c0 bytes (by decide) (by decide +kernel)

theorem inc_rspF8_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (StorePre p 8 (fun s => (Operand.reg 4 : Operand 64).read s + 416) 8)
      (codeRange p [0x48, 0xff, 0x84, 0x24, 0xa0, 0x1, 0x0, 0x0])
      (incM64Effect p (.sib 4 none 0 (.d32 416))) := by
  refine (inc_m64_effect_step p 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d32 416)) (by decide) rfl rfl).mono_pre ?_
  intro s h
  change StorePre p 8 _ 8 s
  simpa [AddrMode.addr, AddrMode.reg64, Disp.value] using h

set_option maxHeartbeats 1000000 in
theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10a7c0 bytes) (Effect.post effect) := by
  advance_begin (StepEffect.forgetFlags (h := inc_rspF8_effect_step 0x10a7c0))
  case pre => intro s h; exact ⟨h.rip,h.writable,h.codeApart 0xa7c0 8 (by decide)⟩
  case av =>
    intro s h
    apply Effect.Avoids.forgetFlags
    apply Effect.avoids_codeRange
    simp only [incM64Effect_components, List.mem_cons, List.not_mem_nil, or_false]
    intro c hc a len eq
    rcases hc with rfl | rfl | rfl
    · cases eq
      x86_norm
      exact h.codeApart 0xa7c0 19 (by decide)
    · cases eq
    · cases eq
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0xa7c8 (by decide))
  advance_then (mov_r32_imm32_effect_step 0x10a7c8 0xba (by decide) 1)
  case sub => exact codeRange_slice_subset 0x10a7c0 bytes 8 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xa7cd (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10a7cd 0x4c 0xf7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10a7c0 bytes 13 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xa7d0 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10a7d0 0x4c 0xe6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10a7c0 bytes 16 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xa7d3 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [effect]
  · x86_norm [effect]
    exact ⟨rfl, rfl⟩
  · intro i; cases i <;> x86_norm [effect]
  · x86_norm [effect]

end P256.Proofs.Nonce.Update.Seeded.Absorb.CompressionSetup
