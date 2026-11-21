import P256.Proofs.Nonce.Update.Absorb.Prefix.Head
import P256.Proofs.Nonce.Update.Absorb.Seeded.Increment

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Absorb.Seeded.CompressionSetup

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Field P256.Proofs.Common.Instructions
open Increment

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10a303
  writable : MemWritable s (rspOf s + 248) 8
  codeApart : ∀ pc len : Nat, pc + len ≤ 118431 →
    RangeApart (rspOf s + 248) 8 (Extracted.textAddress + BitVec.ofNat 64 pc) len

def bytes : List UInt8 := [0x48, 0xff, 0x84, 0x24, 0xf8, 0x0, 0x0, 0x0, 0xba, 0x1, 0x0, 0x0, 0x0, 0x48, 0x8d, 0xbc, 0x24, 0xd8, 0x0, 0x0, 0x0, 0x4c, 0x89, 0xee]

def effect (s : RamState) : Effect :=
  { rip := 0x10a31b
    writes := [⟨(.mem (rspOf s + 248) : Operand 64),memLoad s.external (rspOf s + 248) 64 + 1⟩,
      ⟨(.reg 2 : Operand 64),1⟩, ⟨(.reg 7 : Operand 64),rspOf s + 216⟩,
      ⟨(.reg 6 : Operand 64),(Operand.reg 13 : Operand 64).read s⟩]
    flags := some ⟨none,none,none,none,none,none⟩ }

theorem code {s : RamState} (loaded : ProgramLoaded s) : CodeIn (codeRange 0x10a303 bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xa303 bytes (by decide) (by decide +kernel)

set_option maxHeartbeats 1000000 in
theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10a303 bytes) (Effect.post effect) := by
  advance_begin (StepEffect.forgetFlags (h := inc_rsp1a0_effect_step 0x10a303))
  case pre => intro s h; exact ⟨h.rip,h.writable,h.codeApart 0xa303 8 (by decide)⟩
  case av =>
    intro s h
    apply Effect.Avoids.forgetFlags
    apply Effect.avoids_codeRange
    simp only [incM64Effect_components, List.mem_cons, List.not_mem_nil, or_false]
    intro c hc a len eq
    rcases hc with rfl | rfl | rfl
    · cases eq
      x86_norm
      exact h.codeApart 0xa303 24 (by decide)
    · cases eq
    · cases eq
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0xa30b (by decide))
  advance_then (mov_r32_imm32_effect_step 0x10a30b 0xba (by decide) 1)
  case sub => exact codeRange_slice_subset 0x10a303 bytes 8 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xa310 (by decide))⟩
  advance_then (lea_r64_effect_step 0x10a310 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 216)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a303 bytes 13 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xa318 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10a318 0x4c 0xee (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10a303 bytes 21 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xa31b (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [effect]
  · x86_norm [effect]
    rfl
  · intro i; cases i <;> x86_norm [effect]
  · x86_norm [effect]

end P256.Proofs.Nonce.Update.Absorb.Seeded.CompressionSetup
