import P256.Proofs.Nonce.Update.Absorb.Prefix.TagTail
import X86Proofs.Instructions.Shr.Generated.R.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Absorb.Seeded.RemainderHead

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Field P256.Proofs.Common.Instructions

attribute [local x86_compose] movM8Imm8Effect
attribute [local x86_local] Prepare.CompressionSetup.byteStore_local

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10a320
  remaining : (Operand.reg 3 : Operand 64).read s = 1
  writable : MemWritable s (rspOf s + 215) 1
  codeApart : ∀ pc len : Nat, pc + len ≤ 118431 →
    RangeApart (rspOf s + 215) 1 (Extracted.textAddress + BitVec.ofNat 64 pc) len

def bytes : List UInt8 := [0xc6, 0x84, 0x24, 0xd7, 0x0, 0x0, 0x0, 0x0, 0x4d, 0x89, 0xfc, 0x48, 0x89, 0xda, 0x48, 0xc1, 0xea, 0x6]

def effect (s : RamState) : Effect :=
  { rip := 0x10a332
    writes := [⟨(.mem (rspOf s + 215) : Operand 8),0⟩,
      ⟨(.reg 12 : Operand 64),(Operand.reg 15 : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64),0⟩]
    flags := some (shrFlags (StatusFlags.ofRFLAGS s.RFLAGS) 6 (1 : BitVec 64)) }

theorem code {s : RamState} (loaded : ProgramLoaded s) : CodeIn (codeRange 0x10a320 bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xa320 bytes (by decide) (by decide +kernel)

set_option maxHeartbeats 1000000 in
theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10a320 bytes) (Effect.post effect) := by
  advance_begin (mov_m8_imm8_effect_step 0x10a320 (.sib 4 none 0 (.d32 215)) (by decide) rfl rfl 0)
  case pre => intro s h; exact ⟨h.rip,h.writable,h.codeApart 0xa320 8 (by decide)⟩
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    simp only [movM8Imm8Effect,storeEffect_components,List.mem_cons,List.not_mem_nil,or_false]
    intro c hc a len eq
    rcases hc with rfl | rfl
    · cases eq; x86_norm; exact h.codeApart 0xa320 18 (by decide)
    · cases eq
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0xa328 (by decide))
  advance_then (show StepEffect _ _ (movR64R64Effect 0x10a328 12 15) from mov_r64_r64_effect_step 0x10a328 0x4d 0xfc (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10a320 bytes 8 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xa32b (by decide))⟩
  advance_then (show StepEffect _ _ (movR64R64Effect 0x10a32b 2 3) from mov_r64_r64_effect_step 0x10a32b 0x48 0xda (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10a320 bytes 11 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xa32e (by decide))⟩
  advance_then (show StepEffect _ _ (shrR64Effect 0x10a32e 4 2 6) from shr_r64_imm8_effect_step 0x10a32e 0x48 0xea 6 (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a320 bytes 14 4
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xa332 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  have rem := hP.remaining
  simp only [BitVec.ofNat_eq_ofNat] at rem
  apply hH.weaken
  · x86_norm [effect,rem]
  · x86_norm [effect,rem]
  · intro i; cases i <;> x86_norm [effect,rem]
  · x86_norm [effect,rem]

end P256.Proofs.Nonce.Update.Absorb.Seeded.RemainderHead
