import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Program.Code
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Not.Generated.R.Triple
import X86Proofs.Instructions.Rol.Generated.R.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Xor.Generated.RM.Triple
import X86Proofs.Instructions.Xor.Generated.MR.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Movs.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple

set_option autoImplicit false

namespace P256.Proofs.SHA256

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program
open P256.Proofs.Common.Instructions.LegacyLoad

structure LoadWordsPre (s : RamState) : Prop where
  rip : s.RIP = 0x1159bc
  readable : ∀ i < 7, MemReadable s (s.regValue .rdi + BitVec.ofNat 64 (4 * i)) 4

def loadWordsBytes : List UInt8 :=
  [0x8b,0x1f,0x44,0x8b,0x77,0x4,0x8b,0x47,0x8,0x44,0x8b,0x4f,0xc,0x44,0x8b,0x47,0x10,0x44,0x8b,0x57,0x14,0x8b,0x57,0x18]

def loadWordsEffect (s : RamState) : Effect :=
  { rip := 0x1159d4
    writes := [
      ⟨(Operand.reg 3 : Operand 64), (memLoad s.external (s.regValue .rdi + 0) 32).setWidth 64⟩,
      ⟨(Operand.reg 14 : Operand 64), (memLoad s.external (s.regValue .rdi + 4) 32).setWidth 64⟩,
      ⟨(Operand.reg 0 : Operand 64), (memLoad s.external (s.regValue .rdi + 8) 32).setWidth 64⟩,
      ⟨(Operand.reg 9 : Operand 64), (memLoad s.external (s.regValue .rdi + 12) 32).setWidth 64⟩,
      ⟨(Operand.reg 8 : Operand 64), (memLoad s.external (s.regValue .rdi + 16) 32).setWidth 64⟩,
      ⟨(Operand.reg 10 : Operand 64), (memLoad s.external (s.regValue .rdi + 20) 32).setWidth 64⟩,
      ⟨(Operand.reg 2 : Operand 64), (memLoad s.external (s.regValue .rdi + 24) 32).setWidth 64⟩] }

set_option maxHeartbeats 800000 in
theorem load_words_correct [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary LoadWordsPre (codeRange 0x1159bc loadWordsBytes)
      (Effect.post loadWordsEffect) := by
  advance_begin mov_r32_m32_legacy_effect_step 0x1159bc 3 (.base 7 .none) (by decide) rfl rfl
  case pre =>
    intro s hp
    refine ⟨hp.rip, ?_⟩
    x86_norm
    exact hp.readable 0 (by decide)
  case next => intro s hp; exact boundary_ne_program outside (inProgram_of_textOffset 0x159be (by decide))
  advance_then mov_r32_m32_effect_step 0x1159be 0x44 (by simp [RexNoWPrefix]) 6 (.base 7 (.d8 4)) (by decide) rfl rfl
  case sub => exact codeRange_slice_subset 0x1159bc loadWordsBytes 2 4
  case mid =>
    intro s t hp hh ho
    refine ⟨LoadPre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x159c2 (by decide))⟩
    x86_norm
    exact hp.readable 1 (by decide)
  advance_then mov_r32_m32_legacy_effect_step 0x1159c2 0 (.base 7 (.d8 8)) (by decide) rfl rfl
  case sub => exact codeRange_slice_subset 0x1159bc loadWordsBytes 6 3
  case mid =>
    intro s t hp hh ho
    refine ⟨LoadPre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers, movR32M32LegacyEffect_components]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x159c5 (by decide))⟩
    x86_norm
    exact hp.readable 2 (by decide)
  advance_then mov_r32_m32_effect_step 0x1159c5 0x44 (by simp [RexNoWPrefix]) 1 (.base 7 (.d8 12)) (by decide) rfl rfl
  case sub => exact codeRange_slice_subset 0x1159bc loadWordsBytes 9 4
  case mid =>
    intro s t hp hh ho
    refine ⟨LoadPre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x159c9 (by decide))⟩
    x86_norm
    exact hp.readable 3 (by decide)
  advance_then mov_r32_m32_effect_step 0x1159c9 0x44 (by simp [RexNoWPrefix]) 0 (.base 7 (.d8 16)) (by decide) rfl rfl
  case sub => exact codeRange_slice_subset 0x1159bc loadWordsBytes 13 4
  case mid =>
    intro s t hp hh ho
    refine ⟨LoadPre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x159cd (by decide))⟩
    x86_norm
    exact hp.readable 4 (by decide)
  advance_then mov_r32_m32_effect_step 0x1159cd 0x44 (by simp [RexNoWPrefix]) 2 (.base 7 (.d8 20)) (by decide) rfl rfl
  case sub => exact codeRange_slice_subset 0x1159bc loadWordsBytes 17 4
  case mid =>
    intro s t hp hh ho
    refine ⟨LoadPre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x159d1 (by decide))⟩
    x86_norm
    exact hp.readable 5 (by decide)
  advance_then mov_r32_m32_legacy_effect_step 0x1159d1 2 (.base 7 (.d8 24)) (by decide) rfl rfl
  case sub => exact codeRange_slice_subset 0x1159bc loadWordsBytes 21 3
  case mid =>
    intro s t hp hh ho
    refine ⟨LoadPre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers, movR32M32LegacyEffect_components]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x159d4 (by decide))⟩
    x86_norm
    exact hp.readable 6 (by decide)
  apply AdvanceTriple.block_end
  intro s t hp hh
  apply hh.weaken
  · x86_norm [loadWordsEffect]
  · x86_norm [loadWordsEffect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; cases i <;> x86_norm [loadWordsEffect]
  · x86_norm [loadWordsEffect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]

end P256.Proofs.SHA256
