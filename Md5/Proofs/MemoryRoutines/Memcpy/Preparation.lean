import Md5.Proofs.Block.Execution
import Md5.Proofs.MemoryRoutines.Alignment

namespace Md5.Proofs.MemoryRoutines

open X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

abbrev r8 : Operand 64 := .reg 8

attribute [local x86_compose] andR32Imm8Effect

def memcpyWordsBytes : List UInt8 :=
  [0x4c, 0x29, 0xc2, 0x48, 0x89, 0xd1, 0x48, 0xc1, 0xe9, 0x03]

def memcpyWordsEffect (s : RamState) : Effect :=
  { rip := 0x1024d3
    writes := [⟨rdx, rdx.read s - r8.read s⟩,
      ⟨rcx, (rdx.read s - r8.read s) >>> 3⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem memcpy_words_prepare [Bindings] (boundary : ReturnBoundary)
    (h₁ : 0x1024cc#64 ≠ boundary.rip) (h₂ : 0x1024cf#64 ≠ boundary.rip)
    (h₃ : 0x1024d3#64 ≠ boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x1024c9)
      (codeRange 0x1024c9 memcpyWordsBytes) memcpyWordsEffect := by
  unfold memcpyWordsBytes
  md5_run_begin sub_r64_r64_effect_step 0x1024c9 0x4c 0xc2
    (by unfold RexWPrefix; decide) (by decide)
  case boundary => intro _ _; exact h₁
  md5_run_then mov_r64_r64_effect_step 0x1024cc 0x48 0xd1
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x1024c9) (all := memcpyWordsBytes) 3 (by decide +kernel)
  case boundary => intro _ _; exact h₂
  md5_run_then shr_r64_imm8_effect_step 0x1024cf 0x48 0xe9 0x03
    (by unfold RexWPrefix; decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x1024c9) (all := memcpyWordsBytes) 6 (by decide +kernel)
  case boundary => intro _ _; exact h₃
  apply AdvancesBlock.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [memcpyWordsEffect]
  · x86_norm [memcpyWordsEffect, rdx, r8]
    exact ⟨rfl, rfl⟩
  · intro i; cases i <;> x86_norm [memcpyWordsEffect]
  · x86_norm [memcpyWordsEffect, rdx, r8]

def memcpyTailBytes : List UInt8 := [0x83, 0xe2, 0x07, 0x48, 0x89, 0xd1]

def memcpyTailEffect (s : RamState) : Effect :=
  { rip := 0x1024dc
    writes := [⟨rdx, (((rdx.read s).setWidth 32) &&& (7 : BitVec 32)).setWidth 64⟩,
      ⟨rcx, (((rdx.read s).setWidth 32) &&& (7 : BitVec 32)).setWidth 64⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem memcpy_tail_prepare [Bindings] (boundary : ReturnBoundary)
    (h₁ : 0x1024d9#64 ≠ boundary.rip) (h₂ : 0x1024dc#64 ≠ boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x1024d6)
      (codeRange 0x1024d6 memcpyTailBytes) memcpyTailEffect := by
  unfold memcpyTailBytes
  md5_run_begin and_r32_imm8_effect_step 0x1024d6 0xe2 7 (by decide) (by decide)
  case boundary => intro _ _; exact h₁
  md5_run_then mov_r64_r64_effect_step 0x1024d9 0x48 0xd1
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x1024d6) (all := memcpyTailBytes) 3 (by decide +kernel)
  case boundary => intro _ _; exact h₂
  apply AdvancesBlock.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [memcpyTailEffect]
  · x86_norm [memcpyTailEffect, rdx]
    constructor <;> simp [Operand.read, gprNumber, modrmRm]
  · intro i; cases i <;> x86_norm [memcpyTailEffect]
  · x86_norm [memcpyTailEffect, rdx]

end Md5.Proofs.MemoryRoutines
