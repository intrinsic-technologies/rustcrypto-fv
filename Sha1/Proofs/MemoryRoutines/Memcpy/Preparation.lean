import Sha1.Proofs.Compress.Machine.Execution
import Sha1.Proofs.MemoryRoutines.Alignment

namespace Sha1.Proofs.MemoryRoutines

open X86 X86.Machine X86.UserProcess X86Proofs Sha1.Proofs.Compress.Machine

abbrev r8 : Operand 64 := .reg 8

attribute [local x86_compose] andR32Imm8Effect

def memcpyWordsBytes : List UInt8 :=
  [0x4c, 0x29, 0xc2, 0x48, 0x89, 0xd1, 0x48, 0xc1, 0xe9, 0x03]

def memcpyWordsEffect (s : RamState) : Effect :=
  { rip := 0x103753
    writes := [⟨rdx, rdx.read s - r8.read s⟩,
      ⟨rcx, (rdx.read s - r8.read s) >>> 3⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem memcpy_words_prepare [Bindings] (boundary : ReturnBoundary)
    (h₁ : 0x10374c#64 ≠ boundary.rip) (h₂ : 0x10374f#64 ≠ boundary.rip)
    (h₃ : 0x103753#64 ≠ boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x103749)
      (codeRange 0x103749 memcpyWordsBytes) memcpyWordsEffect := by
  unfold memcpyWordsBytes
  md5_run_begin sub_r64_r64_effect_step 0x103749 0x4c 0xc2
    (by unfold RexWPrefix; decide) (by decide)
  case boundary => intro _ _; exact h₁
  md5_run_then mov_r64_r64_effect_step 0x10374c 0x48 0xd1
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x103749) (all := memcpyWordsBytes) 3 (by decide +kernel)
  case boundary => intro _ _; exact h₂
  md5_run_then shr_r64_imm8_effect_step 0x10374f 0x48 0xe9 0x03
    (by unfold RexWPrefix; decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x103749) (all := memcpyWordsBytes) 6 (by decide +kernel)
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
  { rip := 0x10375c
    writes := [⟨rdx, (((rdx.read s).setWidth 32) &&& (7 : BitVec 32)).setWidth 64⟩,
      ⟨rcx, (((rdx.read s).setWidth 32) &&& (7 : BitVec 32)).setWidth 64⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem memcpy_tail_prepare [Bindings] (boundary : ReturnBoundary)
    (h₁ : 0x103759#64 ≠ boundary.rip) (h₂ : 0x10375c#64 ≠ boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x103756)
      (codeRange 0x103756 memcpyTailBytes) memcpyTailEffect := by
  unfold memcpyTailBytes
  md5_run_begin and_r32_imm8_effect_step 0x103756 0xe2 7 (by decide) (by decide)
  case boundary => intro _ _; exact h₁
  md5_run_then mov_r64_r64_effect_step 0x103759 0x48 0xd1
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x103756) (all := memcpyTailBytes) 3 (by decide +kernel)
  case boundary => intro _ _; exact h₂
  apply AdvancesBlock.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [memcpyTailEffect]
  · x86_norm [memcpyTailEffect, rdx]
    constructor <;> simp [Operand.read, gprNumber, modrmRm]
  · intro i; cases i <;> x86_norm [memcpyTailEffect]
  · x86_norm [memcpyTailEffect, rdx]

end Sha1.Proofs.MemoryRoutines
