import P256.Proofs.Program.Compare.Execution
import P256.Proofs.Program.Compare.Model
import P256.Proofs.Program.Compare.Instructions.And

namespace P256.Proofs.Program.Compare.Tail

open X86 X86.Machine X86.UserProcess X86Proofs

def maskedLength (s : RamState) (mask : BitVec 32) : BitVec 64 :=
  (((Operand.reg 1 : Operand 32).read s) &&& mask).setWidth 64

attribute [local x86_compose] maskedLength BitVec.shiftLeft_zero BitVec.add_zero

def eightPrepareBytes : List UInt8 :=
  [0x41, 0x89, 0xc9, 0x41, 0x83, 0xe1, 0x18, 0x4e, 0x8d, 0x4, 0xe, 0x4d, 0x85, 0xc9]

def eightPrepareEffect (s : RamState) : Effect :=
  { rip := 0x11cd3e
    writes := [⟨(Operand.reg 9 : Operand 64), maskedLength s 24⟩,
      ⟨(Operand.reg 8 : Operand 64), (Operand.reg 6 : Operand 64).read s + maskedLength s 24⟩]
    flags := some (testFlags (maskedLength s 24)) }

set_option maxRecDepth 2048 in
theorem eight_prepare [Bindings] :
    RegisterBlock (fun s ↦ s.RIP = 0x11cd30) (codeRange 0x11cd30 eightPrepareBytes)
      eightPrepareEffect := by
  unfold eightPrepareBytes
  p256_memcmp_run_begin mov_r32_r32_rex_effect_step 0x11cd30 0x41 0xc9
    (by unfold RexNoWPrefix; decide) (by decide)
  p256_memcmp_run_then and_r32_imm8_rex_effect_step 0x11cd33 0x41 0xe1 24
    (by unfold RexNoWPrefix; decide) (by decide) (by decide)
  case sub =>
    exact codeRange_mem_of_drop (p := 0x11cd30) (all := eightPrepareBytes) 3
      (by decide +kernel)
  p256_memcmp_run_then lea_r64_effect_step 0x11cd37 0x4e
    (by unfold RexWPrefix; decide) 0 (.sib 6 (some 9) 0 .none)
    (by decide) (by decide) (by decide)
  case sub =>
    exact codeRange_mem_of_drop (p := 0x11cd30) (all := eightPrepareBytes) 7
      (by decide +kernel)
  p256_memcmp_run_then test_r64_r64_effect_step 0x11cd3b 0x4d 0xc9
    (by unfold RexWPrefix; decide) (by decide)
  case sub =>
    exact codeRange_mem_of_drop (p := 0x11cd30) (all := eightPrepareBytes) 11
      (by decide +kernel)
  apply RegisterBlock.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [eightPrepareEffect, maskedLength]
  · x86_norm [eightPrepareEffect, maskedLength]
    simp [Operand.read, gprNumber, rexR, modrmReg]
  · intro i; cases i <;> x86_norm [eightPrepareEffect, maskedLength, BitVec.and_self]
    all_goals simp [Operand.read, gprNumber, rexR, modrmReg]
  · x86_norm [eightPrepareEffect, maskedLength]

def fourPrepareBytes : List UInt8 :=
  [0x41, 0x89, 0xc9, 0x41, 0x83, 0xe1, 0x4, 0x4a, 0x8d, 0x4, 0xe, 0x4d, 0x85, 0xc9]

def fourPrepareEffect (s : RamState) : Effect :=
  { rip := 0x11cd7e
    writes := [⟨(Operand.reg 9 : Operand 64), maskedLength s 4⟩,
      ⟨(Operand.reg 0 : Operand 64), (Operand.reg 6 : Operand 64).read s + maskedLength s 4⟩]
    flags := some (testFlags (maskedLength s 4)) }

set_option maxRecDepth 2048 in
theorem four_prepare [Bindings] :
    RegisterBlock (fun s ↦ s.RIP = 0x11cd70) (codeRange 0x11cd70 fourPrepareBytes)
      fourPrepareEffect := by
  unfold fourPrepareBytes
  p256_memcmp_run_begin mov_r32_r32_rex_effect_step 0x11cd70 0x41 0xc9
    (by unfold RexNoWPrefix; decide) (by decide)
  p256_memcmp_run_then and_r32_imm8_rex_effect_step 0x11cd73 0x41 0xe1 4
    (by unfold RexNoWPrefix; decide) (by decide) (by decide)
  case sub =>
    exact codeRange_mem_of_drop (p := 0x11cd70) (all := fourPrepareBytes) 3
      (by decide +kernel)
  p256_memcmp_run_then lea_r64_effect_step 0x11cd77 0x4a
    (by unfold RexWPrefix; decide) 0 (.sib 6 (some 9) 0 .none)
    (by decide) (by decide) (by decide)
  case sub =>
    exact codeRange_mem_of_drop (p := 0x11cd70) (all := fourPrepareBytes) 7
      (by decide +kernel)
  p256_memcmp_run_then test_r64_r64_effect_step 0x11cd7b 0x4d 0xc9
    (by unfold RexWPrefix; decide) (by decide)
  case sub =>
    exact codeRange_mem_of_drop (p := 0x11cd70) (all := fourPrepareBytes) 11
      (by decide +kernel)
  apply RegisterBlock.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [fourPrepareEffect, maskedLength]
  · x86_norm [fourPrepareEffect, maskedLength]
    simp [Operand.read, gprNumber, rexR, modrmReg]
  · intro i; cases i <;> x86_norm [fourPrepareEffect, maskedLength, BitVec.and_self]
    all_goals simp [Operand.read, gprNumber, rexR, modrmReg]
  · x86_norm [fourPrepareEffect, maskedLength]

def twoPrepareBytes : List UInt8 :=
  [0x41, 0x89, 0xc9, 0x41, 0x83, 0xe1, 0x2]

def twoPrepareEffect (s : RamState) : Effect :=
  { rip := 0x11cdb6
    writes := [⟨(Operand.reg 9 : Operand 64), maskedLength s 2⟩]
    flags := some (andFlags ((Operand.reg 1 : Operand 32).read s &&& 2)) }

set_option maxRecDepth 2048 in
theorem two_prepare [Bindings] :
    RegisterBlock (fun s ↦ s.RIP = 0x11cdaf) (codeRange 0x11cdaf twoPrepareBytes)
      twoPrepareEffect := by
  unfold twoPrepareBytes
  p256_memcmp_run_begin mov_r32_r32_rex_effect_step 0x11cdaf 0x41 0xc9
    (by unfold RexNoWPrefix; decide) (by decide)
  p256_memcmp_run_then and_r32_imm8_rex_effect_step 0x11cdb2 0x41 0xe1 2
    (by unfold RexNoWPrefix; decide) (by decide) (by decide)
  case sub =>
    exact codeRange_mem_of_drop (p := 0x11cdaf) (all := twoPrepareBytes) 3
      (by decide +kernel)
  apply RegisterBlock.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [twoPrepareEffect, maskedLength]
  · x86_norm [twoPrepareEffect, maskedLength]
    simp [Operand.read, gprNumber, rexR, modrmReg]
  · intro i; cases i <;> x86_norm [twoPrepareEffect, maskedLength, BitVec.and_self]
    all_goals simp [Operand.read, gprNumber, rexR, modrmReg]
  · x86_norm [twoPrepareEffect, maskedLength]

end P256.Proofs.Program.Compare.Tail
