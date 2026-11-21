import P256.Proofs.Program.Compare.Tail.Control

namespace P256.Proofs.Program.Compare

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Spec.Program P256.Spec.Program.Routines

private theorem nopEffect_local (p : BitVec 64) (len : Nat) :
    Effect.Local (fun _ : RamState ↦ nopEffect p len) :=
  AdvancesTriple.const_local (by simp [nopEffect])

attribute [local x86_local] nopEffect_local
attribute [local x86_compose] nopEffect BitVec.shiftLeft_zero BitVec.add_zero andR32Imm8Effect

def mainStartBytes : List UInt8 :=
  [0x4e, 0x8d, 0x0c, 0x06, 0x4e, 0x8d, 0x14, 0x02, 0x45, 0x31, 0xdb,
    0x0f, 0x1f, 0x40, 0x00]

def mainStartEffect (s : RamState) : Effect :=
  { rip := 0x11c890
    writes := [⟨(Operand.reg 9 : Operand 64),
        (Operand.reg 6 : Operand 64).read s + (Operand.reg 8 : Operand 64).read s⟩,
      ⟨(Operand.reg 10 : Operand 64),
        (Operand.reg 2 : Operand 64).read s + (Operand.reg 8 : Operand 64).read s⟩,
      ⟨(Operand.reg 11 : Operand 64), 0⟩]
    flags := some (xorFlags (0 : BitVec 32)) }

theorem main_start [Bindings] : RegisterBlock (fun s ↦ s.RIP = 0x11c881)
    (codeRange 0x11c881 mainStartBytes) mainStartEffect := by
  unfold mainStartBytes
  p256_memcmp_run_begin lea_r64_effect_step 0x11c881 0x4e
    (by unfold RexWPrefix; decide) 1 (.sib 6 (some 8) 0 .none)
    (by decide) (by decide) (by decide)
  p256_memcmp_run_then lea_r64_effect_step 0x11c885 0x4e
    (by unfold RexWPrefix; decide) 2 (.sib 2 (some 8) 0 .none)
    (by decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x11c881) (all := mainStartBytes) 4 (by decide +kernel)
  p256_memcmp_run_then xor_r32_r32_rex_effect_step 0x11c889 0x45 0xdb
    (by unfold RexNoWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x11c881) (all := mainStartBytes) 8 (by decide +kernel)
  p256_memcmp_run_then nop_m_effect_step 0x11c88c [] (by decide) (by decide)
    (.base 0 (.d8 0)) (by decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x11c881) (all := mainStartBytes) 11 (by decide +kernel)
  try (case mid =>
    intro s t hP hH _
    exact ⟨hH.rip, nopEffect_avoids _ _ _⟩)
  apply RegisterBlock.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [mainStartEffect]
  · x86_norm [mainStartEffect] <;> simp [Operand.read, gprNumber, rexR, rexB, modrmReg, modrmRm]
  · intro i; cases i <;> x86_norm [mainStartEffect] <;> simp [Operand.read, gprNumber, rexR, rexB, modrmReg, modrmRm]
  · x86_norm [mainStartEffect]

theorem main_start_program [Bindings] : RegisterBlock (fun s ↦ s.RIP = 0x11c881)
    Extracted.programSections.toCodeMap mainStartEffect :=
  Tail.program_block main_start
    (fun _ hc ↦ program_text_slice hc 0x1c881 15 (by decide +kernel))
    (by intro s hp; simp [mainStartEffect, Effect.components, Component.Covers])

def mainFinishEffect (s : RamState) : Effect :=
  { rip := 0x11c8c2
    writes := [⟨(Operand.reg 2 : Operand 64), (Operand.reg 10 : Operand 64).read s⟩,
      ⟨(Operand.reg 6 : Operand 64), (Operand.reg 9 : Operand 64).read s⟩] }

theorem main_finish [Bindings] : RegisterBlock (fun s ↦ s.RIP = 0x11c8bc)
    (codeRange 0x11c8bc [0x4c, 0x89, 0xd2, 0x4c, 0x89, 0xce]) mainFinishEffect := by
  p256_memcmp_run_begin mov_r64_r64_effect_step 0x11c8bc 0x4c 0xd2
    (by unfold RexWPrefix; decide) (by decide)
  p256_memcmp_run_then mov_r64_r64_effect_step 0x11c8bf 0x4c 0xce
    (by unfold RexWPrefix; decide) (by decide)
  case sub =>
    exact codeRange_mem_of_drop (p := 0x11c8bc)
      (all := [0x4c, 0x89, 0xd2, 0x4c, 0x89, 0xce]) 3 (by decide +kernel)
  apply RegisterBlock.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [mainFinishEffect]
  · x86_norm [mainFinishEffect] <;> simp [Operand.read, gprNumber, rexR, modrmReg]
  · intro i; cases i <;> x86_norm [mainFinishEffect] <;>
      simp [Operand.read, gprNumber, rexR, modrmReg]
  · x86_norm [mainFinishEffect]

theorem main_finish_program [Bindings] : RegisterBlock (fun s ↦ s.RIP = 0x11c8bc)
    Extracted.programSections.toCodeMap mainFinishEffect :=
  Tail.program_block main_finish
    (fun _ hc ↦ program_text_slice hc 0x1c8bc 6 (by decide +kernel))
    (by intro s hp; simp [mainFinishEffect, Effect.components, Component.Covers])

def tailPrepareEffect (s : RamState) : Effect :=
  { rip := 0x11c8c9
    writes := [⟨(Operand.reg 1 : Operand 64),
        (((Operand.reg 1 : Operand 32).read s) &&& 15).zeroExtend 64⟩,
      ⟨(Operand.reg 7 : Operand 64), (Operand.reg 5 : Operand 64).read s - 40⟩]
    flags := some (andFlags (((Operand.reg 1 : Operand 32).read s) &&& 15)) }

theorem tail_prepare [Bindings] : RegisterBlock (fun s ↦ s.RIP = 0x11c8c2)
    (codeRange 0x11c8c2 [0x83, 0xe1, 0x0f, 0x48, 0x8d, 0x7d, 0xd8]) tailPrepareEffect := by
  p256_memcmp_run_begin and_r32_imm8_effect_step 0x11c8c2 0xe1 15 (by decide) (by decide)
  p256_memcmp_run_then lea_r64_effect_step 0x11c8c5 0x48
    (by unfold RexWPrefix; decide) 7 (.base 5 (.d8 0xd8))
    (by decide) (by decide) (by decide)
  case sub =>
    exact codeRange_mem_of_drop (p := 0x11c8c2)
      (all := [0x83, 0xe1, 0x0f, 0x48, 0x8d, 0x7d, 0xd8]) 3 (by decide +kernel)
  apply RegisterBlock.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [tailPrepareEffect, BitVec.sub_eq_add_neg]
  · x86_norm [tailPrepareEffect, BitVec.sub_eq_add_neg] <;> simp [Operand.read, gprNumber, modrmRm]
  · intro i; cases i <;> x86_norm [tailPrepareEffect, BitVec.sub_eq_add_neg] <;>
      simp [Operand.read, gprNumber, modrmRm]
  · x86_norm [tailPrepareEffect, BitVec.sub_eq_add_neg]

theorem tail_prepare_program [Bindings] : RegisterBlock (fun s ↦ s.RIP = 0x11c8c2)
    Extracted.programSections.toCodeMap tailPrepareEffect :=
  Tail.program_block tail_prepare
    (fun _ hc ↦ program_text_slice hc 0x1c8c2 7 (by decide +kernel))
    (by intro s hp; simp [tailPrepareEffect, Effect.components, Component.Covers])

theorem main_gate [Bindings] : RegisterBlock (fun s ↦ s.RIP = 0x11c87f)
    Extracted.programSections.toCodeMap (jccEffect 0x11c87f 2 4 ((0x41#8).signExtend 64)) :=
  Tail.program_block
    (Tail.branch8 0x11c87f 4 0x41 (by unfold InRoutine; decide +kernel)
      (by unfold InRoutine; decide +kernel))
    (fun _ hc ↦ program_text_slice hc 0x1c87f 2 (by decide +kernel))
    (by intro s hp; simp [jccEffect, branchEffect, Effect.components, Component.Covers])

theorem tail_return_jump [Bindings] : RegisterBlock (fun s ↦ s.RIP = 0x11c8ce)
    Extracted.programSections.toCodeMap (fun _ ↦ jmpEffect 0x11c8ce 2 0x53) := by
  apply Tail.program_block
    (code := codeRange 0x11c8ce [0xeb, 0x53])
  · apply RegisterBlock.first (jmp_rel8_effect_step 0x11c8ce 0x53 (by decide +kernel))
      (fun _ h ↦ h) (fun _ h ↦ h)
    · intro s _
      exact Effect.Avoids.of_noMem (by simp [jmpEffect, Effect.components, Component.Covers]) _
    · intros
      simp [jmpEffect, Effect.components]
    · intros
      unfold InRoutine jmpEffect branchTarget
      decide +kernel
  · intro s hc
    exact program_text_slice hc 0x1c8ce 2 (by decide +kernel)
  · intro s hp
    simp [jmpEffect, Effect.components, Component.Covers]

end P256.Proofs.Program.Compare
