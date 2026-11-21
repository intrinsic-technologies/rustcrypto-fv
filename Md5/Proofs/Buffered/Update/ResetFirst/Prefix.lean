import Md5.Proofs.Block.Entry
import Md5.Proofs.Block.Execution
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple

namespace Md5.Proofs.Buffered.ResetFirst

open X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

attribute [x86_compose] movzxR32M8Effect

@[x86_local] theorem movzxR32M8Effect_local (p : BitVec 64) (len : Nat)
    (dst : BitVec 5) (am : AddrMode) : Effect.Local (movzxR32M8Effect p len dst am) := by
  refine ⟨fun _ _ _ ↦ rfl, fun s t h ↦ ?_, fun _ _ _ ↦ rfl,
    fun _ _ _ i hi ↦ ?_, fun _ ↦ ?_⟩
  · simp [movzxR32M8Effect, h.read_mem, AddrMode.addr_obs h]
  · simpa [movzxR32M8Effect, Effect.flag] using hi
  · simp [movzxR32M8Effect, Write.Full, Operand.Full]

def prefixBytes : List UInt8 :=
  [0x44, 0x0f, 0xb6, 0x6c, 0x24, 0x47, 0xba, 0x40, 0x00, 0x00, 0x00,
    0x4c, 0x29, 0xea, 0x4c, 0x89, 0xf3, 0x48, 0x29, 0xd3]

def position (s : RamState) : BitVec 64 :=
  ((Operand.mem (stackPtr s + 71) : Operand 8).read s).setWidth 64

def prefixEffect (s : RamState) : Effect :=
  let capacity := 64 - position s
  { rip := 0x1006e4
    writes := [⟨(.reg 13 : Operand 64), position s⟩,
      ⟨(.reg 2 : Operand 64), capacity⟩,
      ⟨(.reg 3 : Operand 64), (.reg 14 : Operand 64).read s - capacity⟩]
    flags := some (.ofStatusFlags (subSpec ((.reg 14 : Operand 64).read s) capacity).2) }

theorem entry_prepare [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (LoadPre 0x1006d0 (fun s ↦ stackPtr s + 71) 1)
      (codeRange 0x1006d0 prefixBytes) prefixEffect := by
  unfold prefixBytes
  md5_run_begin (movzx_r_m8_rex_effect_step 0x1006d0 0x44
    (by unfold RexPrefix; decide) 32 (.inr rfl)
    (fun seg ↦ (show RexNoWPrefix (0x44 : UInt8).toBitVec by
      unfold RexNoWPrefix; decide).operand_size seg)
    5 (.sib 4 none 0 (.d8 71)) (by decide) (by decide) (by decide))
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0x6d6 (by decide +kernel)
  md5_run_then mov_r32_imm32_effect_step 0x1006d6 0xba (by decide) 64
  case sub => exact codeRange_mem_of_drop (p := 0x1006d0) 6 (by decide +kernel)
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0x6db (by decide +kernel)
  md5_run_then sub_r64_r64_effect_step 0x1006db 0x4c 0xea
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x1006d0) 11 (by decide +kernel)
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0x6de (by decide +kernel)
  md5_run_then mov_r64_r64_effect_step 0x1006de 0x4c 0xf3
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x1006d0) 14 (by decide +kernel)
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0x6e1 (by decide +kernel)
  md5_run_then sub_r64_r64_effect_step 0x1006e1 0x48 0xd3
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x1006d0) 17 (by decide +kernel)
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0x6e4 (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [prefixEffect]
  · x86_norm [prefixEffect, position, stackPtr]
    simp [Operand.read, gprNumber, rexR, modrmReg]
  · intro i; cases i <;> x86_norm [prefixEffect, position, stackPtr]
    all_goals simp [Operand.read, gprNumber, rexR, modrmReg]
  · x86_norm [prefixEffect]

end Md5.Proofs.Buffered.ResetFirst
