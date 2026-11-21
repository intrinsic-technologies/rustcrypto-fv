import Md5.Proofs.Buffered.FinalizeReset.Contracts
import Md5.Proofs.Block.Entry
import Md5.Proofs.Block.Execution
import Md5.Proofs.Block.Shl
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple

namespace Md5.Proofs.Buffered.FinalizeReset.Normalize

open X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

attribute [local x86_compose] movzxR32M8Effect

theorem movzxR32M8Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {am : AddrMode} : Effect.Local (movzxR32M8Effect p len dst am) := by
  refine ⟨fun _ _ _ ↦ rfl, fun t t' h ↦ ?_, fun _ _ _ ↦ rfl,
    fun t t' h i hi ↦ ?_, fun _ ↦ ?_⟩
  · simp only [movzxR32M8Effect, h.read_mem, AddrMode.addr_obs h]
  · simpa only [movzxR32M8Effect, Effect.flag] using congrArg some hi
  · simp [movzxR32M8Effect, Write.Full, Operand.Full]

attribute [local x86_local] movzxR32M8Effect_local

def bytes : List UInt8 :=
  [0x4c, 0x8b, 0x74, 0x24, 0x58, 0x0f, 0xb6, 0x44, 0x24, 0x47,
    0x49, 0xc1, 0xe6, 0x09, 0x4c, 0x8b, 0xa4, 0x24, 0xc0, 0x00, 0x00, 0x00]

structure ReadPre (s : RamState) (variant : Variant := .saved) : Prop where
  rip : s.RIP = (variant.address 0x100790)
  blocks : MemReadable s (stackPtr s + 0x58) 8
  position : MemReadable s (stackPtr s + 0x47) 1
  saved : MemReadable s (stackPtr s + 0xc0) 8

def effect (s : RamState) (variant : Variant := .saved) : Effect :=
  { rip := (variant.address 0x1007a6)
    writes := [⟨(.reg 0 : Operand 64),
        ((Operand.mem (stackPtr s + 0x47) : Operand 8).read s).setWidth 64⟩,
      ⟨(.reg 12 : Operand 64), (Operand.mem (stackPtr s + 0xc0) : Operand 64).read s⟩,
      ⟨(.reg 14 : Operand 64), (Operand.mem (stackPtr s + 0x58) : Operand 64).read s <<< 9⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

local macro "finalize_reset_normalize_execution" v:term "," hout:term : tactic =>
  `(tactic| (
  unfold bytes
  md5_run_begin (mov_r64_m64_effect_step (($v).address 0x100790) 0x4c
    (by unfold RexWPrefix; decide) 6 (.sib 4 none 0 (.d8 0x58))
    (by decide) (by decide) (by decide))
  case pre => intro s h; exact ⟨h.rip, h.blocks⟩
  case boundary =>
    intro _ _
    exact text_address_ne_return ($hout) ((($v).address 0x100795).toNat - 0x100000) (by cases ($v) <;> decide +kernel)
  md5_run_then (movzx_r32_m8_effect_step (($v).address 0x100795) 0 (.sib 4 none 0 (.d8 0x47))
    (by decide) (by decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := (($v).address 0x100790)) 5 (by cases ($v) <;> decide +kernel)
  case mid =>
    intro s t h hE hO
    refine ⟨LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
    · x86_norm
      exact h.position
    · x86_avoid
  case boundary =>
    intro _ _
    exact text_address_ne_return ($hout) ((($v).address 0x10079a).toNat - 0x100000) (by cases ($v) <;> decide +kernel)
  md5_run_then (shl_r64_imm8_effect_step (($v).address 0x10079a) 0x49 0xe6 0x09
    (by unfold RexWPrefix; decide) (by decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := (($v).address 0x100790)) 10 (by cases ($v) <;> decide +kernel)
  case boundary =>
    intro _ _
    exact text_address_ne_return ($hout) ((($v).address 0x10079e).toNat - 0x100000) (by cases ($v) <;> decide +kernel)
  md5_run_then (mov_r64_m64_effect_step (($v).address 0x10079e) 0x4c
    (by unfold RexWPrefix; decide) 4 (.sib 4 none 0 (.d32 0xc0))
    (by decide) (by decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := (($v).address 0x100790)) 14 (by cases ($v) <;> decide +kernel)
  case mid =>
    intro s t h hE hO
    refine ⟨LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
    · x86_norm
      exact h.saved
    · x86_avoid
  case boundary =>
    intro _ _
    exact text_address_ne_return ($hout) ((($v).address 0x1007a6).toNat - 0x100000) (by cases ($v) <;> decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [effect, Variant.address]
  · x86_norm [effect, stackPtr, Variant.address]
    exact ⟨rfl, rfl, rfl⟩
  · intro i; cases i <;> x86_norm [effect, Variant.address]
  · x86_norm [effect, Variant.address]
  ))

theorem execution {variant : Variant} [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ ReadPre s variant) (codeRange (variant.address 0x100790) bytes) (fun s ↦ effect s variant) := by
  cases variant with
  | saved => finalize_reset_normalize_execution Variant.saved, hOutside
  | direct => finalize_reset_normalize_execution Variant.direct, hOutside

end Md5.Proofs.Buffered.FinalizeReset.Normalize
