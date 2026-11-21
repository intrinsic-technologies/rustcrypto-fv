import Md5.Proofs.Buffered.FinalizeReset.Length.Register
import Md5.Proofs.Buffered.Finalize.Geometry
import Md5.Proofs.Buffered.FinalizeReset.Length
import Md5.Proofs.Buffered.Stores.Program
import Md5.Proofs.Block.Rounds.Store.Compose

namespace Md5.Proofs.Buffered.Finalize.Digest.Finish.Length

open X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block
open Md5.Proofs.Buffered.FinalizeReset.Length

def bytes : List UInt8 :=
  [0x41, 0xc1, 0xe4, 0x03, 0x49, 0xc1, 0xe7, 0x09, 0x4d, 0x09, 0xe7,
    0x4c, 0x89, 0x7c, 0x24, 0x50, 0x4c, 0x89, 0xbc, 0x24, 0xa8, 0, 0, 0]

structure RunPre (s : RamState) : Prop extends Storage .digest s where
  rip : s.RIP = 0x1001df

def value (s : RamState) : BitVec 64 :=
  ((Operand.reg 15 : Operand 64).read s <<< 9) |||
    (((Operand.reg 12 : Operand 32).read s) <<< 3).setWidth 64

def effect (s : RamState) : Effect :=
  { rip := 0x1001f7
    writes := [⟨(.reg 12 : Operand 64),
      (((Operand.reg 12 : Operand 32).read s) <<< 3).setWidth 64⟩,
      ⟨(.reg 15 : Operand 64), value s⟩,
      ⟨(.mem (stackPtr s + 0x50) : Operand 64), value s⟩,
      ⟨(.mem (stackPtr s + 0xa8) : Operand 64), value s⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem execution [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary RunPre (codeRange 0x1001df bytes) effect := by
  unfold bytes
  md5_run_begin (shl_r32_imm8_rex_effect_step 0x1001df 0x41 0xe4 3
    (by unfold RexNoWPrefix; decide) (by decide) (by decide))
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1e3 (by decide +kernel)
  md5_run_then (shl_r64_imm8_effect_step 0x1001e3 0x49 0xe7 9
    (by unfold RexWPrefix; decide) (by decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x1001df) 4 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1e7 (by decide +kernel)
  md5_run_then (or_r64_r64_effect_step 0x1001e7 0x4d 0xe7
    (by unfold RexWPrefix; decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x1001df) 8 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1ea (by decide +kernel)
  md5_run_then (Stores.mov_m64_r64_effect_step 0x1001ea 0x4c
    (by unfold RexWPrefix; decide) 7 (.sib 4 none 0 (.d8 0x50))
    (by decide) (by decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x1001df) 11 (by decide +kernel)
  case mid =>
    intro s t h hE hO
    have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
    refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
    · x86_norm
      exact h.toStorage.stackWritable 0x50 8 (by decide)
    · x86_norm
      exact h.toStorage.stackApart (codeOffset := 0x1ea) (by decide) (by decide +kernel)
    · apply Effect.avoids_of_components_mem_rip
        (movM64R64Effect_components 0x1001ea 15 (.sib 4 none 0 (.d8 0x50)) t)
      change RangeApart (stackPtr t + 0x50) 8 0x1001df 24
      rw [hsp]
      exact h.toStorage.stackApart (codeOffset := 0x1df) (by decide) (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1ef (by decide +kernel)
  md5_run_then (Stores.mov_m64_r64_effect_step 0x1001ef 0x4c
    (by unfold RexWPrefix; decide) 7 (.sib 4 none 0 (.d32 0xa8))
    (by decide) (by decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x1001df) 16 (by decide +kernel)
  case mid =>
    intro s t h hE hO
    have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
    refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
    · x86_norm
      exact h.toStorage.stackWritable 0xa8 8 (by decide)
    · x86_norm
      exact h.toStorage.stackApart (codeOffset := 0x1ef) (by decide) (by decide +kernel)
    · apply Effect.avoids_of_components_mem_rip
        (movM64R64Effect_components 0x1001ef 15 (.sib 4 none 0 (.d32 0xa8)) t)
      change RangeApart (stackPtr t + 0xa8) 8 0x1001df 24
      rw [hsp]
      exact h.toStorage.stackApart (codeOffset := 0x1df) (by decide) (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1f7 (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [effect]
  · x86_norm [effect, value, stackPtr]
    simp [Operand.read]
    exact ⟨rfl, rfl⟩
  · intro i; cases i <;> x86_norm [effect]
  · x86_norm [effect, stackPtr]
    simp [Operand.read]

end Md5.Proofs.Buffered.Finalize.Digest.Finish.Length
