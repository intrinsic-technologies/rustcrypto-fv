import Md5.Proofs.Buffered.Finalize.Geometry
import Md5.Proofs.Block.Execution
import Md5.Proofs.Block.Rounds.Store.Compose

namespace Md5.Proofs.Buffered.Finalize.Digest.Long.Clear

open X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

def bytes : List UInt8 :=
  [0x48, 0xc7, 0x44, 0x24, 0x18, 0x0, 0x0, 0x0, 0x0,
   0x48, 0xc7, 0x44, 0x24, 0x20, 0x0, 0x0, 0x0, 0x0,
   0x48, 0xc7, 0x44, 0x24, 0x28, 0x0, 0x0, 0x0, 0x0,
   0x48, 0xc7, 0x44, 0x24, 0x30, 0x0, 0x0, 0x0, 0x0,
   0x48, 0xc7, 0x44, 0x24, 0x38, 0x0, 0x0, 0x0, 0x0,
   0x48, 0xc7, 0x44, 0x24, 0x40, 0x0, 0x0, 0x0, 0x0,
   0x48, 0xc7, 0x44, 0x24, 0x48, 0x0, 0x0, 0x0, 0x0]

structure RunPre (s : RamState) : Prop extends Storage .digest s where
  rip : s.RIP = 0x1001a0

def effect (s : RamState) : Effect :=
  { rip := 0x1001df
    writes := [
      ⟨(.mem (stackPtr s + 24) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 32) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 40) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 48) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 56) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 64) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 72) : Operand 64), 0⟩] }

set_option maxHeartbeats 400000 in
theorem execution [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary RunPre (codeRange 0x1001a0 bytes) effect := by
  unfold bytes
  md5_run_begin (Stores.mov_m64_imm32_effect_step 0x1001a0 0x48
    (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d8 24))
    (by decide) (by decide) (by decide) 0)
  case pre =>
    intro s h
    exact ⟨h.rip, h.toStorage.stackWritable 24 8 (by decide),
      h.toStorage.stackApart (codeOffset := 0x1a0) (by decide) (by decide +kernel)⟩
  case av =>
    intro s h
    apply Effect.avoids_of_components_mem_rip
      (movM64Imm32Effect_components 0x1001a0 (.sib 4 none 0 (.d8 24)) 0 s)
    exact h.toStorage.stackApart (codeOffset := 0x1a0) (by decide) (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1a9 (by decide +kernel)
  md5_run_then (Stores.mov_m64_imm32_effect_step 0x1001a9 0x48
    (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d8 32))
    (by decide) (by decide) (by decide) 0)
  case sub => exact codeRange_mem_of_drop (p := 0x1001a0) 9 (by decide +kernel)
  case mid =>
    intro s t h hE hO
    have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
    refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
    · x86_norm
      exact h.toStorage.stackWritable 32 8 (by decide)
    · x86_norm
      exact h.toStorage.stackApart (codeOffset := 0x1a9) (by decide) (by decide +kernel)
    · apply Effect.avoids_of_components_mem_rip
        (movM64Imm32Effect_components 0x1001a9 (.sib 4 none 0 (.d8 32)) 0 t)
      change RangeApart (stackPtr t + 32) 8 0x1001a0 63
      rw [hsp]
      exact h.toStorage.stackApart (codeOffset := 0x1a0) (by decide) (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1b2 (by decide +kernel)
  md5_run_then (Stores.mov_m64_imm32_effect_step 0x1001b2 0x48
    (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d8 40))
    (by decide) (by decide) (by decide) 0)
  case sub => exact codeRange_mem_of_drop (p := 0x1001a0) 18 (by decide +kernel)
  case mid =>
    intro s t h hE hO
    have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
    refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
    · x86_norm
      exact h.toStorage.stackWritable 40 8 (by decide)
    · x86_norm
      exact h.toStorage.stackApart (codeOffset := 0x1b2) (by decide) (by decide +kernel)
    · apply Effect.avoids_of_components_mem_rip
        (movM64Imm32Effect_components 0x1001b2 (.sib 4 none 0 (.d8 40)) 0 t)
      change RangeApart (stackPtr t + 40) 8 0x1001a0 63
      rw [hsp]
      exact h.toStorage.stackApart (codeOffset := 0x1a0) (by decide) (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1bb (by decide +kernel)
  md5_run_then (Stores.mov_m64_imm32_effect_step 0x1001bb 0x48
    (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d8 48))
    (by decide) (by decide) (by decide) 0)
  case sub => exact codeRange_mem_of_drop (p := 0x1001a0) 27 (by decide +kernel)
  case mid =>
    intro s t h hE hO
    have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
    refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
    · x86_norm
      exact h.toStorage.stackWritable 48 8 (by decide)
    · x86_norm
      exact h.toStorage.stackApart (codeOffset := 0x1bb) (by decide) (by decide +kernel)
    · apply Effect.avoids_of_components_mem_rip
        (movM64Imm32Effect_components 0x1001bb (.sib 4 none 0 (.d8 48)) 0 t)
      change RangeApart (stackPtr t + 48) 8 0x1001a0 63
      rw [hsp]
      exact h.toStorage.stackApart (codeOffset := 0x1a0) (by decide) (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1c4 (by decide +kernel)
  md5_run_then (Stores.mov_m64_imm32_effect_step 0x1001c4 0x48
    (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d8 56))
    (by decide) (by decide) (by decide) 0)
  case sub => exact codeRange_mem_of_drop (p := 0x1001a0) 36 (by decide +kernel)
  case mid =>
    intro s t h hE hO
    have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
    refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
    · x86_norm
      exact h.toStorage.stackWritable 56 8 (by decide)
    · x86_norm
      exact h.toStorage.stackApart (codeOffset := 0x1c4) (by decide) (by decide +kernel)
    · apply Effect.avoids_of_components_mem_rip
        (movM64Imm32Effect_components 0x1001c4 (.sib 4 none 0 (.d8 56)) 0 t)
      change RangeApart (stackPtr t + 56) 8 0x1001a0 63
      rw [hsp]
      exact h.toStorage.stackApart (codeOffset := 0x1a0) (by decide) (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1cd (by decide +kernel)
  md5_run_then (Stores.mov_m64_imm32_effect_step 0x1001cd 0x48
    (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d8 64))
    (by decide) (by decide) (by decide) 0)
  case sub => exact codeRange_mem_of_drop (p := 0x1001a0) 45 (by decide +kernel)
  case mid =>
    intro s t h hE hO
    have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
    refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
    · x86_norm
      exact h.toStorage.stackWritable 64 8 (by decide)
    · x86_norm
      exact h.toStorage.stackApart (codeOffset := 0x1cd) (by decide) (by decide +kernel)
    · apply Effect.avoids_of_components_mem_rip
        (movM64Imm32Effect_components 0x1001cd (.sib 4 none 0 (.d8 64)) 0 t)
      change RangeApart (stackPtr t + 64) 8 0x1001a0 63
      rw [hsp]
      exact h.toStorage.stackApart (codeOffset := 0x1a0) (by decide) (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1d6 (by decide +kernel)
  md5_run_then (Stores.mov_m64_imm32_effect_step 0x1001d6 0x48
    (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d8 72))
    (by decide) (by decide) (by decide) 0)
  case sub => exact codeRange_mem_of_drop (p := 0x1001a0) 54 (by decide +kernel)
  case mid =>
    intro s t h hE hO
    have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
    refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
    · x86_norm
      exact h.toStorage.stackWritable 72 8 (by decide)
    · x86_norm
      exact h.toStorage.stackApart (codeOffset := 0x1d6) (by decide) (by decide +kernel)
    · apply Effect.avoids_of_components_mem_rip
        (movM64Imm32Effect_components 0x1001d6 (.sib 4 none 0 (.d8 72)) 0 t)
      change RangeApart (stackPtr t + 72) 8 0x1001a0 63
      rw [hsp]
      exact h.toStorage.stackApart (codeOffset := 0x1a0) (by decide) (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1df (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [effect]
  · x86_norm [effect, stackPtr]
    simp [Operand.read]
  · intro i; cases i <;> x86_norm [effect]
  · x86_norm [effect, stackPtr]
    simp [Operand.read]

end Md5.Proofs.Buffered.Finalize.Digest.Long.Clear
