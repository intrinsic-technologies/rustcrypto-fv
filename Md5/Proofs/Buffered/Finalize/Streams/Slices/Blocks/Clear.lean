import Md5.Proofs.Buffered.Finalize.Streams.Slices.Layout
import Md5.Proofs.Buffered.Finalize.Geometry
import Md5.Proofs.Block.Execution
import Md5.Proofs.Block.Rounds.Store.Compose

namespace Md5.Proofs.Buffered.Finalize.Streams.Slices.Blocks.Clear

open X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

def bytes : List UInt8 :=
  [0x48, 0xc7, 0x44, 0x24, 0x10, 0x0, 0x0, 0x0, 0x0,
   0x48, 0xc7, 0x44, 0x24, 0x18, 0x0, 0x0, 0x0, 0x0,
   0x48, 0xc7, 0x44, 0x24, 0x20, 0x0, 0x0, 0x0, 0x0,
   0x48, 0xc7, 0x44, 0x24, 0x28, 0x0, 0x0, 0x0, 0x0,
   0x48, 0xc7, 0x44, 0x24, 0x30, 0x0, 0x0, 0x0, 0x0,
   0x48, 0xc7, 0x44, 0x24, 0x38, 0x0, 0x0, 0x0, 0x0,
   0x48, 0xc7, 0x44, 0x24, 0x40, 0x0, 0x0, 0x0, 0x0]

structure RunPre (s : RamState) (update : Bool := false) : Prop extends Storage (streamKind update) s where
  rip : s.RIP = (BitVec.ofNat 64 (relocated update 0x1004fe))

def effect (s : RamState) (update : Bool := false) : Effect :=
  { rip := (BitVec.ofNat 64 (relocated update 0x10053d))
    writes := [
      ⟨(.mem (stackPtr s + 16) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 24) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 32) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 40) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 48) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 56) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 64) : Operand 64), 0⟩] }

set_option maxHeartbeats 800000 in
theorem execution {update : Bool} [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (RunPre (update := update)) (codeRange (BitVec.ofNat 64 (relocated update 0x1004fe)) bytes) (effect (update := update)) := by
  cases update with
  | false =>
    unfold bytes
    md5_run_begin (Stores.mov_m64_imm32_effect_step 0x1004fe 0x48
      (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d8 16))
      (by decide) (by decide) (by decide) 0)
    case pre =>
      intro s h
      exact ⟨h.rip, h.toStorage.stackWritable 16 8 (by decide),
        h.toStorage.stackApart (codeOffset := 0x4fe) (by decide) (by decide +kernel)⟩
    case av =>
      intro s h
      apply Effect.avoids_of_components_mem_rip
        (movM64Imm32Effect_components 0x1004fe (.sib 4 none 0 (.d8 16)) 0 s)
      exact h.toStorage.stackApart (codeOffset := 0x4fe) (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x507 (by decide +kernel)
    md5_run_then (Stores.mov_m64_imm32_effect_step 0x100507 0x48
      (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d8 24))
      (by decide) (by decide) (by decide) 0)
    case sub => exact codeRange_mem_of_drop (p := 0x1004fe) 9 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact h.toStorage.stackWritable 24 8 (by decide)
      · x86_norm
        exact h.toStorage.stackApart (codeOffset := 0x507) (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64Imm32Effect_components 0x100507 (.sib 4 none 0 (.d8 24)) 0 t)
        change RangeApart (stackPtr t + 24) 8 0x1004fe 63
        rw [hsp]
        exact h.toStorage.stackApart (codeOffset := 0x4fe) (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x510 (by decide +kernel)
    md5_run_then (Stores.mov_m64_imm32_effect_step 0x100510 0x48
      (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d8 32))
      (by decide) (by decide) (by decide) 0)
    case sub => exact codeRange_mem_of_drop (p := 0x1004fe) 18 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact h.toStorage.stackWritable 32 8 (by decide)
      · x86_norm
        exact h.toStorage.stackApart (codeOffset := 0x510) (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64Imm32Effect_components 0x100510 (.sib 4 none 0 (.d8 32)) 0 t)
        change RangeApart (stackPtr t + 32) 8 0x1004fe 63
        rw [hsp]
        exact h.toStorage.stackApart (codeOffset := 0x4fe) (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x519 (by decide +kernel)
    md5_run_then (Stores.mov_m64_imm32_effect_step 0x100519 0x48
      (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d8 40))
      (by decide) (by decide) (by decide) 0)
    case sub => exact codeRange_mem_of_drop (p := 0x1004fe) 27 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact h.toStorage.stackWritable 40 8 (by decide)
      · x86_norm
        exact h.toStorage.stackApart (codeOffset := 0x519) (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64Imm32Effect_components 0x100519 (.sib 4 none 0 (.d8 40)) 0 t)
        change RangeApart (stackPtr t + 40) 8 0x1004fe 63
        rw [hsp]
        exact h.toStorage.stackApart (codeOffset := 0x4fe) (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x522 (by decide +kernel)
    md5_run_then (Stores.mov_m64_imm32_effect_step 0x100522 0x48
      (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d8 48))
      (by decide) (by decide) (by decide) 0)
    case sub => exact codeRange_mem_of_drop (p := 0x1004fe) 36 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact h.toStorage.stackWritable 48 8 (by decide)
      · x86_norm
        exact h.toStorage.stackApart (codeOffset := 0x522) (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64Imm32Effect_components 0x100522 (.sib 4 none 0 (.d8 48)) 0 t)
        change RangeApart (stackPtr t + 48) 8 0x1004fe 63
        rw [hsp]
        exact h.toStorage.stackApart (codeOffset := 0x4fe) (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x52b (by decide +kernel)
    md5_run_then (Stores.mov_m64_imm32_effect_step 0x10052b 0x48
      (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d8 56))
      (by decide) (by decide) (by decide) 0)
    case sub => exact codeRange_mem_of_drop (p := 0x1004fe) 45 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact h.toStorage.stackWritable 56 8 (by decide)
      · x86_norm
        exact h.toStorage.stackApart (codeOffset := 0x52b) (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64Imm32Effect_components 0x10052b (.sib 4 none 0 (.d8 56)) 0 t)
        change RangeApart (stackPtr t + 56) 8 0x1004fe 63
        rw [hsp]
        exact h.toStorage.stackApart (codeOffset := 0x4fe) (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x534 (by decide +kernel)
    md5_run_then (Stores.mov_m64_imm32_effect_step 0x100534 0x48
      (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d8 64))
      (by decide) (by decide) (by decide) 0)
    case sub => exact codeRange_mem_of_drop (p := 0x1004fe) 54 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact h.toStorage.stackWritable 64 8 (by decide)
      · x86_norm
        exact h.toStorage.stackApart (codeOffset := 0x534) (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64Imm32Effect_components 0x100534 (.sib 4 none 0 (.d8 64)) 0 t)
        change RangeApart (stackPtr t + 64) 8 0x1004fe 63
        rw [hsp]
        exact h.toStorage.stackApart (codeOffset := 0x4fe) (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x53d (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [effect]
    · x86_norm [effect, stackPtr]
      simp [Operand.read]
    · intro i; cases i <;> x86_norm [effect]
    · x86_norm [effect, stackPtr]
      simp [Operand.read]
  | true =>
    unfold bytes
    md5_run_begin (Stores.mov_m64_imm32_effect_step 0x101aae 0x48
      (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d8 16))
      (by decide) (by decide) (by decide) 0)
    case pre =>
      intro s h
      exact ⟨h.rip, h.toStorage.stackWritable 16 8 (by decide),
        h.toStorage.stackApart (codeOffset := 0x1aae) (by decide) (by decide +kernel)⟩
    case av =>
      intro s h
      apply Effect.avoids_of_components_mem_rip
        (movM64Imm32Effect_components 0x101aae (.sib 4 none 0 (.d8 16)) 0 s)
      exact h.toStorage.stackApart (codeOffset := 0x1aae) (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x1ab7 (by decide +kernel)
    md5_run_then (Stores.mov_m64_imm32_effect_step 0x101ab7 0x48
      (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d8 24))
      (by decide) (by decide) (by decide) 0)
    case sub => exact codeRange_mem_of_drop (p := 0x101aae) 9 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact h.toStorage.stackWritable 24 8 (by decide)
      · x86_norm
        exact h.toStorage.stackApart (codeOffset := 0x1ab7) (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64Imm32Effect_components 0x101ab7 (.sib 4 none 0 (.d8 24)) 0 t)
        change RangeApart (stackPtr t + 24) 8 0x101aae 63
        rw [hsp]
        exact h.toStorage.stackApart (codeOffset := 0x1aae) (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x1ac0 (by decide +kernel)
    md5_run_then (Stores.mov_m64_imm32_effect_step 0x101ac0 0x48
      (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d8 32))
      (by decide) (by decide) (by decide) 0)
    case sub => exact codeRange_mem_of_drop (p := 0x101aae) 18 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact h.toStorage.stackWritable 32 8 (by decide)
      · x86_norm
        exact h.toStorage.stackApart (codeOffset := 0x1ac0) (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64Imm32Effect_components 0x101ac0 (.sib 4 none 0 (.d8 32)) 0 t)
        change RangeApart (stackPtr t + 32) 8 0x101aae 63
        rw [hsp]
        exact h.toStorage.stackApart (codeOffset := 0x1aae) (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x1ac9 (by decide +kernel)
    md5_run_then (Stores.mov_m64_imm32_effect_step 0x101ac9 0x48
      (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d8 40))
      (by decide) (by decide) (by decide) 0)
    case sub => exact codeRange_mem_of_drop (p := 0x101aae) 27 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact h.toStorage.stackWritable 40 8 (by decide)
      · x86_norm
        exact h.toStorage.stackApart (codeOffset := 0x1ac9) (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64Imm32Effect_components 0x101ac9 (.sib 4 none 0 (.d8 40)) 0 t)
        change RangeApart (stackPtr t + 40) 8 0x101aae 63
        rw [hsp]
        exact h.toStorage.stackApart (codeOffset := 0x1aae) (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x1ad2 (by decide +kernel)
    md5_run_then (Stores.mov_m64_imm32_effect_step 0x101ad2 0x48
      (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d8 48))
      (by decide) (by decide) (by decide) 0)
    case sub => exact codeRange_mem_of_drop (p := 0x101aae) 36 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact h.toStorage.stackWritable 48 8 (by decide)
      · x86_norm
        exact h.toStorage.stackApart (codeOffset := 0x1ad2) (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64Imm32Effect_components 0x101ad2 (.sib 4 none 0 (.d8 48)) 0 t)
        change RangeApart (stackPtr t + 48) 8 0x101aae 63
        rw [hsp]
        exact h.toStorage.stackApart (codeOffset := 0x1aae) (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x1adb (by decide +kernel)
    md5_run_then (Stores.mov_m64_imm32_effect_step 0x101adb 0x48
      (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d8 56))
      (by decide) (by decide) (by decide) 0)
    case sub => exact codeRange_mem_of_drop (p := 0x101aae) 45 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact h.toStorage.stackWritable 56 8 (by decide)
      · x86_norm
        exact h.toStorage.stackApart (codeOffset := 0x1adb) (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64Imm32Effect_components 0x101adb (.sib 4 none 0 (.d8 56)) 0 t)
        change RangeApart (stackPtr t + 56) 8 0x101aae 63
        rw [hsp]
        exact h.toStorage.stackApart (codeOffset := 0x1aae) (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x1ae4 (by decide +kernel)
    md5_run_then (Stores.mov_m64_imm32_effect_step 0x101ae4 0x48
      (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d8 64))
      (by decide) (by decide) (by decide) 0)
    case sub => exact codeRange_mem_of_drop (p := 0x101aae) 54 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact h.toStorage.stackWritable 64 8 (by decide)
      · x86_norm
        exact h.toStorage.stackApart (codeOffset := 0x1ae4) (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64Imm32Effect_components 0x101ae4 (.sib 4 none 0 (.d8 64)) 0 t)
        change RangeApart (stackPtr t + 64) 8 0x101aae 63
        rw [hsp]
        exact h.toStorage.stackApart (codeOffset := 0x1aae) (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x1aed (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [effect]
    · x86_norm [effect, stackPtr]
      simp [Operand.read]
    · intro i; cases i <;> x86_norm [effect]
    · x86_norm [effect, stackPtr]
      simp [Operand.read]

end Md5.Proofs.Buffered.Finalize.Streams.Slices.Blocks.Clear
