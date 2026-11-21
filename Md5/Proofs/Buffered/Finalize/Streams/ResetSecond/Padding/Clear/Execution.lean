import Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Contracts
import Md5.Proofs.Block.Execution
import Md5.Proofs.Block.Rounds.Store.Compose

namespace Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Padding.Clear

open X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

def entry (variant : Variant := .original) : BitVec 64 :=
  match variant with
  | .original => 0x100b87
  | .finalize => 0x101217
  | .discard => 0x101703

def bytes (variant : Variant := .original) : List UInt8 :=
  match variant with
  | .original => [0x48, 0xc7, 0x44, 0x24, 0x60, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x44, 0x24, 0x68, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x44, 0x24, 0x70, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x44, 0x24, 0x78, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x84, 0x24, 0x80, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x84, 0x24, 0x88, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x84, 0x24, 0x90, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]
  | .finalize => [0x48, 0xc7, 0x44, 0x24, 0x60, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x44, 0x24, 0x68, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x44, 0x24, 0x70, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x44, 0x24, 0x78, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x84, 0x24, 0x80, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x84, 0x24, 0x88, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x84, 0x24, 0x90, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]
  | .discard => [0x48, 0xc7, 0x84, 0x24, 0x88, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x84, 0x24, 0x90, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x84, 0x24, 0x98, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x84, 0x24, 0xa0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x84, 0x24, 0xa8, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x84, 0x24, 0xb0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x84, 0x24, 0xb8, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]

structure RunPre (s : RamState) (variant : Variant := .original) : Prop extends Storage variant.toKind s where
  rip : s.RIP = entry variant

def effect (s : RamState) (variant : Variant := .original) : Effect :=
  { rip := variant.paddedRip
    writes := [
      ⟨(.mem (stackPtr s + BitVec.ofNat 64 (variant.tailOffset + 0)) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + BitVec.ofNat 64 (variant.tailOffset + 8)) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + BitVec.ofNat 64 (variant.tailOffset + 16)) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + BitVec.ofNat 64 (variant.tailOffset + 24)) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + BitVec.ofNat 64 (variant.tailOffset + 32)) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + BitVec.ofNat 64 (variant.tailOffset + 40)) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + BitVec.ofNat 64 (variant.tailOffset + 48)) : Operand 64), 0⟩] }

set_option maxHeartbeats 1200000 in
theorem execution [Bindings] {variant : Variant} (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ RunPre s variant) (codeRange (entry variant) (bytes variant))
      (fun s ↦ effect s variant) := by
  cases variant with
  | original =>
    simp only [bytes]
    md5_run_begin (Stores.mov_m64_imm32_effect_step 0x100b87 0x48
      (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d8 96))
      (by decide) (by decide) (by decide) 0)
    case pre =>
      intro s h
      exact ⟨h.rip, h.toStorage.stackWritable 96 8 (by decide),
        h.toStorage.stackApart (codeOffset := 0xb87) (by decide) (by decide +kernel)⟩
    case av =>
      intro s h
      apply Effect.avoids_of_components_mem_rip
        (movM64Imm32Effect_components 0x100b87 (.sib 4 none 0 (.d8 96)) 0 s)
      exact h.toStorage.stackApart (codeOffset := 0xb87) (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0xb90 (by decide +kernel)
    md5_run_then (Stores.mov_m64_imm32_effect_step 0x100b90 0x48
      (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d8 104))
      (by decide) (by decide) (by decide) 0)
    case sub => exact codeRange_mem_of_drop (p := 0x100b87) 9 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact h.toStorage.stackWritable 104 8 (by decide)
      · x86_norm
        exact h.toStorage.stackApart (codeOffset := 0xb90) (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64Imm32Effect_components 0x100b90 (.sib 4 none 0 (.d8 104)) 0 t)
        change RangeApart (stackPtr t + 104) 8 0x100b87 72
        rw [hsp]
        exact h.toStorage.stackApart (codeOffset := 0xb87) (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0xb99 (by decide +kernel)
    md5_run_then (Stores.mov_m64_imm32_effect_step 0x100b99 0x48
      (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d8 112))
      (by decide) (by decide) (by decide) 0)
    case sub => exact codeRange_mem_of_drop (p := 0x100b87) 18 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact h.toStorage.stackWritable 112 8 (by decide)
      · x86_norm
        exact h.toStorage.stackApart (codeOffset := 0xb99) (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64Imm32Effect_components 0x100b99 (.sib 4 none 0 (.d8 112)) 0 t)
        change RangeApart (stackPtr t + 112) 8 0x100b87 72
        rw [hsp]
        exact h.toStorage.stackApart (codeOffset := 0xb87) (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0xba2 (by decide +kernel)
    md5_run_then (Stores.mov_m64_imm32_effect_step 0x100ba2 0x48
      (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d8 120))
      (by decide) (by decide) (by decide) 0)
    case sub => exact codeRange_mem_of_drop (p := 0x100b87) 27 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact h.toStorage.stackWritable 120 8 (by decide)
      · x86_norm
        exact h.toStorage.stackApart (codeOffset := 0xba2) (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64Imm32Effect_components 0x100ba2 (.sib 4 none 0 (.d8 120)) 0 t)
        change RangeApart (stackPtr t + 120) 8 0x100b87 72
        rw [hsp]
        exact h.toStorage.stackApart (codeOffset := 0xb87) (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0xbab (by decide +kernel)
    md5_run_then (Stores.mov_m64_imm32_effect_step 0x100bab 0x48
      (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d32 128))
      (by decide) (by decide) (by decide) 0)
    case sub => exact codeRange_mem_of_drop (p := 0x100b87) 36 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact h.toStorage.stackWritable 128 8 (by decide)
      · x86_norm
        exact h.toStorage.stackApart (codeOffset := 0xbab) (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64Imm32Effect_components 0x100bab (.sib 4 none 0 (.d32 128)) 0 t)
        change RangeApart (stackPtr t + 128) 8 0x100b87 72
        rw [hsp]
        exact h.toStorage.stackApart (codeOffset := 0xb87) (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0xbb7 (by decide +kernel)
    md5_run_then (Stores.mov_m64_imm32_effect_step 0x100bb7 0x48
      (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d32 136))
      (by decide) (by decide) (by decide) 0)
    case sub => exact codeRange_mem_of_drop (p := 0x100b87) 48 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact h.toStorage.stackWritable 136 8 (by decide)
      · x86_norm
        exact h.toStorage.stackApart (codeOffset := 0xbb7) (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64Imm32Effect_components 0x100bb7 (.sib 4 none 0 (.d32 136)) 0 t)
        change RangeApart (stackPtr t + 136) 8 0x100b87 72
        rw [hsp]
        exact h.toStorage.stackApart (codeOffset := 0xb87) (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0xbc3 (by decide +kernel)
    md5_run_then (Stores.mov_m64_imm32_effect_step 0x100bc3 0x48
      (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d32 144))
      (by decide) (by decide) (by decide) 0)
    case sub => exact codeRange_mem_of_drop (p := 0x100b87) 60 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact h.toStorage.stackWritable 144 8 (by decide)
      · x86_norm
        exact h.toStorage.stackApart (codeOffset := 0xbc3) (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64Imm32Effect_components 0x100bc3 (.sib 4 none 0 (.d32 144)) 0 t)
        change RangeApart (stackPtr t + 144) 8 0x100b87 72
        rw [hsp]
        exact h.toStorage.stackApart (codeOffset := 0xb87) (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0xbcf (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [effect]
    · x86_norm [effect, stackPtr]
      simp [Operand.read, Variant.tailOffset]
    · intro i; cases i <;> x86_norm [effect]
    · x86_norm [effect, stackPtr]
      simp [Operand.read, Variant.tailOffset]
  | finalize =>
    simp only [bytes]
    md5_run_begin (Stores.mov_m64_imm32_effect_step 0x101217 0x48
      (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d8 96))
      (by decide) (by decide) (by decide) 0)
    case pre =>
      intro s h
      exact ⟨h.rip, h.toStorage.stackWritable 96 8 (by decide),
        h.toStorage.stackApart (codeOffset := 0x1217) (by decide) (by decide +kernel)⟩
    case av =>
      intro s h
      apply Effect.avoids_of_components_mem_rip
        (movM64Imm32Effect_components 0x101217 (.sib 4 none 0 (.d8 96)) 0 s)
      exact h.toStorage.stackApart (codeOffset := 0x1217) (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x1220 (by decide +kernel)
    md5_run_then (Stores.mov_m64_imm32_effect_step 0x101220 0x48
      (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d8 104))
      (by decide) (by decide) (by decide) 0)
    case sub => exact codeRange_mem_of_drop (p := 0x101217) 9 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact h.toStorage.stackWritable 104 8 (by decide)
      · x86_norm
        exact h.toStorage.stackApart (codeOffset := 0x1220) (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64Imm32Effect_components 0x101220 (.sib 4 none 0 (.d8 104)) 0 t)
        change RangeApart (stackPtr t + 104) 8 0x101217 72
        rw [hsp]
        exact h.toStorage.stackApart (codeOffset := 0x1217) (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x1229 (by decide +kernel)
    md5_run_then (Stores.mov_m64_imm32_effect_step 0x101229 0x48
      (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d8 112))
      (by decide) (by decide) (by decide) 0)
    case sub => exact codeRange_mem_of_drop (p := 0x101217) 18 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact h.toStorage.stackWritable 112 8 (by decide)
      · x86_norm
        exact h.toStorage.stackApart (codeOffset := 0x1229) (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64Imm32Effect_components 0x101229 (.sib 4 none 0 (.d8 112)) 0 t)
        change RangeApart (stackPtr t + 112) 8 0x101217 72
        rw [hsp]
        exact h.toStorage.stackApart (codeOffset := 0x1217) (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x1232 (by decide +kernel)
    md5_run_then (Stores.mov_m64_imm32_effect_step 0x101232 0x48
      (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d8 120))
      (by decide) (by decide) (by decide) 0)
    case sub => exact codeRange_mem_of_drop (p := 0x101217) 27 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact h.toStorage.stackWritable 120 8 (by decide)
      · x86_norm
        exact h.toStorage.stackApart (codeOffset := 0x1232) (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64Imm32Effect_components 0x101232 (.sib 4 none 0 (.d8 120)) 0 t)
        change RangeApart (stackPtr t + 120) 8 0x101217 72
        rw [hsp]
        exact h.toStorage.stackApart (codeOffset := 0x1217) (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x123b (by decide +kernel)
    md5_run_then (Stores.mov_m64_imm32_effect_step 0x10123b 0x48
      (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d32 128))
      (by decide) (by decide) (by decide) 0)
    case sub => exact codeRange_mem_of_drop (p := 0x101217) 36 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact h.toStorage.stackWritable 128 8 (by decide)
      · x86_norm
        exact h.toStorage.stackApart (codeOffset := 0x123b) (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64Imm32Effect_components 0x10123b (.sib 4 none 0 (.d32 128)) 0 t)
        change RangeApart (stackPtr t + 128) 8 0x101217 72
        rw [hsp]
        exact h.toStorage.stackApart (codeOffset := 0x1217) (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x1247 (by decide +kernel)
    md5_run_then (Stores.mov_m64_imm32_effect_step 0x101247 0x48
      (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d32 136))
      (by decide) (by decide) (by decide) 0)
    case sub => exact codeRange_mem_of_drop (p := 0x101217) 48 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact h.toStorage.stackWritable 136 8 (by decide)
      · x86_norm
        exact h.toStorage.stackApart (codeOffset := 0x1247) (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64Imm32Effect_components 0x101247 (.sib 4 none 0 (.d32 136)) 0 t)
        change RangeApart (stackPtr t + 136) 8 0x101217 72
        rw [hsp]
        exact h.toStorage.stackApart (codeOffset := 0x1217) (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x1253 (by decide +kernel)
    md5_run_then (Stores.mov_m64_imm32_effect_step 0x101253 0x48
      (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d32 144))
      (by decide) (by decide) (by decide) 0)
    case sub => exact codeRange_mem_of_drop (p := 0x101217) 60 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact h.toStorage.stackWritable 144 8 (by decide)
      · x86_norm
        exact h.toStorage.stackApart (codeOffset := 0x1253) (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64Imm32Effect_components 0x101253 (.sib 4 none 0 (.d32 144)) 0 t)
        change RangeApart (stackPtr t + 144) 8 0x101217 72
        rw [hsp]
        exact h.toStorage.stackApart (codeOffset := 0x1217) (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x125f (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [effect]
    · x86_norm [effect, stackPtr]
      simp [Operand.read, Variant.tailOffset]
    · intro i; cases i <;> x86_norm [effect]
    · x86_norm [effect, stackPtr]
      simp [Operand.read, Variant.tailOffset]
  | discard =>
    simp only [bytes]
    md5_run_begin (Stores.mov_m64_imm32_effect_step 0x101703 0x48
      (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d32 136))
      (by decide) (by decide) (by decide) 0)
    case pre =>
      intro s h
      exact ⟨h.rip, h.toStorage.stackWritable 136 8 (by decide),
        h.toStorage.stackApart (codeOffset := 0x1703) (by decide) (by decide +kernel)⟩
    case av =>
      intro s h
      apply Effect.avoids_of_components_mem_rip
        (movM64Imm32Effect_components 0x101703 (.sib 4 none 0 (.d32 136)) 0 s)
      exact h.toStorage.stackApart (codeOffset := 0x1703) (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x170f (by decide +kernel)
    md5_run_then (Stores.mov_m64_imm32_effect_step 0x10170f 0x48
      (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d32 144))
      (by decide) (by decide) (by decide) 0)
    case sub => exact codeRange_mem_of_drop (p := 0x101703) 12 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact h.toStorage.stackWritable 144 8 (by decide)
      · x86_norm
        exact h.toStorage.stackApart (codeOffset := 0x170f) (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64Imm32Effect_components 0x10170f (.sib 4 none 0 (.d32 144)) 0 t)
        change RangeApart (stackPtr t + 144) 8 0x101703 84
        rw [hsp]
        exact h.toStorage.stackApart (codeOffset := 0x1703) (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x171b (by decide +kernel)
    md5_run_then (Stores.mov_m64_imm32_effect_step 0x10171b 0x48
      (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d32 152))
      (by decide) (by decide) (by decide) 0)
    case sub => exact codeRange_mem_of_drop (p := 0x101703) 24 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact h.toStorage.stackWritable 152 8 (by decide)
      · x86_norm
        exact h.toStorage.stackApart (codeOffset := 0x171b) (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64Imm32Effect_components 0x10171b (.sib 4 none 0 (.d32 152)) 0 t)
        change RangeApart (stackPtr t + 152) 8 0x101703 84
        rw [hsp]
        exact h.toStorage.stackApart (codeOffset := 0x1703) (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x1727 (by decide +kernel)
    md5_run_then (Stores.mov_m64_imm32_effect_step 0x101727 0x48
      (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d32 160))
      (by decide) (by decide) (by decide) 0)
    case sub => exact codeRange_mem_of_drop (p := 0x101703) 36 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact h.toStorage.stackWritable 160 8 (by decide)
      · x86_norm
        exact h.toStorage.stackApart (codeOffset := 0x1727) (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64Imm32Effect_components 0x101727 (.sib 4 none 0 (.d32 160)) 0 t)
        change RangeApart (stackPtr t + 160) 8 0x101703 84
        rw [hsp]
        exact h.toStorage.stackApart (codeOffset := 0x1703) (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x1733 (by decide +kernel)
    md5_run_then (Stores.mov_m64_imm32_effect_step 0x101733 0x48
      (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d32 168))
      (by decide) (by decide) (by decide) 0)
    case sub => exact codeRange_mem_of_drop (p := 0x101703) 48 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact h.toStorage.stackWritable 168 8 (by decide)
      · x86_norm
        exact h.toStorage.stackApart (codeOffset := 0x1733) (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64Imm32Effect_components 0x101733 (.sib 4 none 0 (.d32 168)) 0 t)
        change RangeApart (stackPtr t + 168) 8 0x101703 84
        rw [hsp]
        exact h.toStorage.stackApart (codeOffset := 0x1703) (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x173f (by decide +kernel)
    md5_run_then (Stores.mov_m64_imm32_effect_step 0x10173f 0x48
      (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d32 176))
      (by decide) (by decide) (by decide) 0)
    case sub => exact codeRange_mem_of_drop (p := 0x101703) 60 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact h.toStorage.stackWritable 176 8 (by decide)
      · x86_norm
        exact h.toStorage.stackApart (codeOffset := 0x173f) (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64Imm32Effect_components 0x10173f (.sib 4 none 0 (.d32 176)) 0 t)
        change RangeApart (stackPtr t + 176) 8 0x101703 84
        rw [hsp]
        exact h.toStorage.stackApart (codeOffset := 0x1703) (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x174b (by decide +kernel)
    md5_run_then (Stores.mov_m64_imm32_effect_step 0x10174b 0x48
      (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d32 184))
      (by decide) (by decide) (by decide) 0)
    case sub => exact codeRange_mem_of_drop (p := 0x101703) 72 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact h.toStorage.stackWritable 184 8 (by decide)
      · x86_norm
        exact h.toStorage.stackApart (codeOffset := 0x174b) (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64Imm32Effect_components 0x10174b (.sib 4 none 0 (.d32 184)) 0 t)
        change RangeApart (stackPtr t + 184) 8 0x101703 84
        rw [hsp]
        exact h.toStorage.stackApart (codeOffset := 0x1703) (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x1757 (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [effect]
    · x86_norm [effect, stackPtr]
      simp [Operand.read, Variant.tailOffset]
    · intro i; cases i <;> x86_norm [effect]
    · x86_norm [effect, stackPtr]
      simp [Operand.read, Variant.tailOffset]

end Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Padding.Clear
