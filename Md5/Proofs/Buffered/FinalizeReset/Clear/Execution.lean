import Md5.Proofs.Buffered.FinalizeReset.Length.Execution

namespace Md5.Proofs.Buffered.FinalizeReset.Clear

open X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

def bytes : List UInt8 :=
  [0x48, 0xc7, 0x44, 0x24, 0x8, 0x0, 0x0, 0x0, 0x0,
   0x48, 0xc7, 0x44, 0x24, 0x10, 0x0, 0x0, 0x0, 0x0,
   0x48, 0xc7, 0x44, 0x24, 0x18, 0x0, 0x0, 0x0, 0x0,
   0x48, 0xc7, 0x44, 0x24, 0x20, 0x0, 0x0, 0x0, 0x0,
   0x48, 0xc7, 0x44, 0x24, 0x28, 0x0, 0x0, 0x0, 0x0,
   0x48, 0xc7, 0x44, 0x24, 0x30, 0x0, 0x0, 0x0, 0x0,
   0x48, 0xc7, 0x44, 0x24, 0x38, 0x0, 0x0, 0x0, 0x0]

structure RunPre (s : RamState) (variant : Variant := .saved) : Prop extends Storage s variant where
  rip : s.RIP = (variant.address 0x100863)

def effect (s : RamState) (variant : Variant := .saved) : Effect :=
  { rip := (variant.address 0x1008a2)
    writes := [
      ⟨(.mem (stackPtr s + 8) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 16) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 24) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 32) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 40) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 48) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 56) : Operand 64), 0⟩] }

local macro "clear_execution" hout:term "," pc0:term "," pc1:term "," pc2:term "," pc3:term "," pc4:term "," pc5:term "," pc6:term "," pc7:term "," pc8:term "," pc9:term "," pc10:term "," pc11:term "," pc12:term "," pc13:term "," pc14:term : tactic =>
  `(tactic| (
    unfold bytes
    md5_run_begin (Stores.mov_m64_imm32_effect_step $pc8 0x48
      (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d8 8))
      (by decide) (by decide) (by decide) 0)
    case pre =>
      intro s h
      exact ⟨h.rip, Export.stackWritable h.toStorage 8 8 (by decide),
        Export.stackTextApart h.toStorage _ _ $pc0 _ (by decide) (by decide +kernel)⟩
    case av =>
      intro s h
      apply Effect.avoids_of_components_mem_rip
        (movM64Imm32Effect_components $pc8 (.sib 4 none 0 (.d8 8)) 0 s)
      exact Export.stackTextApart h.toStorage _ _ $pc0 _ (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return $hout $pc1 (by decide +kernel)
    md5_run_then (Stores.mov_m64_imm32_effect_step $pc9 0x48
      (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d8 16))
      (by decide) (by decide) (by decide) 0)
    case sub => exact codeRange_mem_of_drop (p := $pc8) 9 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact Export.stackWritable h.toStorage 16 8 (by decide)
      · x86_norm
        exact Export.stackTextApart h.toStorage _ _ $pc1 _ (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64Imm32Effect_components $pc9 (.sib 4 none 0 (.d8 16)) 0 t)
        change RangeApart (stackPtr t + 16) 8 $pc8 63
        rw [hsp]
        exact Export.stackTextApart h.toStorage _ _ $pc0 _ (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return $hout $pc2 (by decide +kernel)
    md5_run_then (Stores.mov_m64_imm32_effect_step $pc10 0x48
      (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d8 24))
      (by decide) (by decide) (by decide) 0)
    case sub => exact codeRange_mem_of_drop (p := $pc8) 18 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact Export.stackWritable h.toStorage 24 8 (by decide)
      · x86_norm
        exact Export.stackTextApart h.toStorage _ _ $pc2 _ (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64Imm32Effect_components $pc10 (.sib 4 none 0 (.d8 24)) 0 t)
        change RangeApart (stackPtr t + 24) 8 $pc8 63
        rw [hsp]
        exact Export.stackTextApart h.toStorage _ _ $pc0 _ (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return $hout $pc3 (by decide +kernel)
    md5_run_then (Stores.mov_m64_imm32_effect_step $pc11 0x48
      (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d8 32))
      (by decide) (by decide) (by decide) 0)
    case sub => exact codeRange_mem_of_drop (p := $pc8) 27 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact Export.stackWritable h.toStorage 32 8 (by decide)
      · x86_norm
        exact Export.stackTextApart h.toStorage _ _ $pc3 _ (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64Imm32Effect_components $pc11 (.sib 4 none 0 (.d8 32)) 0 t)
        change RangeApart (stackPtr t + 32) 8 $pc8 63
        rw [hsp]
        exact Export.stackTextApart h.toStorage _ _ $pc0 _ (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return $hout $pc4 (by decide +kernel)
    md5_run_then (Stores.mov_m64_imm32_effect_step $pc12 0x48
      (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d8 40))
      (by decide) (by decide) (by decide) 0)
    case sub => exact codeRange_mem_of_drop (p := $pc8) 36 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact Export.stackWritable h.toStorage 40 8 (by decide)
      · x86_norm
        exact Export.stackTextApart h.toStorage _ _ $pc4 _ (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64Imm32Effect_components $pc12 (.sib 4 none 0 (.d8 40)) 0 t)
        change RangeApart (stackPtr t + 40) 8 $pc8 63
        rw [hsp]
        exact Export.stackTextApart h.toStorage _ _ $pc0 _ (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return $hout $pc5 (by decide +kernel)
    md5_run_then (Stores.mov_m64_imm32_effect_step $pc13 0x48
      (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d8 48))
      (by decide) (by decide) (by decide) 0)
    case sub => exact codeRange_mem_of_drop (p := $pc8) 45 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact Export.stackWritable h.toStorage 48 8 (by decide)
      · x86_norm
        exact Export.stackTextApart h.toStorage _ _ $pc5 _ (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64Imm32Effect_components $pc13 (.sib 4 none 0 (.d8 48)) 0 t)
        change RangeApart (stackPtr t + 48) 8 $pc8 63
        rw [hsp]
        exact Export.stackTextApart h.toStorage _ _ $pc0 _ (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return $hout $pc6 (by decide +kernel)
    md5_run_then (Stores.mov_m64_imm32_effect_step $pc14 0x48
      (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d8 56))
      (by decide) (by decide) (by decide) 0)
    case sub => exact codeRange_mem_of_drop (p := $pc8) 54 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact Export.stackWritable h.toStorage 56 8 (by decide)
      · x86_norm
        exact Export.stackTextApart h.toStorage _ _ $pc6 _ (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64Imm32Effect_components $pc14 (.sib 4 none 0 (.d8 56)) 0 t)
        change RangeApart (stackPtr t + 56) 8 $pc8 63
        rw [hsp]
        exact Export.stackTextApart h.toStorage _ _ $pc0 _ (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return $hout $pc7 (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [effect]
    · x86_norm [effect, stackPtr]
      simp [Operand.read]
    · intro i; cases i <;> x86_norm [effect]
    · x86_norm [effect, stackPtr]
      simp [Operand.read]))

set_option maxHeartbeats 800000 in
theorem execution {variant : Variant} [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ RunPre s variant) (codeRange (variant.address 0x100863) bytes) (fun s ↦ effect s variant) := by
  cases variant with
  | saved => clear_execution hOutside, 0x863, 0x86c, 0x875, 0x87e, 0x887, 0x890, 0x899, 0x8a2, 0x100863, 0x10086c, 0x100875, 0x10087e, 0x100887, 0x100890, 0x100899
  | direct => clear_execution hOutside, 0xf13, 0xf1c, 0xf25, 0xf2e, 0xf37, 0xf40, 0xf49, 0xf52, 0x100f13, 0x100f1c, 0x100f25, 0x100f2e, 0x100f37, 0x100f40, 0x100f49

end Md5.Proofs.Buffered.FinalizeReset.Clear
