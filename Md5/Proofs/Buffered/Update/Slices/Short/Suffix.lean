import Md5.Proofs.Buffered.Update.Slices.Entry
import Md5.Proofs.Buffered.Update.Slices.Byte
import Md5.Proofs.Block.Execution
import Md5.Proofs.Block.Entry
import Md5.Proofs.Block.Rounds.Store.Compose
import Md5.Proofs.MemoryRoutines.Ranges

namespace Md5.Proofs.Buffered.Update.Slices

open X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

def shortSuffixBytes : List UInt8 :=
  [0x44, 0x00, 0xeb, 0x88, 0x9c, 0x24, 0xff, 0x00, 0x00, 0x00]

def shortSuffixEffect (variant : Bool) (s : RamState) : Effect :=
  let value := (.reg 3 : Operand 8).read s + (.reg 13 : Operand 8).read s
  { rip := pc variant 0x100331
    writes := [⟨(.reg 3 : Operand 64), mergeGPR 8 value ((.reg 3 : Operand 64).read s)⟩,
      ⟨(.mem (stackPtr s + 255) : Operand 8), value⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem short_suffix [Bindings] {variant : Bool} (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = (pc variant 0x100327) ∧
      Md5.Proofs.Memory.MemWritable s (stackPtr s + 255) 1 ∧
      RangeApart (stackPtr s + 255) 1 (pc variant 0x100327) 10)
      (codeRange (pc variant 0x100327) shortSuffixBytes) (shortSuffixEffect variant) := by
  cases variant
  case false =>
    simp only [pc]
    unfold shortSuffixBytes
    md5_run_begin Byte.add_r8_r8_effect_step 0x100327 0x44 0xeb
      (by unfold RexPrefix; decide) (by decide)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x32a (by decide +kernel)
    md5_run_then Byte.mov_m8_r8_effect_step 0x10032a
      3 (.sib 4 none 0 (.d32 255))
      (by decide) (by decide) (by decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x100327) 3 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact h.2.1
      · x86_norm
        exact MemoryRoutines.rangeApart_slice_right h.2.2 3 7 (by decide)
      · apply Effect.avoids_of_components_mem_rip
          (storeEffect_components 0x10032a 7
            (storeAddrAt 0x10032a (.sib 4 none 0 (.d32 255)) 7)
            (fun u ↦ (.reg 3 : Operand 8).read u) t)
        change RangeApart (stackPtr t + 255) 1 0x100327 10
        rw [hsp]
        exact h.2.2
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x331 (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [shortSuffixEffect, pc]
    · x86_norm [shortSuffixEffect, pc, stackPtr]
      simp [gprNumber, rexB, rexR, modrmReg, modrmRm, Operand.read]
    · intro i; cases i <;> x86_norm [shortSuffixEffect, pc]
    · x86_norm [shortSuffixEffect, pc, stackPtr]
      rfl
  case true =>
    simp only [pc]
    unfold shortSuffixBytes
    md5_run_begin Byte.add_r8_r8_effect_step 0x1018d7 0x44 0xeb
      (by unfold RexPrefix; decide) (by decide)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x18da (by decide +kernel)
    md5_run_then Byte.mov_m8_r8_effect_step 0x1018da
      3 (.sib 4 none 0 (.d32 255))
      (by decide) (by decide) (by decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x1018d7) 3 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact h.2.1
      · x86_norm
        exact MemoryRoutines.rangeApart_slice_right h.2.2 3 7 (by decide)
      · apply Effect.avoids_of_components_mem_rip
          (storeEffect_components 0x1018da 7
            (storeAddrAt 0x1018da (.sib 4 none 0 (.d32 255)) 7)
            (fun u ↦ (.reg 3 : Operand 8).read u) t)
        change RangeApart (stackPtr t + 255) 1 0x1018d7 10
        rw [hsp]
        exact h.2.2
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x18e1 (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [shortSuffixEffect, pc]
    · x86_norm [shortSuffixEffect, pc, stackPtr]
      simp [gprNumber, rexB, rexR, modrmReg, modrmRm, Operand.read]
    · intro i; cases i <;> x86_norm [shortSuffixEffect, pc]
    · x86_norm [shortSuffixEffect, pc, stackPtr]
      rfl

end Md5.Proofs.Buffered.Update.Slices
