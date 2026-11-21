import Md5.Proofs.Buffered.Update.Slices.Byte.Add
import Md5.Proofs.Buffered.Update.Slices.Byte.Store
import Md5.Proofs.Buffered.Update.Slices.Byte
import Md5.Proofs.Block.Execution
import Md5.Proofs.Block.Entry
import Md5.Proofs.Block.Rounds.Store.Compose
import Md5.Proofs.MemoryRoutines.Ranges

namespace Md5.Proofs.NewEntries.Reset.FirstUpdate

open Md5.Proofs.Buffered X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

def shortFinishBytes : List UInt8 :=
  [0x41, 0x00, 0xee, 0x44, 0x88, 0x74, 0x24, 0x5f]

def shortFinishEffect (s : RamState) : Effect :=
  let value := (.reg 14 : Operand 8).read s + (.reg 5 : Operand 8).read s
  { rip := 0x1013ec
    writes := [⟨(.reg 14 : Operand 64), mergeGPR 8 value ((.reg 14 : Operand 64).read s)⟩,
      ⟨(.mem (stackPtr s + 95) : Operand 8), value⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem short_finish [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x1013e4 ∧
      Md5.Proofs.Memory.MemWritable s (stackPtr s + 95) 1 ∧
      RangeApart (stackPtr s + 95) 1 0x1013e4 8)
      (codeRange 0x1013e4 shortFinishBytes) shortFinishEffect := by
  unfold shortFinishBytes
  md5_run_begin Update.Byte.add_r8_r8_effect_step 0x1013e4 0x41 0xee
    (by unfold RexPrefix; decide) (by decide)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x13e7 (by decide +kernel)
  md5_run_then Update.Byte.mov_m8_r8_rex_effect_step 0x1013e7 0x44
    (by unfold RexPrefix; decide) 6 (.sib 4 none 0 (.d8 95))
    (by decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x1013e4) 3 (by decide +kernel)
  case mid =>
    intro s t h hE hO
    have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
    refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
    · x86_norm
      exact h.2.1
    · x86_norm
      exact MemoryRoutines.rangeApart_slice_right h.2.2 3 5 (by decide)
    · apply Effect.avoids_of_components_mem_rip
        (storeEffect_components 0x1013e7 5
          (storeAddrAt 0x1013e7 (.sib 4 none 0 (.d8 95)) 5)
          (fun u ↦ (.reg 14 : Operand 8).read u) t)
      change RangeApart (stackPtr t + 95) 1 0x1013e4 8
      rw [hsp]
      exact h.2.2
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x13ec (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [shortFinishEffect]
  · x86_norm [shortFinishEffect, stackPtr]
    simp [gprNumber, rexB, rexR, modrmReg, modrmRm, Operand.read]
  · intro i; cases i <;> x86_norm [shortFinishEffect]
  · x86_norm [shortFinishEffect, stackPtr]
    rfl

end Md5.Proofs.NewEntries.Reset.FirstUpdate
