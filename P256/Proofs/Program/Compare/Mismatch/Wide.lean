import P256.Proofs.Program.Compare.Mismatch.Blocks
import P256.Proofs.Program.Compare.Mismatch.Comparisons
import P256.Proofs.Program.Compare.Mismatch.Narrowing

namespace P256.Proofs.Program.Compare.Mismatch

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Spec.Program P256.Spec.Program.Routines

def mainStage32 [Bindings] : NarrowingStage 32 0 7 0x11c8e0 0x11c8f1 where
  shiftEntry := 0x11c8e4
  shiftedEntry := 0x11c8ec
  equalExit := 0x11c916
  lowCompare := main_low32
  shift := by
    intro boundary s hr hc hb hp
    obtain ⟨t, ht, he⟩ := run_block main_high32_block hr hc hb hp
      (program_text_slice hc 0x1c8e4 8 (by decide +kernel))
      (by simp [mainHigh32Effect, Effect.components, changes, Write.component, Operand.component])
    refine ⟨t, ht, he.rip, ?_, ?_⟩
    · simpa only [mainHigh32Effect, register_setWidth _ _ _ _ (by decide : 32 ≤ 64)]
        using congrArg (BitVec.setWidth 32) he.writes.2
    · simpa only [mainHigh32Effect, register_setWidth _ _ _ _ (by decide : 32 ≤ 64)]
        using congrArg (BitVec.setWidth 32) he.writes.1
  highCompare := main_shifted32

def tailStage32 [Bindings] : NarrowingStage 32 0 7 0x11ce0e 0x11ce1f where
  shiftEntry := 0x11ce12
  shiftedEntry := 0x11ce1a
  equalExit := 0x11ce91
  lowCompare := tail_low32
  shift := by
    intro boundary s hr hc hb hp
    obtain ⟨t, ht, he⟩ := run_block tail_high32_block hr hc hb hp
      (program_text_slice hc 0x1ce12 8 (by decide +kernel))
      (by simp [tailHigh32Effect, Effect.components, changes, Write.component, Operand.component])
    refine ⟨t, ht, he.rip, ?_, ?_⟩
    · simpa only [tailHigh32Effect, register_setWidth _ _ _ _ (by decide : 32 ≤ 64)]
        using congrArg (BitVec.setWidth 32) he.writes.2
    · simpa only [tailHigh32Effect, register_setWidth _ _ _ _ (by decide : 32 ≤ 64)]
        using congrArg (BitVec.setWidth 32) he.writes.1
  highCompare := tail_shifted32

end P256.Proofs.Program.Compare.Mismatch
