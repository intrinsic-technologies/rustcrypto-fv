import P256.Proofs.Program.Compare.Mismatch.Blocks

namespace P256.Proofs.Program.Compare.Mismatch

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Spec.Program P256.Spec.Program.Routines

theorem upper_byte_setWidth (x : BitVec 16) :
    ((x.setWidth 32 >>> 8).setWidth 64).setWidth 8 = (x >>> 8).setWidth 8 := by
  rw [← BitVec.setWidth_ushiftRight (by decide : 16 ≤ 32)]
  simp only [BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64),
    BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32)]

theorem main_shift16 [Bindings] (boundary : ReturnBoundary) (s : RamState)
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programSections.toCodeMap s)
    (hb : RegisterBoundary boundary s) (hp : s.RIP = 0x11c8f6) :
    ∃ t, Run boundary s t ∧ t.RIP = 0x11c8fc ∧
      (Operand.reg 0 : Operand 16).read t =
        ((Operand.reg 0 : Operand 32).read s >>> 16).setWidth 16 ∧
      (Operand.reg 7 : Operand 16).read t =
        ((Operand.reg 7 : Operand 32).read s >>> 16).setWidth 16 := by
  obtain ⟨t, ht, he⟩ := run_block main_high16_block hr hc hb hp
    (program_text_slice hc 0x1c8f6 6 (by decide +kernel))
    (by simp [mainHigh16Effect, Effect.components, changes, Write.component, Operand.component])
  refine ⟨t, ht, he.rip, ?_, ?_⟩
  · simpa only [register_setWidth _ _ _ _ (by decide : 16 ≤ 64),
        BitVec.setWidth_setWidth_of_le _ (by decide : 16 ≤ 64)]
      using congrArg (BitVec.setWidth 16) he.writes.2
  · simpa only [register_setWidth _ _ _ _ (by decide : 16 ≤ 64),
        BitVec.setWidth_setWidth_of_le _ (by decide : 16 ≤ 64)]
      using congrArg (BitVec.setWidth 16) he.writes.1

theorem tail_shift16 [Bindings] (boundary : ReturnBoundary) (s : RamState)
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programSections.toCodeMap s)
    (hb : RegisterBoundary boundary s) (hp : s.RIP = 0x11ce24) :
    ∃ t, Run boundary s t ∧ t.RIP = 0x11ce2a ∧
      (Operand.reg 0 : Operand 16).read t =
        ((Operand.reg 0 : Operand 32).read s >>> 16).setWidth 16 ∧
      (Operand.reg 7 : Operand 16).read t =
        ((Operand.reg 7 : Operand 32).read s >>> 16).setWidth 16 := by
  obtain ⟨t, ht, he⟩ := run_block tail_high16_block hr hc hb hp
    (program_text_slice hc 0x1ce24 6 (by decide +kernel))
    (by simp [tailHigh16Effect, Effect.components, changes, Write.component, Operand.component])
  refine ⟨t, ht, he.rip, ?_, ?_⟩
  · simpa only [register_setWidth _ _ _ _ (by decide : 16 ≤ 64),
        BitVec.setWidth_setWidth_of_le _ (by decide : 16 ≤ 64)]
      using congrArg (BitVec.setWidth 16) he.writes.2
  · simpa only [register_setWidth _ _ _ _ (by decide : 16 ≤ 64),
        BitVec.setWidth_setWidth_of_le _ (by decide : 16 ≤ 64)]
      using congrArg (BitVec.setWidth 16) he.writes.1

theorem four_shift16 [Bindings] (boundary : ReturnBoundary) (s : RamState)
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programSections.toCodeMap s)
    (hb : RegisterBoundary boundary s) (hp : s.RIP = 0x11ce52) :
    ∃ t, Run boundary s t ∧ t.RIP = 0x11ce58 ∧
      (Operand.reg 6 : Operand 16).read t =
        ((Operand.reg 6 : Operand 32).read s >>> 16).setWidth 16 ∧
      (Operand.reg 7 : Operand 16).read t =
        ((Operand.reg 7 : Operand 32).read s >>> 16).setWidth 16 := by
  obtain ⟨t, ht, he⟩ := run_block four_high16_block hr hc hb hp
    (program_text_slice hc 0x1ce52 6 (by decide +kernel))
    (by simp [fourHigh16Effect, Effect.components, changes, Write.component, Operand.component])
  refine ⟨t, ht, he.rip, ?_, ?_⟩
  · simpa only [register_setWidth _ _ _ _ (by decide : 16 ≤ 64),
        BitVec.setWidth_setWidth_of_le _ (by decide : 16 ≤ 64)]
      using congrArg (BitVec.setWidth 16) he.writes.2
  · simpa only [register_setWidth _ _ _ _ (by decide : 16 ≤ 64),
        BitVec.setWidth_setWidth_of_le _ (by decide : 16 ≤ 64)]
      using congrArg (BitVec.setWidth 16) he.writes.1

theorem main_shift8 [Bindings] (boundary : ReturnBoundary) (s : RamState)
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programSections.toCodeMap s)
    (hb : RegisterBoundary boundary s) (hp : s.RIP = 0x11c905) :
    ∃ t, Run boundary s t ∧ t.RIP = 0x11c911 ∧
      (Operand.reg 0 : Operand 8).read t =
        ((Operand.reg 0 : Operand 16).read s >>> 8).setWidth 8 ∧
      (Operand.reg 7 : Operand 8).read t =
        ((Operand.reg 7 : Operand 16).read s >>> 8).setWidth 8 := by
  obtain ⟨t, ht, he⟩ := run_block main_high8_block hr hc hb hp
    (program_text_slice hc 0x1c905 12 (by decide +kernel))
    (by simp [mainHigh8Effect, Effect.components, changes, Write.component, Operand.component])
  refine ⟨t, ht, he.rip, ?_, ?_⟩
  · simpa only [register_setWidth _ _ _ _ (by decide : 8 ≤ 64), upper_byte_setWidth]
      using congrArg (BitVec.setWidth 8) he.writes.2
  · simpa only [register_setWidth _ _ _ _ (by decide : 8 ≤ 64), upper_byte_setWidth]
      using congrArg (BitVec.setWidth 8) he.writes.1

theorem tail_shift8 [Bindings] (boundary : ReturnBoundary) (s : RamState)
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programSections.toCodeMap s)
    (hb : RegisterBoundary boundary s) (hp : s.RIP = 0x11ce33) :
    ∃ t, Run boundary s t ∧ t.RIP = 0x11ce3f ∧
      (Operand.reg 0 : Operand 8).read t =
        ((Operand.reg 0 : Operand 16).read s >>> 8).setWidth 8 ∧
      (Operand.reg 7 : Operand 8).read t =
        ((Operand.reg 7 : Operand 16).read s >>> 8).setWidth 8 := by
  obtain ⟨t, ht, he⟩ := run_block tail_high8_block hr hc hb hp
    (program_text_slice hc 0x1ce33 12 (by decide +kernel))
    (by simp [tailHigh8Effect, Effect.components, changes, Write.component, Operand.component])
  refine ⟨t, ht, he.rip, ?_, ?_⟩
  · simpa only [register_setWidth _ _ _ _ (by decide : 8 ≤ 64), upper_byte_setWidth]
      using congrArg (BitVec.setWidth 8) he.writes.2
  · simpa only [register_setWidth _ _ _ _ (by decide : 8 ≤ 64), upper_byte_setWidth]
      using congrArg (BitVec.setWidth 8) he.writes.1

theorem four_shift8 [Bindings] (boundary : ReturnBoundary) (s : RamState)
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programSections.toCodeMap s)
    (hb : RegisterBoundary boundary s) (hp : s.RIP = 0x11ce61) :
    ∃ t, Run boundary s t ∧ t.RIP = 0x11ce6d ∧
      (Operand.reg 6 : Operand 8).read t =
        ((Operand.reg 6 : Operand 16).read s >>> 8).setWidth 8 ∧
      (Operand.reg 7 : Operand 8).read t =
        ((Operand.reg 7 : Operand 16).read s >>> 8).setWidth 8 := by
  obtain ⟨t, ht, he⟩ := run_block four_high8_block hr hc hb hp
    (program_text_slice hc 0x1ce61 12 (by decide +kernel))
    (by simp [fourHigh8Effect, Effect.components, changes, Write.component, Operand.component])
  refine ⟨t, ht, he.rip, ?_, ?_⟩
  · simpa only [register_setWidth _ _ _ _ (by decide : 8 ≤ 64), upper_byte_setWidth]
      using congrArg (BitVec.setWidth 8) he.writes.2
  · simpa only [register_setWidth _ _ _ _ (by decide : 8 ≤ 64), upper_byte_setWidth]
      using congrArg (BitVec.setWidth 8) he.writes.1

theorem two_shift8 [Bindings] (boundary : ReturnBoundary) (s : RamState)
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programSections.toCodeMap s)
    (hb : RegisterBoundary boundary s) (hp : s.RIP = 0x11ce7d) :
    ∃ t, Run boundary s t ∧ t.RIP = 0x11ce8b ∧
      (Operand.reg 8 : Operand 8).read t =
        ((Operand.reg 8 : Operand 16).read s >>> 8).setWidth 8 ∧
      (Operand.reg 7 : Operand 8).read t =
        ((Operand.reg 7 : Operand 16).read s >>> 8).setWidth 8 := by
  obtain ⟨t, ht, he⟩ := run_block two_high8_block hr hc hb hp
    (program_text_slice hc 0x1ce7d 14 (by decide +kernel))
    (by simp [twoHigh8Effect, Effect.components, changes, Write.component, Operand.component])
  refine ⟨t, ht, he.rip, ?_, ?_⟩
  · simpa only [register_setWidth _ _ _ _ (by decide : 8 ≤ 64), upper_byte_setWidth]
      using congrArg (BitVec.setWidth 8) he.writes.2
  · simpa only [register_setWidth _ _ _ _ (by decide : 8 ≤ 64), upper_byte_setWidth]
      using congrArg (BitVec.setWidth 8) he.writes.1

end P256.Proofs.Program.Compare.Mismatch
