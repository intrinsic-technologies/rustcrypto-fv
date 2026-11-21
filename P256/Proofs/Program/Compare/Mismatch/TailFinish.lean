import P256.Proofs.Program.Compare.Mismatch.Blocks
import P256.Proofs.Program.Compare.Mismatch.Arithmetic

namespace P256.Proofs.Program.Compare.Mismatch

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Spec.Program P256.Spec.Program.Routines

theorem tail_subtract [Bindings] (boundary : ReturnBoundary) (s : RamState)
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programSections.toCodeMap s)
    (hb : RegisterBoundary boundary s) (hp : s.RIP = 0x11ce9c)
    (hne : (Operand.reg 0 : Operand 32).read s ≠ (Operand.reg 1 : Operand 32).read s) :
    ∃ t, Run boundary s t ∧ t.RIP = 0x11ce9e ∧ (Operand.reg 0 : Operand 32).read t ≠ 0 := by
  obtain ⟨t, ht, he⟩ := run_block tail_subtract_block hr hc hb hp
    (program_text_slice hc 0x1ce9c 2 (by decide +kernel))
    (by simp [tailSubtractEffect, Effect.components, changes, Write.component, Operand.component])
  refine ⟨t, ht, he.rip, ?_⟩
  have ha : (Operand.reg 0 : Operand 32).read t =
      (Operand.reg 0 : Operand 32).read s - (Operand.reg 1 : Operand 32).read s := by
    simpa only [tailSubtractEffect, register_setWidth _ _ _ _ (by decide : 32 ≤ 64),
      BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
      using congrArg (BitVec.setWidth 32) he.writes
  rw [ha]
  simpa [BitVec.sub_eq_iff_eq_add] using hne

theorem tail_jump [Bindings] (boundary : ReturnBoundary) (s : RamState)
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programSections.toCodeMap s)
    (hb : RegisterBoundary boundary s) (hp : s.RIP = 0x11ce4b) :
    ∃ t, Run boundary s t ∧ t.RIP = 0x11ce9c ∧ AgreesExcept [.rip] s t := by
  obtain ⟨t, ht, he⟩ := run_step (jmp_rel8_effect_step 0x11ce4b 0x4f (by decide +kernel))
    hr hc hb hp (program_text_slice hc 0x1ce4b 2 (by decide +kernel))
    (by simp [jmpEffect, Effect.components, changes]) (by constructor <;> decide +kernel)
  exact ⟨t, ht, by simpa [jmpEffect, branchEffect, branchTarget] using he.rip, he.agrees⟩

theorem four_jump [Bindings] (boundary : ReturnBoundary) (s : RamState)
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programSections.toCodeMap s)
    (hb : RegisterBoundary boundary s) (hp : s.RIP = 0x11ce76) :
    ∃ t, Run boundary s t ∧ t.RIP = 0x11ce98 ∧ AgreesExcept [.rip] s t := by
  obtain ⟨t, ht, he⟩ := run_step (jmp_rel8_effect_step 0x11ce76 0x20 (by decide +kernel))
    hr hc hb hp (program_text_slice hc 0x1ce76 2 (by decide +kernel))
    (by simp [jmpEffect, Effect.components, changes]) (by constructor <;> decide +kernel)
  exact ⟨t, ht, by simpa [jmpEffect, branchEffect, branchTarget] using he.rip, he.agrees⟩

theorem tail_byte_subtract [Bindings] (boundary : ReturnBoundary) (s : RamState)
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programSections.toCodeMap s)
    (hb : RegisterBoundary boundary s) (hp : s.RIP = 0x11ce44)
    (hne : (Operand.reg 0 : Operand 8).read s ≠ (Operand.reg 7 : Operand 8).read s) :
    ∃ t, Run boundary s t ∧ t.RIP = 0x11ce9e ∧ (Operand.reg 0 : Operand 32).read t ≠ 0 := by
  obtain ⟨u, hu, he⟩ := run_block tail_bytes_block hr hc hb hp
    (program_text_slice hc 0x1ce44 7 (by decide +kernel))
    (by simp [tailBytesEffect, Effect.components, changes, Write.component, Operand.component])
  obtain ⟨v, hv, hipv, hfv⟩ := tail_jump boundary u hu.ready hu.code (hu.boundary hb) he.rip
  have hneq : (Operand.reg 0 : Operand 32).read v ≠ (Operand.reg 1 : Operand 32).read v := by
    rw [hfv.read (by simp), hfv.read (by simp)]
    have ha := congrArg (BitVec.setWidth 32) he.writes.1
    have hd := congrArg (BitVec.setWidth 32) he.writes.2
    simp only [register_setWidth _ _ _ _ (by decide : 32 ≤ 64),
      BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64)] at ha hd
    rw [ha, hd]
    intro heq
    apply hne
    simpa only [BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32),
      BitVec.setWidth_eq] using congrArg (BitVec.setWidth 8) heq
  obtain ⟨t, ht, hip, hret⟩ := tail_subtract boundary v hv.ready hv.code
    (hv.boundary (hu.boundary hb)) hipv hneq
  exact ⟨t, hu.trans (hv.trans ht), hip, hret⟩

theorem right_byte_subtract [Bindings] (boundary : ReturnBoundary) (s : RamState)
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programSections.toCodeMap s)
    (hb : RegisterBoundary boundary s) (hp : s.RIP = 0x11ce98)
    (hne : (Operand.reg 0 : Operand 32).read s ≠
      ((Operand.reg 7 : Operand 8).read s).setWidth 32) :
    ∃ t, Run boundary s t ∧ t.RIP = 0x11ce9e ∧ (Operand.reg 0 : Operand 32).read t ≠ 0 := by
  obtain ⟨u, hu, he⟩ := run_block right_byte_block hr hc hb hp
    (program_text_slice hc 0x1ce98 4 (by decide +kernel))
    (by simp [rightByteEffect, Effect.components, changes, Write.component, Operand.component])
  have hneq : (Operand.reg 0 : Operand 32).read u ≠ (Operand.reg 1 : Operand 32).read u := by
    rw [he.agrees.read (by simp [rightByteEffect, Effect.components])]
    have ha := congrArg (BitVec.setWidth 32) he.writes
    simp only [register_setWidth _ _ _ _ (by decide : 32 ≤ 64),
      BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64)] at ha
    rwa [ha]
  obtain ⟨t, ht, hip, hret⟩ := tail_subtract boundary u hu.ready hu.code
    (hu.boundary hb) he.rip hneq
  exact ⟨t, hu.trans ht, hip, hret⟩

theorem four_byte_subtract [Bindings] (boundary : ReturnBoundary) (s : RamState)
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programSections.toCodeMap s)
    (hb : RegisterBoundary boundary s) (hp : s.RIP = 0x11ce72)
    (hne : (Operand.reg 6 : Operand 8).read s ≠ (Operand.reg 7 : Operand 8).read s) :
    ∃ t, Run boundary s t ∧ t.RIP = 0x11ce9e ∧ (Operand.reg 0 : Operand 32).read t ≠ 0 := by
  obtain ⟨u, hu, he⟩ := run_block four_byte_block hr hc hb hp
    (program_text_slice hc 0x1ce72 4 (by decide +kernel))
    (by simp [fourByteEffect, Effect.components, changes, Write.component, Operand.component])
  have hneq : (Operand.reg 0 : Operand 32).read u ≠
      ((Operand.reg 7 : Operand 8).read u).setWidth 32 := by
    rw [he.agrees.read (r := 7) (n := 8) (by simp [fourByteEffect, Effect.components])]
    have ha := congrArg (BitVec.setWidth 32) he.writes
    simp only [register_setWidth _ _ _ _ (by decide : 32 ≤ 64),
      BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64)] at ha
    rw [ha]
    intro heq
    apply hne
    simpa only [BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32),
      BitVec.setWidth_eq] using congrArg (BitVec.setWidth 8) heq
  obtain ⟨v, hv, hipv, hfv⟩ := four_jump boundary u hu.ready hu.code (hu.boundary hb) he.rip
  have hneqv : (Operand.reg 0 : Operand 32).read v ≠
      ((Operand.reg 7 : Operand 8).read v).setWidth 32 := by
    simpa only [hfv.read (r := 0) (n := 32) (by simp),
      hfv.read (r := 7) (n := 8) (by simp)] using hneq
  obtain ⟨t, ht, hip, hret⟩ := right_byte_subtract boundary v hv.ready hv.code
    (hv.boundary (hu.boundary hb)) hipv hneqv
  exact ⟨t, hu.trans (hv.trans ht), hip, hret⟩

theorem two_byte_subtract [Bindings] (boundary : ReturnBoundary) (s : RamState)
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programSections.toCodeMap s)
    (hb : RegisterBoundary boundary s) (hp : s.RIP = 0x11ce94)
    (hne : (Operand.reg 8 : Operand 8).read s ≠ (Operand.reg 7 : Operand 8).read s) :
    ∃ t, Run boundary s t ∧ t.RIP = 0x11ce9e ∧ (Operand.reg 0 : Operand 32).read t ≠ 0 := by
  obtain ⟨u, hu, he⟩ := run_block two_byte_block hr hc hb hp
    (program_text_slice hc 0x1ce94 4 (by decide +kernel))
    (by simp [twoByteEffect, Effect.components, changes, Write.component, Operand.component])
  have hneq : (Operand.reg 0 : Operand 32).read u ≠
      ((Operand.reg 7 : Operand 8).read u).setWidth 32 := by
    rw [he.agrees.read (r := 7) (n := 8) (by simp [twoByteEffect, Effect.components])]
    have ha := congrArg (BitVec.setWidth 32) he.writes
    simp only [register_setWidth _ _ _ _ (by decide : 32 ≤ 64),
      BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64)] at ha
    rw [ha]
    intro heq
    apply hne
    simpa only [BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32),
      BitVec.setWidth_eq] using congrArg (BitVec.setWidth 8) heq
  obtain ⟨t, ht, hip, hret⟩ := right_byte_subtract boundary u hu.ready hu.code
    (hu.boundary hb) he.rip hneq
  exact ⟨t, hu.trans ht, hip, hret⟩

end P256.Proofs.Program.Compare.Mismatch
