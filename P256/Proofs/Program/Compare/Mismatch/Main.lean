import P256.Proofs.Program.Compare.Mismatch.Stages
import P256.Proofs.Program.Compare.Mismatch.MainPrefix
import P256.Proofs.Program.Compare.Mismatch.TailFinish

namespace P256.Proofs.Program.Compare.Mismatch

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Spec.Program P256.Spec.Program.Routines

theorem main_mismatch [Bindings] (boundary : ReturnBoundary) (s : RamState)
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programSections.toCodeMap s)
    (hb : RegisterBoundary boundary s) (hp : s.RIP = 0x11c8d0)
    (hne : (Operand.reg 0 : Operand 64).read s ≠ (Operand.reg 7 : Operand 64).read s ∨
      (Operand.reg 3 : Operand 64).read s ≠ (Operand.reg 14 : Operand 64).read s) :
    ∃ t, Run boundary s t ∧ t.RIP = 0x11c923 ∧ (Operand.reg 0 : Operand 32).read t ≠ 0 := by
  obtain ⟨u, hu, hipu, hneu⟩ := main_select boundary s hr hc hb hp hne
  obtain ⟨s32, h32, hip32, hne32⟩ := mainStage32.run boundary u
    hu.ready hu.code (hu.boundary hb) hipu hneu
  obtain ⟨s16, h16, hip16, hne16⟩ := mainStage16.run boundary s32
    h32.ready h32.code (h32.boundary (hu.boundary hb)) hip32 hne32
  obtain ⟨s8, h8, hip8, hne8⟩ := mainStage8.run boundary s16
    h16.ready h16.code (h16.boundary (h32.boundary (hu.boundary hb))) hip16 hne16
  obtain ⟨t, ht, hipt, hnet⟩ := main_byte_subtract boundary s8
    h8.ready h8.code (h8.boundary (h16.boundary (h32.boundary (hu.boundary hb)))) hip8 hne8
  exact ⟨t, hu.trans (h32.trans (h16.trans (h8.trans ht))), hipt, hnet⟩

theorem tail_mismatch [Bindings] (boundary : ReturnBoundary) (s : RamState)
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programSections.toCodeMap s)
    (hb : RegisterBoundary boundary s) (hp : s.RIP = 0x11ce0e)
    (hne : (Operand.reg 0 : Operand 64).read s ≠ (Operand.reg 7 : Operand 64).read s) :
    ∃ t, Run boundary s t ∧ t.RIP = 0x11ce9e ∧ (Operand.reg 0 : Operand 32).read t ≠ 0 := by
  obtain ⟨s32, h32, hip32, hne32⟩ := tailStage32.run boundary s
    hr hc hb hp hne
  obtain ⟨s16, h16, hip16, hne16⟩ := tailStage16.run boundary s32
    h32.ready h32.code (h32.boundary hb) hip32 hne32
  obtain ⟨s8, h8, hip8, hne8⟩ := tailStage8.run boundary s16
    h16.ready h16.code (h16.boundary (h32.boundary hb)) hip16 hne16
  obtain ⟨t, ht, hipt, hnet⟩ := tail_byte_subtract boundary s8
    h8.ready h8.code (h8.boundary (h16.boundary (h32.boundary hb))) hip8 hne8
  exact ⟨t, h32.trans (h16.trans (h8.trans ht)), hipt, hnet⟩

theorem four_mismatch [Bindings] (boundary : ReturnBoundary) (s : RamState)
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programSections.toCodeMap s)
    (hb : RegisterBoundary boundary s) (hp : s.RIP = 0x11ce4d)
    (hne : (Operand.reg 6 : Operand 32).read s ≠ (Operand.reg 7 : Operand 32).read s) :
    ∃ t, Run boundary s t ∧ t.RIP = 0x11ce9e ∧ (Operand.reg 0 : Operand 32).read t ≠ 0 := by
  obtain ⟨s16, h16, hip16, hne16⟩ := fourStage16.run boundary s
    hr hc hb hp hne
  obtain ⟨s8, h8, hip8, hne8⟩ := fourStage8.run boundary s16
    h16.ready h16.code (h16.boundary hb) hip16 hne16
  obtain ⟨t, ht, hipt, hnet⟩ := four_byte_subtract boundary s8
    h8.ready h8.code (h8.boundary (h16.boundary hb)) hip8 hne8
  exact ⟨t, h16.trans (h8.trans ht), hipt, hnet⟩

theorem two_mismatch [Bindings] (boundary : ReturnBoundary) (s : RamState)
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programSections.toCodeMap s)
    (hb : RegisterBoundary boundary s) (hp : s.RIP = 0x11ce78)
    (hne : (Operand.reg 8 : Operand 16).read s ≠ (Operand.reg 7 : Operand 16).read s) :
    ∃ t, Run boundary s t ∧ t.RIP = 0x11ce9e ∧ (Operand.reg 0 : Operand 32).read t ≠ 0 := by
  obtain ⟨s8, h8, hip8, hne8⟩ := twoStage8.run boundary s
    hr hc hb hp hne
  obtain ⟨t, ht, hipt, hnet⟩ := two_byte_subtract boundary s8
    h8.ready h8.code (h8.boundary hb) hip8 hne8
  exact ⟨t, h8.trans ht, hipt, hnet⟩

end P256.Proofs.Program.Compare.Mismatch
