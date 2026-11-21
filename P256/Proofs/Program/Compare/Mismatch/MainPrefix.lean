import P256.Proofs.Program.Compare.Mismatch.Blocks
import P256.Proofs.Program.Compare.Mismatch.Comparisons
import P256.Proofs.Program.Compare.Mismatch.Arithmetic

namespace P256.Proofs.Program.Compare.Mismatch

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Spec.Program P256.Spec.Program.Routines

theorem main_select [Bindings] (boundary : ReturnBoundary) (s : RamState)
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programSections.toCodeMap s)
    (hb : RegisterBoundary boundary s) (hp : s.RIP = 0x11c8d0)
    (hne : (Operand.reg 0 : Operand 64).read s ≠ (Operand.reg 7 : Operand 64).read s ∨
      (Operand.reg 3 : Operand 64).read s ≠ (Operand.reg 14 : Operand 64).read s) :
    ∃ t, Run boundary s t ∧ t.RIP = 0x11c8e0 ∧
      (Operand.reg 0 : Operand 64).read t ≠ (Operand.reg 7 : Operand 64).read t := by
  obtain ⟨u, hu, hf, hip⟩ := main_first boundary s hr hc hb hp
  by_cases heq : (Operand.reg 0 : Operand 64).read s = (Operand.reg 7 : Operand 64).read s
  · have hne' : (Operand.reg 3 : Operand 64).read s ≠
        (Operand.reg 14 : Operand 64).read s := hne.resolve_left (not_not_intro heq)
    have hip' : u.RIP = 0x11c8d5 := by simpa only [heq, ite_true] using hip
    obtain ⟨v, hv, hfv, hipv⟩ := main_second boundary u hu.ready hu.code (hu.boundary hb) hip'
    have hne_u : (Operand.reg 3 : Operand 64).read u ≠
        (Operand.reg 14 : Operand 64).read u := by
      simpa only [hf.read (r := 3) (n := 64) (by simp),
        hf.read (r := 14) (n := 64) (by simp)] using hne'
    have hipv' : v.RIP = 0x11c8da := by simpa only [ite_eq_right hne_u] using hipv
    obtain ⟨t, ht, he⟩ := run_block select_second_block hv.ready hv.code
      (hv.boundary (hu.boundary hb)) hipv'
      (program_text_slice hv.code 0x1c8da 6 (by decide +kernel))
      (by simp [selectSecondEffect, Effect.components, changes, Write.component, Operand.component])
    refine ⟨t, hu.trans (hv.trans ht), he.rip, ?_⟩
    have ha := he.writes.1
    have hg := he.writes.2
    change (Operand.reg 0 : Operand 64).read t = (Operand.reg 3 : Operand 64).read v at ha
    change (Operand.reg 7 : Operand 64).read t = (Operand.reg 14 : Operand 64).read v at hg
    rw [ha, hg, hfv.read (by simp), hfv.read (by simp)]
    exact hne_u
  · refine ⟨u, hu, by simpa only [ite_eq_right heq] using hip, ?_⟩
    simpa only [hf.read (r := 0) (n := 64) (by simp),
      hf.read (r := 7) (n := 64) (by simp)] using heq

theorem main_byte_subtract [Bindings] (boundary : ReturnBoundary) (s : RamState)
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programSections.toCodeMap s)
    (hb : RegisterBoundary boundary s) (hp : s.RIP = 0x11c91a)
    (hne : (Operand.reg 0 : Operand 8).read s ≠ (Operand.reg 7 : Operand 8).read s) :
    ∃ t, Run boundary s t ∧ t.RIP = 0x11c923 ∧ (Operand.reg 0 : Operand 32).read t ≠ 0 := by
  obtain ⟨t, ht, he⟩ := run_block main_subtract_block hr hc hb hp
    (program_text_slice hc 0x1c91a 9 (by decide +kernel))
    (by simp [mainSubtractEffect, Effect.components, changes, Write.component, Operand.component])
  refine ⟨t, ht, he.rip, ?_⟩
  have ha := congrArg (BitVec.setWidth 32) he.writes.1
  have ha' : (Operand.reg 0 : Operand 32).read t =
      ((Operand.reg 0 : Operand 8).read s).setWidth 32 -
        ((Operand.reg 7 : Operand 8).read s).setWidth 32 := by
    simpa only [mainSubtractEffect, register_setWidth _ _ _ _ (by decide : 32 ≤ 64),
      BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq] using ha
  rw [ha']
  exact byte_sub_ne_zero hne

end P256.Proofs.Program.Compare.Mismatch
