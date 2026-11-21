import P256.Proofs.Program.Compare.Mismatch.Support
import P256.Proofs.Program.Compare.Mismatch.Arithmetic

namespace P256.Proofs.Program.Compare.Mismatch

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Spec.Program P256.Spec.Program.Routines

theorem wider_register_ne {s : RamState} {n m : Nat} {left right : BitVec 5}
    (h : n ≤ m)
    (hne : (Operand.reg left : Operand n).read s ≠ (Operand.reg right : Operand n).read s) :
    (Operand.reg left : Operand m).read s ≠ (Operand.reg right : Operand m).read s := by
  intro he
  apply hne
  simpa only [register_setWidth _ _ _ _ h] using congrArg (BitVec.setWidth n) he

structure NarrowingStage [Bindings] (width : Nat) (left right : BitVec 5)
    (entry exit : BitVec 64) where
  shiftEntry : BitVec 64
  shiftedEntry : BitVec 64
  equalExit : BitVec 64
  lowCompare : ∀ (boundary : ReturnBoundary) (s : RamState), ReadyToStep s →
    CodeIn Extracted.programSections.toCodeMap s → RegisterBoundary boundary s → s.RIP = entry →
    ∃ t, Run boundary s t ∧ AgreesExcept [.flags, .rip] s t ∧
      t.RIP = if (Operand.reg left : Operand width).read s =
        (Operand.reg right : Operand width).read s then shiftEntry else exit
  shift : ∀ (boundary : ReturnBoundary) (s : RamState), ReadyToStep s →
    CodeIn Extracted.programSections.toCodeMap s → RegisterBoundary boundary s → s.RIP = shiftEntry →
    ∃ t, Run boundary s t ∧ t.RIP = shiftedEntry ∧
      (Operand.reg left : Operand width).read t =
        (((Operand.reg left : Operand (width + width)).read s) >>> width).setWidth width ∧
      (Operand.reg right : Operand width).read t =
        (((Operand.reg right : Operand (width + width)).read s) >>> width).setWidth width
  highCompare : ∀ (boundary : ReturnBoundary) (s : RamState), ReadyToStep s →
    CodeIn Extracted.programSections.toCodeMap s → RegisterBoundary boundary s → s.RIP = shiftedEntry →
    ∃ t, Run boundary s t ∧ AgreesExcept [.flags, .rip] s t ∧
      t.RIP = if (Operand.reg left : Operand (width + width)).read s =
        (Operand.reg right : Operand (width + width)).read s then equalExit else exit

theorem NarrowingStage.run [Bindings] {width : Nat} {left right : BitVec 5}
    {entry exit : BitVec 64} (stage : NarrowingStage width left right entry exit)
    (boundary : ReturnBoundary) (s : RamState) (hr : ReadyToStep s)
    (hc : CodeIn Extracted.programSections.toCodeMap s) (hb : RegisterBoundary boundary s) (hp : s.RIP = entry)
    (hne : (Operand.reg left : Operand (width + width)).read s ≠
      (Operand.reg right : Operand (width + width)).read s) :
    ∃ t, Run boundary s t ∧ t.RIP = exit ∧
      (Operand.reg left : Operand width).read t ≠ (Operand.reg right : Operand width).read t := by
  obtain ⟨u, hu, hfu, hipu⟩ := stage.lowCompare boundary s hr hc hb hp
  by_cases heq : (Operand.reg left : Operand width).read s =
      (Operand.reg right : Operand width).read s
  · have hpu : u.RIP = stage.shiftEntry := by simpa only [ite_eq_left heq] using hipu
    obtain ⟨v, hv, hipv, hl, hg⟩ := stage.shift boundary u hu.ready hu.code (hu.boundary hb) hpu
    have hneqv : (Operand.reg left : Operand width).read v ≠
        (Operand.reg right : Operand width).read v := by
      rw [hl, hg, hfu.read (by simp), hfu.read (by simp)]
      apply shifted_half_ne hne
      simpa only [register_setWidth _ _ _ _ (by omega : width ≤ width + width)] using heq
    obtain ⟨t, ht, hft, hipt⟩ :=
      stage.highCompare boundary v hv.ready hv.code (hv.boundary (hu.boundary hb)) hipv
    refine ⟨t, hu.trans (hv.trans ht), ?_, ?_⟩
    · simpa only [ite_eq_right (wider_register_ne (by omega : width ≤ width + width) hneqv)] using hipt
    · simpa only [hft.read (r := left) (n := width) (by simp),
        hft.read (r := right) (n := width) (by simp)] using hneqv
  · refine ⟨u, hu, by simpa only [ite_eq_right heq] using hipu, ?_⟩
    simpa only [hfu.read (r := left) (n := width) (by simp),
      hfu.read (r := right) (n := width) (by simp)] using heq

end P256.Proofs.Program.Compare.Mismatch
