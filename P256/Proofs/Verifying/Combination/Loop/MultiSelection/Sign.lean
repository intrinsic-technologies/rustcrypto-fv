import P256.Proofs.Verifying.Combination.Loop.MultiSelection.Arithmetic
import P256.Proofs.Verifying.Combination.Loop.MultiSelection.State
import P256.Proofs.Verifying.Combination.Naf.Iterator.Advance.Branch
import P256.Proofs.Common.Encoding.Serialize.Tail.ByteOps.Test
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false


namespace P256.Proofs.Verifying.Combination.Loop.Multi.Selection

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Projective P256.Proofs.Program P256.Proofs.Program.ScalarFrame
open P256.Proofs.Common.Instructions (test_r8_r8_effect_step)
open Naf.Iterator.Advance (branch8 branch32)

set_option maxRecDepth 4096 in
theorem select_sign_branch [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {tables digits : BitVec 64} {p q point : Projective} {u v k : Nat} {left : Bool}
    (pre : MultiPre s boundary tables digits)
    (state : DigitState s t tables digits p q u v k point left 0x10f2d9)
    (digit : Int) (hd : Naf.ValidDigit digit) (hne : digit ≠ 0)
    (rdi : t.regValue .rdi = (BitVec.ofInt 8 digit).setWidth 64) :
    ∃ w, Advances boundary 3 t w ∧
      DigitState s w tables digits p q u v k point left
        (if digit < 0 then 0x10f1d0 else 0x10f2e4) ∧
      w.regValue .rdi = (BitVec.ofInt 8 digit).setWidth 64 ∧
      w.regValue .rax = (BitVec.ofInt 8 digit).setWidth 64 := by
  let off : Nat := 0xf2d9
  obtain ⟨a, runA, readyA, effectA⟩ :=
    (mov_r32_r32_effect_step (Extracted.textAddress + BitVec.ofNat 64 off) 0xf8 rfl).advances (boundary := boundary)
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) off [0x89, 0xf8]
        (by decide) (by decide +kernel))
      state.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf2db (by decide)))
  have frameA : AgreesExcept [.reg 0, .rip] t a := effectA.agrees
  have stateA := state_after_registers state readyA frameA (by simp [Component.Covers]) (by simp) effectA.rip
  have rdiA : a.regValue .rdi = (BitVec.ofInt 8 digit).setWidth 64 :=
    (frameA.read (n := 64) (r := 7) (by simp)).trans rdi
  have raxA : a.regValue .rax = (BitVec.ofInt 8 digit).setWidth 64 := by
    have h := effectA.writes
    change a.regValue .rax = ((t.regValue .rdi).setWidth 32).setWidth 64 at h
    rw [rdi, BitVec.setWidth_setWidth_of_le (k := 32) (l := 64) _ (by decide), BitVec.setWidth_setWidth (by decide)] at h
    exact h
  obtain ⟨b, runB, readyB, effectB⟩ :=
    (test_r8_r8_effect_step (Extracted.textAddress + BitVec.ofNat 64 (off+2)) 0x40 0xff
      (by simp [RexPrefix]) rfl).advances (boundary := boundary) readyA
      (programText_slice (programLoaded_codeIn stateA.loaded) (off+2) [0x40, 0x84, 0xff]
        (by decide) (by decide +kernel))
      (by simpa only [movR32R32Effect, BitVec.ofNat_add, BitVec.add_assoc] using effectA.rip)
      (by
        change (Extracted.textAddress + BitVec.ofNat 64 (off+2) + 3) ≠ boundary.rip
        simpa only [off, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
          BitVec.reduceAdd, Extracted.textAddress] using
          boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf2de (by decide)))
  have ripB : b.RIP = 0x10f2de := by
    simpa [P256.Proofs.Common.Instructions.testR8R8Effect, off, Extracted.textAddress] using effectB.rip
  have frameB : AgreesExcept [.flags, .rip] a b := effectB.agrees
  have stateB := state_after_registers stateA readyB frameB (by simp [Component.Covers]) (by simp) effectB.rip
  have rdiB := (frameB.read (n := 64) (r := 7) (by simp)).trans rdiA
  have raxB := (frameB.read (n := 64) (r := 0) (by simp)).trans raxA
  have cond : condHolds 14 (StatusFlags.ofRFLAGS b.RFLAGS) = decide (digit < 0) := by
    have zf := effectB.flags.2.2.2.1
    have sf := effectB.flags.2.2.2.2.1
    have of := effectB.flags.2.2.2.2.2
    change _ = ((a.regValue .rdi).setWidth 8 &&& (a.regValue .rdi).setWidth 8 == 0#8) at zf
    change _ = ((a.regValue .rdi).setWidth 8 &&& (a.regValue .rdi).setWidth 8).msb at sf
    change _ = false at of
    simp only [rdiA, BitVec.setWidth_setWidth_of_le (k := 8) (l := 64) _ (by decide), BitVec.setWidth_eq, BitVec.and_self] at zf sf
    have nz : BitVec.ofInt 8 digit ≠ 0 := fun h => hne ((digit_zero hd).mp h)
    have zf' : (StatusFlags.ofRFLAGS b.RFLAGS).ZF = false := by
      rw [show (BitVec.ofInt 8 digit == 0#8) = false from beq_eq_false_iff_ne.mpr nz] at zf
      exact zf
    change ((StatusFlags.ofRFLAGS b.RFLAGS).ZF || ((StatusFlags.ofRFLAGS b.RFLAGS).SF != (StatusFlags.ofRFLAGS b.RFLAGS).OF)) = _
    rw [zf', sf, of, digit_sign hd]
    cases decide (digit < 0) <;> rfl
  have branch : ∃ w, Advances boundary 1 b w ∧ ReadyToStep w ∧
      w.RIP = (if digit < 0 then 0x10f1d0 else 0x10f2e4) ∧ AgreesExcept [.rip] b w := by
    obtain ⟨w, run, ready, _, rip, agrees⟩ := branch32 (offset := 0xf2de) 14 0xfffffeec
      (decide (digit < 0)) readyB stateB.loaded ripB cond (by decide) (by decide +kernel)
      (by decide +kernel) (by
        by_cases h : digit < 0
        · simp only [h, decide_true, ↓reduceIte]
          exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf1d0 (by decide))
        · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
          exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf2e4 (by decide)))
    refine ⟨w, run, ready, ?_, agrees⟩
    by_cases h : digit < 0 <;> simpa [h, branchTarget, Extracted.textAddress] using rip
  obtain ⟨w, runW, readyW, ripW, frameW⟩ := branch
  refine ⟨w, (runA.trans runB).trans runW,
    state_after_registers stateB readyW frameW (by simp [Component.Covers]) (by simp) ripW,
    (frameW.read (n := 64) (r := 7) (by simp)).trans rdiB,
    (frameW.read (n := 64) (r := 0) (by simp)).trans raxB⟩

end P256.Proofs.Verifying.Combination.Loop.Multi.Selection
