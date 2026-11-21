import P256.Proofs.Verifying.Combination.Loop.MultiSelection.State
import P256.Proofs.Verifying.Combination.Loop.MultiSelection.Arithmetic
import P256.Proofs.Verifying.Combination.Naf.Iterator.Advance.Branch
import X86Proofs.Instructions.Test.Generated.RR.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Loop.Multi.Selection

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Naf.Iterator.Advance (branch8)

theorem digit_branch [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {tables digits : BitVec 64} {p q point : Projective} {u v k : Nat} {left : Bool} {d : Int}
    (pre : MultiPre s boundary tables digits)
    (state : DigitState s t tables digits p q u v k point left 0x10f2d4)
    (hd : Naf.ValidDigit d) (digit : t.regValue .rdi = (BitVec.ofInt 8 d).setWidth 64) :
    ∃ w, Advances boundary 2 t w ∧
      DigitState s w tables digits p q u v k point left (if d = 0 then 0x10f2b8 else 0x10f2d9) ∧
      w.regValue .rdi = t.regValue .rdi := by
  obtain ⟨a, runA, readyA, effectA⟩ :=
    (test_r64_r64_effect_step 0x10f2d4 0x48 0xff (by simp [RexWPrefix]) rfl).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0xf2d4 [0x48,0x85,0xff]
        (by decide) (by decide +kernel)) state.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf2d7 (by decide)))
  have frameA : AgreesExcept [.flags, .rip] t a := effectA.agrees
  have stateA := state_after_registers state readyA frameA (by simp [Component.Covers])
    (by simp) effectA.rip
  have zf : (StatusFlags.ofRFLAGS a.RFLAGS).ZF = decide (d = 0) := by
    have h := effectA.flags.2.2.2.1
    change _ = (t.regValue .rdi &&& t.regValue .rdi == 0#64) at h
    rw [BitVec.and_self, digit] at h
    apply h.trans
    rcases validDigit_cases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  obtain ⟨w, runW, readyW, _, ripW, frameW⟩ := branch8 (offset := 0xf2d7) 4 0xdf
    (decide (d = 0)) readyA stateA.loaded effectA.rip (by exact zf)
    (by decide) (by decide +kernel) (by decide +kernel)
    (by by_cases h : d = 0
        · simp only [h, decide_true, ↓reduceIte]
          exact
            boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf2b8 (by decide))
        · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
          exact
            boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf2d9 (by decide)))
  have frame : AgreesExcept [.flags, .rip] t w := (frameA.trans frameW).mono (by simp)
  refine ⟨w, runA.trans runW, state_after_registers state readyW frame
    (by simp [Component.Covers]) (by simp) ?_, frame.read (n := 64) (r := 7) (by simp)⟩
  by_cases h : d = 0 <;> simpa [h, branchTarget, Extracted.textAddress] using ripW

end P256.Proofs.Verifying.Combination.Loop.Multi.Selection
