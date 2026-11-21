import P256.Proofs.Verifying.Combination.Loop.MultiSelection.PositiveSetup
import P256.Proofs.Verifying.Combination.Loop.MultiSelection.TableCopy
import P256.Proofs.Verifying.Combination.Naf.Iterator.Advance.Branch

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Loop.Multi.Selection

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open P256.Proofs.Projective.Multiply.Machine.Basepoint.TableSteps
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem select_positive [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {tables digits : BitVec 64} {p q point : Projective} {u v k : Nat} {left : Bool}
    (pre : MultiPre s boundary tables digits)
    (state : DigitState s t tables digits p q u v k point left 0x10f2ea)
    (i : Fin 8) (index : t.regValue .rdi = BitVec.ofNat 64 i.val) :
    ∃ fuel w, Advances boundary fuel t w ∧
      SelectedState s w tables digits p q u v k point (Table.oddTable (if left then p else q) i) left := by
  have stride : positiveStride t = BitVec.ofNat 64 (96*i.val) := by
    unfold positiveStride
    rw [index]
    exact (show ∀ j : Fin 8,
      (((BitVec.ofNat 64 j.val + (BitVec.ofNat 64 j.val <<< 1)).setWidth 32) <<< 5).setWidth 64 =
        BitVec.ofNat 64 (96*j.val) from by decide +kernel) i
  obtain ⟨fuel, a, run, ready, _, effect⟩ := positiveSetup_correct boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xf2ea positiveSetupBytes
      (by decide) (by decide +kernel)) state.rip
  have frameA : AgreesExcept [.reg 6, .reg 1, .reg 7, .flags, .rip] t a := effect.agrees
  have stateA := state.toDigitData.after_registers ready frameA (by simp [Component.Covers]) (by simp)
  have writes : a.regValue .rsi = positiveStride t + t.regValue .rbp ∧
      a.regValue .rcx = 12 ∧ a.regValue .rdi = t.regValue .r15 := effect.writes
  have src : a.regValue .rsi = tables + (if left then 0 else 768) + BitVec.ofNat 64 (96*i.val) := by
    rw [writes.1, stride, state.tableCursor, BitVec.add_comm]
  obtain ⟨b, runB, stateB, ripB, selectedB, frameB⟩ := table_copy pre stateA i 0xf2fc 144
    (by decide) (by decide) (by decide) (by decide +kernel) effect.rip src
    (writes.2.2.trans state.scratch) writes.2.1
  obtain ⟨w, runW, readyW, effectW⟩ :=
    (jmp_rel8_effect_step 0x10f2ff 0xa7 (by decide +kernel)).advances
      (readyToStep stateB.machine stateB.bindingsSupported)
      (programText_slice (programLoaded_codeIn stateB.loaded) 0xf2ff [0xeb,0xa7]
        (by decide) (by decide +kernel)) ripB
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf2a8 (by decide)))
  have frameW : AgreesExcept [.rip] b w := effectW.agrees
  exact ⟨fuel+12+1, w, (run.trans runB).trans runW,
    stateB.after_registers readyW frameW (by simp [Component.Covers]) (by simp), effectW.rip,
    selectedB.of_bytes_eq (fun _ _ => congrArg (fun m : Ram => m[_]?)
      (frameW.external (by simp [Component.Covers])))⟩

end P256.Proofs.Verifying.Combination.Loop.Multi.Selection
