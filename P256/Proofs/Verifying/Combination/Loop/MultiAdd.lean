import P256.Proofs.Verifying.Combination.Loop.MultiAddSetup
import P256.Proofs.Verifying.Combination.Loop.MultiNegative.State
import P256.Proofs.Verifying.Combination.PointAdd
import P256.Proofs.Verifying.Combination.PointMemory
import X86Proofs.Instructions.Mov.Generated.R8Imm8.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Loop.Multi

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem add_selected [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {tables digits : BitVec 64} {p q point selected : Projective} {u v k : Nat} {left : Bool}
    (pre : MultiPre s boundary tables digits)
    (state : SelectedState s t tables digits p q u v k point selected left) :
    ∃ fuel w, Advances boundary fuel t w ∧
      DigitState s w tables digits p q u v k (point.add selected) left 0x10f2b8 := by
  obtain ⟨fa, a, runA, readyA, _, effectA⟩ := addSetup_correct boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xf2a8 addSetupBytes
      (by decide) (by decide +kernel)) state.rip
  have frameA : AgreesExcept [.reg 7, .reg 6, .rip] t a := effectA.agrees
  have stateA := state.toDigitData.after_registers readyA frameA (by simp [Component.Covers]) (by simp)
  have dstA : a.regValue .rdi = stackPtr s - 336 :=
    effectA.writes.1.trans (scalar_stack_address state.rsp (offset := 72) (by decide) (by decide))
  have srcA : a.regValue .rsi = stackPtr s - 144 := effectA.writes.2.trans state.scratch
  have selectedA : ProjectiveAt a (stackPtr s - 144) selected :=
    state.selectedValue.of_bytes_eq (fun _ _ => congrArg (fun m : Ram => m[_]?)
      (frameA.external (by simp [Component.Covers])))
  obtain ⟨b, resultB⟩ := point_add pre.toCalleePre stateA.toFrameState effectA.rip dstA srcA stateA.value selectedA
  have stateB : DigitData s b tables digits p q u v k (point.add selected) left := by
    refine ⟨⟨stateA.toMemory.of_frame pre resultB.toFrameState,
      (resultB.registers .rbx (by simp)).trans stateA.count, stateA.positive, stateA.bounded,
      (resultB.registers .r15 (by simp)).trans stateA.scratch,
      resultB.value, ?_, ?_, ?_⟩,
      (resultB.registers .r13 (by simp)).trans stateA.cursor,
      (resultB.registers .rbp (by simp)).trans stateA.tableCursor,
      (resultB.registers .r12 (by simp)).trans stateA.remaining, ?_⟩
    · exact (resultB.read (offset := 400) (by decide) (by decide) (.inr (by decide))).trans stateA.total
    · exact (resultB.read (offset := 384) (by decide) (by decide) (.inr (by decide))).trans stateA.tableBase
    · exact (resultB.read (offset := 392) (by decide) (by decide) (.inr (by decide))).trans stateA.output
    · exact (resultB.read (offset := 376) (by decide) (by decide) (.inr (by decide))).trans stateA.savedCursor
  obtain ⟨w, runW, readyW, effectW⟩ :=
    (mov_r8_imm8_rex_effect_step 0x10f2b5 0x41 (by simp [RexPrefix]) 0xb6 (by decide) 1).advances
      (readyToStep stateB.machine stateB.bindingsSupported)
      (programText_slice (programLoaded_codeIn stateB.loaded) 0xf2b5 _
        (by decide) (by decide +kernel)) resultB.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf2b8 (by decide)))
  have frameW : AgreesExcept [.reg 14, .rip] b w := effectW.agrees
  have flagW : (w.regValue .r14).getLsbD 0 = true := by
    have h : w.regValue .r14 = mergeGPR 8 (1#8) (b.regValue .r14) := effectW.writes
    rw [h]
    simp [mergeGPR, X86.Runtime.setSlice]
  obtain ⟨fb, runB⟩ := resultB.execution
  refine ⟨fa+fb+1, w, (runA.trans runB).trans runW,
    ⟨stateB.after_registers readyW frameW (by simp [Component.Covers]) (by simp), effectW.rip, ?_⟩⟩
  intro h
  rw [flagW] at h
  contradiction

end P256.Proofs.Verifying.Combination.Loop.Multi
