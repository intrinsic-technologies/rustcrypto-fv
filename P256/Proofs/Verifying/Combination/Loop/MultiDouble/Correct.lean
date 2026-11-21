import P256.Proofs.Verifying.Combination.Loop.MultiDouble.Branch
import P256.Proofs.Verifying.Combination.Loop.MultiDouble.Setup
import P256.Proofs.Verifying.Combination.Loop.MultiDouble.State
import P256.Proofs.Verifying.Combination.PointDouble
import P256.Proofs.Verifying.Combination.PointCopy
import P256.Proofs.Verifying.Combination.Loop.MultiDigitState
import P256.Proofs.Verifying.Combination.Algebra.Interface

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Loop.Multi

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

theorem double_path [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {tables digits : BitVec 64} {p q point : Projective} {u v k : Nat}
    (pre : MultiPre s boundary tables digits)
    (state : RoundState s t tables digits p q u v k point 0x10f17a) :
    ∃ fuel w, Advances boundary fuel t w ∧
      RoundState s w tables digits p q u v k point.double 0x10f1a3 := by
  obtain ⟨n, a, runA, readyA, _, effectA⟩ := doubleInputSetup_correct boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xf17a doubleInputSetupBytes
      (by decide) (by decide +kernel)) state.rip
  have agreesA : AgreesExcept [.reg 1, .reg 7, .reg 12, .reg 6, .rip] t a := effectA.agrees
  have stateA := state.after_registers readyA agreesA (by simp [Component.Covers])
    (by simp) effectA.rip
  have argsA : a.regValue .rcx = 12 ∧ a.regValue .rdi = t.regValue .r15 ∧
      a.regValue .r12 = stackPtr t + 72 ∧ a.regValue .rsi = stackPtr t + 72 := effectA.writes
  have accumulator : stackPtr t + 72 = stackPtr s - 336 := by
    rw [state.rsp]
    change stackPtr s - 408 + 72 = _
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  obtain ⟨b, resultB⟩ := point_copy pre.toCalleePre stateA.toFrameState 0xf18a 336 144
    (by decide) (by decide +kernel) stateA.rip (by decide) (by decide)
    (argsA.2.1.trans state.scratch) argsA.1 (by decide) (by decide) (Or.inl (by decide))
    (argsA.2.2.2.trans accumulator) stateA.value
  have stateB := scratch_result pre stateA resultB
  have accumulatorB : b.regValue .r12 = stackPtr s - 336 :=
    (resultB.registers .r12 (by simp)).trans (argsA.2.2.1.trans accumulator)
  obtain ⟨c, runC, readyC, effectC⟩ :=
    (mov_r64_r64_effect_step 0x10f18d 0x4c 0xff (by simp [RexWPrefix]) rfl).advances
      (readyToStep stateB.machine stateB.bindingsSupported)
      (programText_slice (programLoaded_codeIn stateB.loaded) 0xf18d [0x4c,0x89,0xff]
        (by decide) (by decide +kernel)) stateB.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf190 (by decide)))
  have agreesC : AgreesExcept [.reg 7, .rip] b c := effectC.agrees
  have stateC := stateB.after_registers readyC agreesC (by simp [Component.Covers])
    (by simp) effectC.rip
  have inputC := resultB.value.of_bytes_eq (fun _ _ => congrArg (fun ram : Ram => ram[_]?)
    (agreesC.external (by simp [Component.Covers])))
  obtain ⟨d, resultD⟩ := point_double pre.toCalleePre stateC.toFrameState stateC.rip
    ((show c.regValue .rdi = b.regValue .r15 from effectC.writes).trans stateB.scratch) inputC
  have stateD := scratch_result pre stateC resultD
  have accumulatorD : d.regValue .r12 = stackPtr s - 336 :=
    (resultD.registers .r12 (by simp)).trans
      ((agreesC.read (n := 64) (r := 12) (by simp)).trans accumulatorB)
  obtain ⟨m, e, runE, readyE, _, effectE⟩ := doubleOutputSetup_correct boundary pre.outerBoundary d
    (readyToStep stateD.machine stateD.bindingsSupported)
    (programText_slice (programLoaded_codeIn stateD.loaded) 0xf195 doubleOutputSetupBytes
      (by decide) (by decide +kernel)) stateD.rip
  have agreesE : AgreesExcept [.reg 1, .reg 7, .reg 6, .rip] d e := effectE.agrees
  have stateE := stateD.after_registers readyE agreesE (by simp [Component.Covers])
    (by simp) effectE.rip
  have argsE : e.regValue .rcx = 12 ∧ e.regValue .rdi = d.regValue .r12 ∧
      e.regValue .rsi = d.regValue .r15 := effectE.writes
  have valueE := resultD.value.of_bytes_eq (fun _ _ => congrArg (fun ram : Ram => ram[_]?)
    (agreesE.external (by simp [Component.Covers])))
  obtain ⟨w, resultW⟩ := point_copy pre.toCalleePre stateE.toFrameState 0xf1a0 144 336
    (by decide) (by decide +kernel) stateE.rip (by decide) (by decide)
    (argsE.2.1.trans accumulatorD) argsE.1 (by decide) (by decide) (Or.inr (by decide))
    (argsE.2.2.trans stateD.scratch) valueE
  obtain ⟨j, runB⟩ := resultB.execution
  obtain ⟨k', runD⟩ := resultD.execution
  obtain ⟨l, runW⟩ := resultW.execution
  refine ⟨n+j+1+k'+m+l, w, ((((runA.trans runB).trans runC).trans runD).trans runE).trans runW,
    ⟨⟨stateE.toMemory.of_frame pre resultW.toFrameState,
      (resultW.registers .rbx (by simp)).trans stateE.count, stateE.positive, stateE.bounded,
      (resultW.registers .r15 (by simp)).trans stateE.scratch, resultW.value, ?_, ?_, ?_⟩,
      resultW.rip, (resultW.registers .r13 (by simp)).trans stateE.cursor, ?_⟩⟩
  · exact (resultW.read (offset := 400) (n := 64) (by decide) (by decide)
      (Or.inr (by decide))).trans stateE.total
  · exact (resultW.read (offset := 384) (n := 64) (by decide) (by decide)
      (Or.inr (by decide))).trans stateE.tableBase
  · exact (resultW.read (offset := 392) (n := 64) (by decide) (by decide)
      (Or.inr (by decide))).trans stateE.output
  · intro h
    rw [resultW.registers .r14 (by simp)] at h
    rw [stateE.identity h]
    exact Algebra.identity_double

end P256.Proofs.Verifying.Combination.Loop.Multi
