import P256.Proofs.Sec1.Affine.Uncompressed.Output.State
import P256.Proofs.Common.Instructions.ByteLogic.And
import P256.Proofs.Field.Preserve

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Output

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Masked [Bindings] (s t : RamState) (bytes : ByteArray) : Prop extends Frame s t where
  rip : t.RIP = 0x110cc7
  output : t.regValue .rbx = s.regValue .rdi
  x : Field.MontgomeryAt t (stackPtr s - 664)
    (if valid bytes then canonical (xCoordinate bytes) else 0)
  y : Field.MontgomeryAt t (stackPtr s - 632)
    (if valid bytes then canonical (yCoordinate bytes) else 0)
  choice : (t.regValue .rbp).setWidth 8 = if valid bytes then 1 else 0
  infinity : (t.regValue .r15).setWidth 8 = if valid bytes then 0 else 1

theorem mask [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    (pre : AffineDecodePre s boundary bytes) (state : Selected s t bytes) :
    ∃ u, Advances boundary 1 t u ∧ Masked s u bytes := by
  obtain ⟨u,run,ready,effect⟩ :=
    (P256.Proofs.Common.Instructions.ByteLogic.and_r8_imm8_effect_step
      0x110cc3 0x41 0xe7 1 (by simp [RexPrefix]) rfl rfl).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0x10cc3 _
        (by decide) (by decide +kernel)) state.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x10cc7 (by decide)))
  have agrees : AgreesExcept [.reg 15,.flags,.rip] t u := effect.agrees
  have memory := agrees.external (by simp [Component.Covers])
  refine ⟨u,run,state.toFrameState.after_registers ready agrees
    (by simp [Component.Covers]) (by simp),effect.rip,?_,?_,?_,?_,?_⟩
  · exact (agrees.read (n := 64) (r := 3) (by simp)).trans state.output
  · exact state.x.of_bytes_eq (by intro i hi; rw [memory])
  · exact state.y.of_bytes_eq (by intro i hi; rw [memory])
  · exact (congrArg (BitVec.setWidth 8)
      (agrees.read (n := 64) (r := 5) (by simp))).trans state.choice
  · have h := congrArg (BitVec.setWidth 8) effect.writes
    change (u.regValue .r15).setWidth 8 =
      (mergeGPR 8 ((t.regValue .r15).setWidth 8 &&& 1) (t.regValue .r15)).setWidth 8 at h
    rw [P256.Proofs.Common.Instructions.ByteOps.ByteOps.mergeGPR_low8] at h
    rw [h,state.infinity]
    cases valid bytes <;> decide +kernel

end P256.Proofs.Sec1.Affine.Uncompressed.Output
