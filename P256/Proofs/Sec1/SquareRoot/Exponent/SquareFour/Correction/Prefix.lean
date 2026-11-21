import P256.Proofs.Sec1.SquareRoot.Exponent.SquareFour.Correction.Support
import P256.Proofs.Common.Instructions.ByteLogic.AndReg
import P256.Proofs.Common.Instructions.Setb.Triple
import P256.Proofs.Common.Instructions.ByteOps.Effects
import X86Proofs.Instructions.Test.Generated.RR.Triple

set_option autoImplicit false
namespace P256.Proofs.Sec1.SquareRoot.SquareFour.Correction
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Common.Instructions.ByteLogic P256.Proofs.Common.Instructions.Setb

theorem prefix_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (ctx : ExponentPre s boundary x) (hf : ExponentFrame s t) (hip : t.RIP = 0x115770) :
    ∃ u, Advances boundary 3 t u ∧ ExponentFrame s u ∧ u.RIP = 0x11577a ∧
      (Operand.reg 8 : Operand 8).read u =
        (if (Operand.reg 15 : Operand 64).read t = 0 then 1 else 0) &&&
          (Operand.reg 9 : Operand 8).read t ∧
      AgreesExcept [.reg 8, .flags, .rip] t u := by
  obtain ⟨t1,r1,ready1,e1⟩ := (test_r64_r64_effect_step 0x115770 0x4d 0xff
    (by simp [RexWPrefix]) rfl).advances (readyToStep hf.machine hf.bindingsSupported)
      (programText_slice (programLoaded_codeIn hf.loaded) 0x15770 _ (by decide) (by decide +kernel)) hip
      (boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x15773 (by decide)))
  change (testR64R64Effect 0x115770 15 15 t).Holds t t1 at e1
  have a1 : AgreesExcept [.flags,.rip] t t1 := e1.agrees
  have f1 := frame_of_agrees ctx hf ready1 (a1.mono (by simp [SquareFour.components]))
  have hz : (StatusFlags.ofRFLAGS t1.RFLAGS).ZF = ((Operand.reg 15 : Operand 64).read t == 0) := by
    simpa only [testR64R64Effect,testFlags,BitVec.and_self,FlagAllows] using e1.flags.2.2.2.1
  obtain ⟨t2,r2,ready2,e2⟩ := (setcc_r8_rex_effect_step 0x115773 0x41 0x94 0xc0
    (by simp [RexPrefix]) (by simp [SupportedOpcode]) rfl).advances ready1
      (programText_slice (programLoaded_codeIn f1.loaded) 0x15773 _ (by decide) (by decide +kernel)) e1.rip
      (boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x15777 (by decide)))
  have a2 : AgreesExcept [.reg 8,.rip] t1 t2 := e2.agrees
  have f2 := frame_of_agrees ctx f1 ready2 (a2.mono (by simp [SquareFour.components]))
  have byte2 : (Operand.reg 8 : Operand 8).read t2 =
      if (Operand.reg 15 : Operand 64).read t = 0 then 1 else 0 := by
    have hw := congrArg (BitVec.setWidth 8) e2.writes
    rw [P256.Proofs.Common.Instructions.ByteOps.ByteOps.mergeGPR_low8] at hw
    change (Operand.reg 8 : Operand 8).read t2 = (if (StatusFlags.ofRFLAGS t1.RFLAGS).ZF then 1 else 0) at hw
    simpa only [hz,beq_iff_eq] using hw
  have borrow2 : (Operand.reg 9 : Operand 8).read t2 = (Operand.reg 9 : Operand 8).read t :=
    (a1.trans a2).read (by simp)
  obtain ⟨t3,r3,ready3,e3⟩ := (and_r8_r8_rex_effect_step 0x115777 0x45 0xc8
    (by simp [RexPrefix]) rfl).advances ready2
      (programText_slice (programLoaded_codeIn f2.loaded) 0x15777 _ (by decide) (by decide +kernel)) e2.rip
      (boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x1577a (by decide)))
  change (andR8R8Effect 0x115777 8 9 t2).Holds t2 t3 at e3
  have a3 : AgreesExcept [.reg 8,.flags,.rip] t2 t3 := e3.agrees
  have f3 := frame_of_agrees ctx f2 ready3 (a3.mono (by simp [SquareFour.components]))
  refine ⟨t3,(r1.trans r2).trans r3,f3,e3.rip,?_,((a1.trans a2).trans a3).mono (by simp)⟩
  have hw := congrArg (BitVec.setWidth 8) e3.writes
  rw [P256.Proofs.Common.Instructions.ByteOps.ByteOps.mergeGPR_low8] at hw
  exact hw.trans (by rw [byte2,borrow2])
end P256.Proofs.Sec1.SquareRoot.SquareFour.Correction
