import P256.Proofs.Verifying.Core.Reduce.Choice
import P256.Proofs.Common.Instructions.ByteLogic.Unary
import P256.Proofs.Common.Instructions.ByteOps.Effects
import P256.Proofs.Common.Instructions.MovzxByte

set_option autoImplicit false

open P256.Proofs.Program (CalleePre boundary_ne_program inProgram_of_textOffset
  programLoaded_codeIn programText_slice readyToStep)

namespace P256.Proofs.Verifying.Core.Reduce

open P256.Proofs.Program
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem invert_choice [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x113120 32 32 104) (state : FrameState s t)
    (rip : t.RIP = 0x1131f8) :
    ∃ u, Advances boundary 3 t u ∧ FrameState s u ∧ u.RIP = 0x1131ff ∧
      u.regValue .rdi = ((~~~((t.regValue .rax).setWidth 8)) &&& 1).setWidth 64 ∧
      AgreesExcept [.reg 0,.reg 7,.flags,.rip] t u := by
  obtain ⟨a,ha,ra,ea⟩ := (P256.Proofs.Common.Instructions.ByteLogic.not_al_effect_step 0x1131f8).advances
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x131f8 _ (by decide) (by decide +kernel))
    rip (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x131fa (by decide)))
  have fa : AgreesExcept [.reg 0,.rip] t a := ea.agrees
  have sta := state.after_registers ra fa (by simp [Component.Covers]) (by simp)
  obtain ⟨b,hb,rb,eb⟩ := (P256.Proofs.Common.Instructions.ByteOps.ByteOps.and_al_imm8_effect_step 0x1131fa 1).advances ra
    (programText_slice (programLoaded_codeIn sta.loaded) 0x131fa _ (by decide) (by decide +kernel))
    ea.rip (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x131fc (by decide)))
  have fb : AgreesExcept [.reg 0,.flags,.rip] a b := eb.agrees
  have stb := sta.after_registers rb fb (by simp [Component.Covers]) (by simp)
  obtain ⟨u,hu,ru,eu⟩ :=
    (P256.Proofs.Common.Instructions.MovzxByte.movzx_r32_r8_effect_step 0x1131fc 0xf8 (by decide) (by decide)).advances rb
      (programText_slice (programLoaded_codeIn stb.loaded) 0x131fc _ (by decide) (by decide +kernel))
      eb.rip (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x131ff (by decide)))
  have fu : AgreesExcept [.reg 7,.rip] b u := eu.agrees
  have f : AgreesExcept [.reg 0,.reg 7,.flags,.rip] t u := (fa.trans (fb.trans fu)).mono (by simp)
  refine ⟨u,ha.trans (hb.trans hu),state.after_registers ru f (by simp [Component.Covers])
    (by simp),eu.rip,?_,f⟩
  have va : a.regValue .rax = mergeGPR 8 (~~~((t.regValue .rax).setWidth 8)) (t.regValue .rax) := ea.writes
  have vb : b.regValue .rax = mergeGPR 8 ((a.regValue .rax).setWidth 8 &&& 1) (a.regValue .rax) := eb.writes
  have vu : u.regValue .rdi = ((b.regValue .rax).setWidth 8).setWidth 64 := eu.writes
  rw [vu,vb,P256.Proofs.Common.Instructions.ByteOps.ByteOps.mergeGPR_low8,va,P256.Proofs.Common.Instructions.ByteOps.ByteOps.mergeGPR_low8]

theorem choices [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {a : SecretKeyFromBytes.Scalar.Limbs}
    (pre : CalleePre s boundary 0x113120 32 32 104) (state : Subtracted s t a) :
    ∃ u, Advances boundary 15 t u ∧ FrameState s u ∧ u.RIP = 0x113204 ∧
      u.regValue .rax = (if SecretKeyFromBytes.Scalar.orderBorrow a = 0 then 1 else 0) ∧
      AgreesExcept (choiceFrame t ++ [.reg 7]) t u := by
  obtain ⟨v,hv,sv,pv,av,fv⟩ := choice_call pre state.toFrameState 0x131f3 0x5e78
    (by decide) (by decide +kernel) (by decide +kernel) state.rip
  obtain ⟨w,hw,sw,pw,dw,fw⟩ := invert_choice pre sv pv
  obtain ⟨u,hu,su,pu,au,fu⟩ := choice_call pre sw 0x131ff 0x5e6c
    (by decide) (by decide +kernel) (by decide +kernel) pw
  have spw : stackPtr w = stackPtr t := sw.rsp.trans state.rsp.symm
  have f : AgreesExcept (choiceFrame t ++ [.reg 7]) t u := by
    apply (fv.trans (fw.trans fu)).mono
    simp [choiceFrame,spw]
  refine ⟨u,hv.trans (hw.trans hu),su,pu,?_,f⟩
  change u.regValue .rax = _ at au
  rw [au]
  change ((w.regValue .rdi).setWidth 8).setWidth 64 = _
  rw [dw,av]
  change (((~~~((((t.regValue .rdi).setWidth 8).setWidth 64).setWidth 8) &&& 1).setWidth 64).setWidth 8).setWidth 64 = _
  rw [state.borrow, SecretKeyFromBytes.Scalar.orderBorrow_eq]
  split <;> decide +kernel

end P256.Proofs.Verifying.Core.Reduce
