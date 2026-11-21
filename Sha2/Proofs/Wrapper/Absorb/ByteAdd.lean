import Sha2.Proofs.Wrapper.Variant
import Sha2.Proofs.Wrapper.Buffered
import Sha2.Proofs.Common.Instructions.AddByte.Effect

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper.Absorb

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.Instructions.AddByte

theorem mergeGPR8_low (value : BitVec 8) (old : BitVec 64) :
    (mergeGPR 8 value old).setWidth 8 = value := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and, mergeGPR,
    show ¬ (8 : Nat) = 32 by decide, ite_false]
  rw [getLsbD_setSlice old 0 8 value i (by omega)]
  simp [hi]

theorem add_short_length [Bindings] {v : Variant} {initial s : RamState} {inputs : Array Input}
    (ctx : Context initial inputs v) (input : Preserved initial s v) (rip : s.RIP = (v.pc 0xb7)) :
    ∃ t, Preserved initial t v ∧ t.RIP=(v.pc 0xba) ∧
      (Operand.reg 3 : Operand 8).read t =
        (Operand.reg 3 : Operand 8).read s + (Operand.reg 12 : Operand 8).read s ∧
      AgreesExcept [.reg 3,.flags,.rip] s t := by
  obtain ⟨t,run,ready,effect⟩ := (add_bl_r12b_effect_step (v.pc 0xb7)).advances
    (supportedMachine_readyToStep input.machine)
    (programText_slice (programLoaded_codeIn input.loaded) (v.textOffset + 0xb7) [0x44,0x00,0xe3]
      (by cases v <;> decide) (by cases v <;> decide +kernel)) rip
    (boundary_ne_program (validCall_returnBoundary ctx.machine ctx.call).2.2
      (by
        change InProgram (v.pc 0xb7 + BitVec.ofNat 64 3)
        rw [Variant.pc_add]
        exact Variant.pc_inProgram v (by decide)))
  have frame : AgreesExcept [.reg 3,.flags,.rip] s t := effect.agrees
  refine ⟨t, preserved_of_agrees ctx input run ready frame
    (by simp [LocalWrites,Component.Covers]) (by simp), (by
      have h : t.RIP = v.pc 0xb7 + BitVec.ofNat 64 3 := effect.rip
      rw [Variant.pc_add] at h
      exact h), ?_, frame⟩
  have write : (Operand.reg 3 : Operand 64).read t = mergeGPR 8
      ((Operand.reg 3 : Operand 8).read s + (Operand.reg 12 : Operand 8).read s)
      ((Operand.reg 3 : Operand 64).read s) := effect.writes
  have low : (Operand.reg 3 : Operand 8).read t =
      ((Operand.reg 3 : Operand 64).read t).setWidth 8 := rfl
  rw [low,write,mergeGPR8_low]

end Sha2.Proofs.Wrapper.Absorb
