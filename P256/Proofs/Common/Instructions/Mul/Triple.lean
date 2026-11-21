import P256.Proofs.Common.Instructions.Mul.Step
import X86Proofs.Step.Prefix
import X86Proofs.Step.Decode
import X86Proofs.Core.Gpr

set_option autoImplicit false

open X86Proofs

namespace P256.Proofs.Common.Instructions

open X86 X86.Machine X86.UserProcess

theorem mul_r64_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 4) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0xF7, modrm])
      (mulR64Effect p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, mul_r64_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), mul_r64_ready h _, ⟨?_, ?_, ?_, ?_⟩⟩
  · simp [mulR64Effect, afterStep, finishStep, mulResult64, setFlags,
      afterFetches, beforeFetch, resetStepFields, h.ready.repeatClear, h.ready.msr]
  · simp [mulR64Effect, Write.AllHold, afterStep, finishStep, afterFetches, beforeFetch,
      resetStepFields, mulResult64,
      setFlags, Operand.read_reg64, gprIndex]
  · change (mulFlags64 _ _).Allows (StatusFlags.ofRFLAGS ((mulStatus64 _ _ _).store _))
    rw [StatusFlags.ofRFLAGS_store]
    exact mulFlags64_allows _ _ _
  · change AgreesExcept [.reg 0, .reg 2, .flags, .rip] s _
    refine ⟨fun c hc _ => ?_, fun _ _ => rfl, ?_, fun _ h => h⟩
    · cases c with
      | reg r =>
        have h0 : r ≠ 0 := by intro hr; subst r; simp at hc
        have h2 : r ≠ 2 := by intro hr; subst r; simp at hc
        have hn0 : r.toNat ≠ 0 := fun he => h0 (BitVec.eq_of_toNat_eq he)
        have hn2 : r.toNat ≠ 2 := fun he => h2 (BitVec.eq_of_toNat_eq he)
        simp [Component.Agrees, afterStep, finishStep, mulResult64, setFlags,
          afterFetches, beforeFetch, resetStepFields, gprIndex,
          Ne.symm hn0, Ne.symm hn2]
      | flags => exact absurd (by simp) hc
      | rip => exact absurd (by simp) hc
      | mem addr len => exact fun _ _ => rfl
      | xmm x => exact Component.agrees_xmm_of_zmm rfl x
      | mxcsr => rfl
      | fpr x => exact Component.agrees_fpr_of_fp87 rfl x
      | fsw => rfl
      | fcc => rfl
      | ftw => rfl
      | fcw => rfl
      | fpuPtr => rfl
      | df => exact dfBit_store _ _
    · simp only [fixedPart, afterStep, finishStep, mulResult64, setFlags,
        afterFetches, beforeFetch, resetStepFields, clearStatusFlags_store]

end P256.Proofs.Common.Instructions
