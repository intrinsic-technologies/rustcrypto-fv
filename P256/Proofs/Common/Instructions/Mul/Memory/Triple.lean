import P256.Proofs.Common.Instructions.Mul.Memory.Step
import X86Proofs.Instructions.Xor.Generated.RM.Triple
import X86Proofs.Program.ReadWrite.LoadFlags

set_option autoImplicit false

open X86Proofs

namespace P256.Proofs.Common.Instructions

open X86 X86.Machine X86.UserProcess

def mulM64Effect (p : BitVec 64) (am : AddrMode) (s : RamState) : Effect :=
  let a := (Operand.reg 0 : Operand 64).read s
  let b := (Operand.mem (am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) : Operand 64).read s
  { rip := p + BitVec.ofNat 64 (3 + am.tail.length)
    writes := [⟨(Operand.reg 0 : Operand 64), a * b⟩,
      ⟨(Operand.reg 2 : Operand 64), mulHigh64 a b⟩]
    flags := some (mulFlags64 a b) }

theorem mul_m64_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 8) (codeRange p (rex :: 0xF7 :: am.modrm 4 :: am.tail))
      (mulM64Effect p am) := by
  rintro s h hcode ⟨hp, hread⟩
  have hlow := movLoadLen_low hp am hcode
  subst hp
  refine ⟨_, mul_m64_step s h rex hrex am hv hx hb hcode.bytesAt hlow hread,
    ReadyToStep.afterStep_mulLoad h _ _ _, ⟨?_, ?_, ?_, ?_⟩⟩
  · simp [mulM64Effect, afterStep, finishStep, mulResult64, setFlags, dataAccess,
      afterFetches, beforeFetch, resetStepFields, h.ready.repeatClear, h.ready.msr]
  · simp [mulM64Effect, Write.AllHold, afterStep, finishStep, afterFetches, beforeFetch,
      resetStepFields, mulResult64, dataAccess,
      setFlags, Operand.read, AddrMode.addrAt, gprIndex]
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
        simp [Component.Agrees, afterStep, finishStep, mulResult64, setFlags, dataAccess,
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
    · simp only [fixedPart, afterStep, finishStep, mulResult64, setFlags, dataAccess,
        afterFetches, beforeFetch, resetStepFields, clearStatusFlags_store]

end P256.Proofs.Common.Instructions
