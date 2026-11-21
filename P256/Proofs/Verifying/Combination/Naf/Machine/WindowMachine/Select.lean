import P256.Proofs.Verifying.Combination.Naf.Interface
import P256.Proofs.Verifying.Combination.Naf.Machine.WindowMachine.Interface
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Machine.WindowMachine

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open Iterator.Advance

theorem select [Bindings] {s : RamState} {boundary : ReturnBoundary} {j : Nat}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (rip : s.RIP=0x10f3fe)
    (index : s.regValue .rbx=BitVec.ofNat 64 j) (width : s.regValue .r12=5)
    (bound : j<64) (outer : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 3 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP=(if j+5<64 then 0x10f408 else 0x10f420) ∧
      AgreesExcept [.reg 1,.flags,.rip] s t := by
  obtain ⟨a,runA,readyA,loadedA,effectA⟩ := step_nomem (offset:=0xf3fe)
    (show StepEffect _ _ (leaR64Effect 0x10f3fe 1 (.sib 3 (some 12) 0 .none)) from
      lea_r64_effect_step 0x10f3fe 0x4a (by simp [RexWPrefix]) 1
      (.sib 3 (some 12) 0 .none) (by decide) rfl rfl)
    ready loaded rip (by decide) (by decide +kernel)
    (boundary_ne_program outer (inProgram_of_textOffset 0xf402 (by decide)))
    (by simp [Component.Covers])
  have valueA : a.regValue .rcx=BitVec.ofNat 64 (j+5) := by
    have h := effectA.writes
    x86_norm at h
    have sum : a.regValue .rcx=s.regValue .rbx+s.regValue .r12 := by
      simp only [Write.AllHold,Operand.read_reg64,BitVec.shiftLeft_zero] at h
      change a.regValue .rcx=s.regValue .rbx+(s.regValue .r12+(0 : BitVec 64)) at h
      have zero : s.regValue .r12+(0 : BitVec 64)=s.regValue .r12 := BitVec.add_zero _
      rw [zero] at h
      exact h
    rw [sum,index,width,BitVec.ofNat_add]
    rfl
  obtain ⟨b,runB,readyB,loadedB,effectB⟩ := step_nomem (offset:=0xf402)
    (show StepEffect _ _ (cmpR64Imm8Effect 0x10f402 1 64) from
      cmp_r64_imm8_effect_step 0x10f402 0x48 0xf9 64 (by simp [RexWPrefix]) rfl rfl)
    readyA loadedA effectA.rip (by decide) (by decide +kernel)
    (boundary_ne_program outer (inProgram_of_textOffset 0xf406 (by decide)))
    (by simp [Component.Covers])
  have carry : (StatusFlags.ofRFLAGS b.RFLAGS).CF=decide (j+5<64) := by
    have h := effectB.flags.1
    change (StatusFlags.ofRFLAGS b.RFLAGS).CF=decide (a.regValue .rcx < (64 : BitVec 64)) at h
    rw [h,valueA]
    change decide ((j+5)%2^64<64)=decide (j+5<64)
    rw [Nat.mod_eq_of_lt (show j+5<2^64 by omega)]
  have condition : condHolds 3 (StatusFlags.ofRFLAGS b.RFLAGS)=decide (¬j+5<64) := by
    change (!(StatusFlags.ofRFLAGS b.RFLAGS).CF)=_
    rw [carry]
    by_cases h : j+5<64 <;> simp [h]
  obtain ⟨t,runT,readyT,loadedT,ripT,agreesT⟩ := branch8 (offset:=0xf406) 3 0x18
    (decide (¬j+5<64)) readyB loadedB effectB.rip condition
    (by decide) (by decide +kernel) (by decide +kernel) (by
      by_cases h : j+5<64
      · simpa [h,branchTarget,Extracted.textAddress] using
          boundary_ne_program outer (inProgram_of_textOffset 0xf408 (by decide))
      · simpa [h,branchTarget,Extracted.textAddress] using
          boundary_ne_program outer (inProgram_of_textOffset 0xf420 (by decide)))
  refine ⟨t,(runA.trans runB).trans runT,readyT,loadedT,?_,?_⟩
  · by_cases h : j+5<64 <;> simpa [h,branchTarget,Extracted.textAddress] using ripT
  · exact ((effectA.agrees.trans effectB.agrees).trans agreesT).mono (by simp)

end P256.Proofs.Verifying.Combination.Naf.Machine.WindowMachine
