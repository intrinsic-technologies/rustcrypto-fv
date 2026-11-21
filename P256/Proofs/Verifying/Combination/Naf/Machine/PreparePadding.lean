import P256.Proofs.Verifying.Combination.Naf.Interface
import P256.Proofs.Verifying.Combination.Naf.Machine.Frame
import P256.Proofs.Verifying.Combination.Naf.Iterator.Advance.Steps
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Nop.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Machine

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar

theorem prepare_padding [Bindings] {s t : RamState} {boundary : ReturnBoundary} {i count : Nat}
    (state : FrameState s t) (rip : t.RIP=0x10f4b2)
    (r14 : t.regValue .r14=BitVec.ofNat 64 i) (rbp : t.regValue .rbp=BitVec.ofNat 64 count)
    (rsi : t.regValue .rsi=s.regValue .rdi) (outer : ¬InProgram boundary.rip) :
    ∃ u, Advances boundary 4 t u ∧ FrameState s u ∧ u.RIP=0x10f4c0 ∧
      u.regValue .rcx=BitVec.ofNat 64 (i+count) ∧
      u.regValue .r14=s.regValue .rdi+BitVec.ofNat 64 i ∧ u.regValue .rdx=1 ∧
      AgreesExcept [.reg 1,.reg 14,.reg 2,.flags,.rip] t u := by
  have next (offset : Nat) (bound : offset < 118431) :=
    boundary_ne_program outer (inProgram_of_textOffset offset bound)
  obtain ⟨a, ra, readyA, loadedA, ea⟩ := Iterator.Advance.step_nomem (offset := 0xf4b2)
    (lea_r64_effect_step 0x10f4b2 0x49 (by simp [RexWPrefix]) 1
      (.sib 14 (some 5) 0 .none) (by decide) rfl rfl)
    (readyToStep state.machine state.bindingsSupported) state.loaded rip
    (by decide) (by decide +kernel) (next 0xf4b6 (by decide))
    (by simp [Component.Covers])
  have ga : AgreesExcept [.reg 1,.rip] t a := ea.agrees
  have cxA : a.regValue .rcx=BitVec.ofNat 64 (i+count) := by
    have h : a.regValue .rcx=t.regValue .r14+(t.regValue .rbp <<< (0 : Nat))+0#64 := ea.writes
    simpa only [r14,rbp,BitVec.shiftLeft_zero,BitVec.add_zero,BitVec.ofNat_add] using h
  obtain ⟨b, rb, readyB, loadedB, eb⟩ := Iterator.Advance.step_nomem (offset := 0xf4b6)
    (add_r64_r64_effect_step 0x10f4b6 0x49 0xf6 (by simp [RexWPrefix]) rfl)
    readyA loadedA ea.rip (by decide) (by decide +kernel) (next 0xf4b9 (by decide))
    (by simp [Component.Covers])
  have gb : AgreesExcept [.reg 14,.flags,.rip] a b := eb.agrees
  have indexB : b.regValue .r14=s.regValue .rdi+BitVec.ofNat 64 i := by
    have h : b.regValue .r14=a.regValue .r14+a.regValue .rsi := eb.writes
    have ha14 : a.regValue .r14=BitVec.ofNat 64 i := (ga.read (n := 64) (r := 14) (by simp)).trans r14
    have ha6 : a.regValue .rsi=s.regValue .rdi := (ga.read (n := 64) (r := 6) (by simp)).trans rsi
    rw [ha14,ha6,BitVec.add_comm] at h
    exact h
  obtain ⟨c, rc, readyC, loadedC, ec⟩ := Iterator.Advance.step_nomem (offset := 0xf4b9)
    (mov_r32_imm32_effect_step 0x10f4b9 0xba (by decide) 1)
    readyB loadedB eb.rip (by decide) (by decide +kernel) (next 0xf4be (by decide))
    (by simp [Component.Covers])
  have gc : AgreesExcept [.reg 2,.rip] b c := ec.agrees
  obtain ⟨u, ru, readyU, _, eu⟩ := Iterator.Advance.step_nomem (offset := 0xf4be)
    (nop_66_effect_step 0x10f4be) readyC loadedC ec.rip (by decide)
    (by decide +kernel) (next 0xf4c0 (by decide)) (by simp [nopEffect,Effect.components,Component.Covers])
  have gu : AgreesExcept [.rip] c u := eu.agrees
  have total : AgreesExcept [.reg 1,.reg 14,.reg 2,.flags,.rip] t u :=
    (((ga.trans gb).trans gc).trans gu).mono (by simp)
  refine ⟨u, ((ra.trans rb).trans rc).trans ru,
    state.after_registers readyU total (by simp [Component.Covers]) (by simp), eu.rip,
    (((gb.trans gc).trans gu).read (n := 64) (r := 1) (by simp)).trans cxA,
    ((gc.trans gu).read (n := 64) (r := 14) (by simp)).trans indexB, ?_, total⟩
  exact (gu.read (n := 64) (r := 2) (by simp)).trans ec.writes

end P256.Proofs.Verifying.Combination.Naf.Machine
