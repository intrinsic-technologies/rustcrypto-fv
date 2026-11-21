import P256.Proofs.SignatureFromSlice.Wrapper.Epilogue.Success.Memory
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.SignatureFromSlice.Wrapper.Epilogue.Success

open P256.Proofs.SignatureFromSlice.Wrapper.Epilogue

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem capacity_payload [Bindings] {initial t : RamState} (pre : Pre initial)
    (state : State initial t) (rip : t.RIP = 0x1022b1) :
    ∃ u, Advances (returnBoundary initial) 2 t u ∧ State initial u ∧
      u.RIP = 0x1022b7 ∧ AgreesExcept [.flags,.rip] t u := by
  obtain ⟨a, ha, ra, ea⟩ := (cmp_r64_imm8_effect_step 0x1022b1 0x49 0xfe 71
    (by simp [RexWPrefix]) (by decide) (by decide)).advances
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x22b1 _ (by decide) (by decide +kernel))
    rip (boundary_ne_program pre.outside (inProgram_of_textOffset 0x22b5 (by decide)))
  have fa : AgreesExcept [.flags,.rip] t a := ea.agrees
  have ma := fa.external (by simp [Component.Covers])
  have cf : (StatusFlags.ofRFLAGS a.RFLAGS).CF = false := by
    have h := ea.flags.1
    change (StatusFlags.ofRFLAGS a.RFLAGS).CF = decide ((t.regValue .r14).toNat < 71) at h
    rw [h, state.capacity]
    exact decide_eq_false (by have := pre.capacity; omega)
  have zf : (StatusFlags.ofRFLAGS a.RFLAGS).ZF = false := by
    have h := ea.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS a.RFLAGS).ZF = ((t.regValue .r14 - 71) == 0) at h
    rw [h, state.capacity]
    apply Bool.eq_false_iff.mpr
    intro hz
    have he : initial.regValue .r8 = 71 :=
      by simpa only [BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using BitVec.sub_eq_iff_eq_add.mp (of_decide_eq_true hz)
    have he' := congrArg BitVec.toNat he
    have := pre.capacity
    change (initial.regValue .r8).toNat = 71 at he'
    omega
  have cond : condHolds 6 (StatusFlags.ofRFLAGS a.RFLAGS) = false := by
    change ((StatusFlags.ofRFLAGS a.RFLAGS).CF || (StatusFlags.ofRFLAGS a.RFLAGS).ZF) = false
    rw [cf,zf]; rfl
  obtain ⟨u, step, ready, raw⟩ := jcc_rel8_effect_step 0x1022b5 6 0x76 a ra
    (programText_slice ((programLoaded_codeIn state.loaded).of_external_eq ma)
      0x22b5 _ (by decide) (by decide +kernel)) ⟨ea.rip, by intro; decide⟩
  have effect := jccEffect_not_taken cond raw
  have run : Advances (returnBoundary initial) 1 a u := Advances.of_step step (.inl (by
    rw [effect.rip]
    exact boundary_ne_program pre.outside (inProgram_of_textOffset 0x22b7 (by decide))))
  have fu : AgreesExcept [.rip] a u := effect.agrees
  have f : AgreesExcept [.flags,.rip] t u := (fa.trans fu).mono (by simp)
  exact ⟨u, ha.trans run, state.after_registers ready f (by simp [Component.Covers])
    (by simp) (by simp), effect.rip, f⟩

end P256.Proofs.SignatureFromSlice.Wrapper.Epilogue.Success
