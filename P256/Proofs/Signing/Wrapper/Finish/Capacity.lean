import P256.Proofs.Signing.Wrapper.Finish.State
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem capacity_payload [Bindings] {initial t : RamState} (pre : Pre initial)
    (state : State initial t) (rip : t.RIP = 0x102a46)
    (capacity : t.regValue .rdx = initial.regValue .r8) :
    ∃ u, Advances (returnBoundary initial) 2 t u ∧ State initial u ∧
      u.RIP = 0x102a50 ∧ AgreesExcept [.flags,.rip] t u := by
  obtain ⟨a, ha, ra, ea⟩ := (cmp_r64_imm8_effect_step 0x102a46 0x48 0xfa 71
    (by simp [RexWPrefix]) (by decide) (by decide)).advances
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x2a46 _ (by decide) (by decide +kernel))
    rip (boundary_ne_program pre.outside (inProgram_of_textOffset 0x2a4a (by decide)))
  have fa : AgreesExcept [.flags,.rip] t a := ea.agrees
  have ma := fa.external (by simp [Component.Covers])
  have cf : (StatusFlags.ofRFLAGS a.RFLAGS).CF = false := by
    have h := ea.flags.1
    change (StatusFlags.ofRFLAGS a.RFLAGS).CF = decide ((t.regValue .rdx).toNat < 71) at h
    rw [h, capacity]
    exact decide_eq_false (by have := pre.capacity; omega)
  have zf : (StatusFlags.ofRFLAGS a.RFLAGS).ZF = false := by
    have h := ea.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS a.RFLAGS).ZF = ((t.regValue .rdx - 71) == 0) at h
    rw [h, capacity]
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
  obtain ⟨u, step, ready, raw⟩ := jcc_rel32_effect_step 0x102a4a 6 0xe0 a ra
    (programText_slice ((programLoaded_codeIn state.loaded).of_external_eq ma)
      0x2a4a _ (by decide) (by decide +kernel)) ⟨ea.rip, by intro; decide⟩
  have effect := jccEffect_not_taken cond raw
  have run : Advances (returnBoundary initial) 1 a u := Advances.of_step step (.inl (by
    rw [effect.rip]
    exact boundary_ne_program pre.outside (inProgram_of_textOffset 0x2a50 (by decide))))
  have fu : AgreesExcept [.rip] a u := effect.agrees
  have f : AgreesExcept [.flags,.rip] t u := (fa.trans fu).mono (by simp)
  exact ⟨u, ha.trans run, state.after_registers ready f (by simp [Component.Covers])
    (by simp) (by simp), effect.rip, f⟩

end P256.Proofs.Signing.Wrapper.Finish
