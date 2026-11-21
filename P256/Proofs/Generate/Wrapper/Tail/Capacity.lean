import P256.Proofs.Generate.Wrapper.Tail.OutputSafety
import P256.Proofs.Generate.Wrapper.Tail.Registers
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Generate.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem capacity_payload [Bindings] {initial t : RamState} {input : ByteArray}
    {slices : Array Input} {d : Nat} {written : Option MemoryRegion}
    (call : ValidCallWithSlices signingKeyGenerateFromRng initial [input] slices)
    (draw : Ecdh.drawNonzeroScalar input = some d)
    (outside : ¬ InProgram (returnBoundary initial).rip)
    (state : State initial t 264 written) (rip : t.RIP = 0x106dba) :
    ∃ u, Advances (returnBoundary initial) 2 t u ∧ State initial u 264 written ∧
      u.RIP = 0x106dc4 ∧ AgreesExcept [.flags,.rip] t u := by
  obtain ⟨a, ha, ra, ea⟩ := (cmp_r64_imm8_effect_step 0x106dba 0x48 0xfb 39
    (by simp [RexWPrefix]) (by decide) (by decide)).advances
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x6dba _ (by decide) (by decide +kernel))
    rip (boundary_ne_program outside (inProgram_of_textOffset 0x6dbe (by decide)))
  have fa : AgreesExcept [.flags,.rip] t a := ea.agrees
  have ma := fa.external (by simp [Component.Covers])
  have cf : (StatusFlags.ofRFLAGS a.RFLAGS).CF = false := by
    have h := ea.flags.1
    change (StatusFlags.ofRFLAGS a.RFLAGS).CF = decide ((t.regValue .rbx).toNat < 39) at h
    rw [h, state.capacity]
    exact decide_eq_false (by have := output_capacity call draw; omega)
  have zf : (StatusFlags.ofRFLAGS a.RFLAGS).ZF = false := by
    have h := ea.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS a.RFLAGS).ZF = ((t.regValue .rbx - 39) == 0) at h
    rw [h, state.capacity]
    apply Bool.eq_false_iff.mpr
    intro hz
    have he : initial.regValue .r8 = 39 :=
      by simpa only [BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using BitVec.sub_eq_iff_eq_add.mp (of_decide_eq_true hz)
    have he' := congrArg BitVec.toNat he
    have := output_capacity call draw
    change (initial.regValue .r8).toNat = 39 at he'
    omega
  have cond : condHolds 6 (StatusFlags.ofRFLAGS a.RFLAGS) = false := by
    change ((StatusFlags.ofRFLAGS a.RFLAGS).CF || (StatusFlags.ofRFLAGS a.RFLAGS).ZF) = false
    rw [cf,zf]; rfl
  obtain ⟨u, step, ready, raw⟩ := jcc_rel32_effect_step 0x106dbe 6 0x12c a ra
    (programText_slice ((programLoaded_codeIn state.loaded).of_external_eq ma)
      0x6dbe _ (by decide) (by decide +kernel)) ⟨ea.rip, by intro; decide⟩
  have effect := jccEffect_not_taken cond raw
  have run : Advances (returnBoundary initial) 1 a u := Advances.of_step step (.inl (by
    rw [effect.rip]
    exact boundary_ne_program outside (inProgram_of_textOffset 0x6dc4 (by decide))))
  have fu : AgreesExcept [.rip] a u := effect.agrees
  have f : AgreesExcept [.flags,.rip] t u := (fa.trans fu).mono (by simp)
  exact ⟨u, ha.trans run, state.after_registers (ha.trans run) ready f (by simp [Component.Covers])
    (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp) (by simp), effect.rip, f⟩

theorem capacity_length [Bindings] {initial t : RamState} {input : ByteArray}
    {slices : Array Input} {d : Nat} {written : Option MemoryRegion}
    (call : ValidCallWithSlices signingKeyGenerateFromRng initial [input] slices)
    (draw : Ecdh.drawNonzeroScalar input = some d)
    (outside : ¬ InProgram (returnBoundary initial).rip)
    (state : State initial t 264 written) (rip : t.RIP = 0x106ed3) :
    ∃ u, Advances (returnBoundary initial) 2 t u ∧ State initial u 264 written ∧
      u.RIP = 0x106ed9 ∧ AgreesExcept [.flags,.rip] t u := by
  obtain ⟨a, ha, ra, ea⟩ := (cmp_r64_imm8_effect_step 0x106ed3 0x48 0xfb 7
    (by simp [RexWPrefix]) (by decide) (by decide)).advances
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x6ed3 _ (by decide) (by decide +kernel))
    rip (boundary_ne_program outside (inProgram_of_textOffset 0x6ed7 (by decide)))
  have fa : AgreesExcept [.flags,.rip] t a := ea.agrees
  have ma := fa.external (by simp [Component.Covers])
  have cf : (StatusFlags.ofRFLAGS a.RFLAGS).CF = false := by
    have h := ea.flags.1
    change (StatusFlags.ofRFLAGS a.RFLAGS).CF = decide ((t.regValue .rbx).toNat < 7) at h
    rw [h, state.capacity]
    exact decide_eq_false (by have := output_capacity call draw; omega)
  have zf : (StatusFlags.ofRFLAGS a.RFLAGS).ZF = false := by
    have h := ea.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS a.RFLAGS).ZF = ((t.regValue .rbx - 7) == 0) at h
    rw [h, state.capacity]
    apply Bool.eq_false_iff.mpr
    intro hz
    have he : initial.regValue .r8 = 7 :=
      by simpa only [BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using BitVec.sub_eq_iff_eq_add.mp (of_decide_eq_true hz)
    have he' := congrArg BitVec.toNat he
    have := output_capacity call draw
    change (initial.regValue .r8).toNat = 7 at he'
    omega
  have cond : condHolds 6 (StatusFlags.ofRFLAGS a.RFLAGS) = false := by
    change ((StatusFlags.ofRFLAGS a.RFLAGS).CF || (StatusFlags.ofRFLAGS a.RFLAGS).ZF) = false
    rw [cf,zf]; rfl
  obtain ⟨u, step, ready, raw⟩ := jcc_rel8_effect_step 0x106ed7 6 0x44 a ra
    (programText_slice ((programLoaded_codeIn state.loaded).of_external_eq ma)
      0x6ed7 _ (by decide) (by decide +kernel)) ⟨ea.rip, by intro; decide⟩
  have effect := jccEffect_not_taken cond raw
  have run : Advances (returnBoundary initial) 1 a u := Advances.of_step step (.inl (by
    rw [effect.rip]
    exact boundary_ne_program outside (inProgram_of_textOffset 0x6ed9 (by decide))))
  have fu : AgreesExcept [.rip] a u := effect.agrees
  have f : AgreesExcept [.flags,.rip] t u := (fa.trans fu).mono (by simp)
  exact ⟨u, ha.trans run, state.after_registers (ha.trans run) ready f (by simp [Component.Covers])
    (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp) (by simp), effect.rip, f⟩

end P256.Proofs.Generate.Wrapper
