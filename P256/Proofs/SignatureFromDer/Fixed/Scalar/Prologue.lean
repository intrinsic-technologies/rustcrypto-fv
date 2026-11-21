import P256.Proofs.Program.SaveRegisters
import P256.Proofs.Program.Interface
import X86Proofs.Instructions.Sub.Generated.Imm8.Triple

set_option autoImplicit false

open P256.Proofs.Program (CalleePre boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice)

namespace P256.Proofs.SignatureFromDer.Fixed.Scalar

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem scalar_prologue [bindings : Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10fa20 32 40 288) :
    ∃ t, Advances boundary 7 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = 0x10fa2e ∧ stackPtr t = stackPtr s - 152 ∧
      t.external = P256.Proofs.Program.saveMemory s ∧
      AgreesExcept (P256.Proofs.Program.saveFrame s ++ [.flags]) s t := by
  obtain ⟨u, ha, hr, hl, hip, hsp, hm, hf⟩ :=
    P256.Proofs.Program.save_registers pre.stack
      (pre.avoids (Stack.region s 288) (by simp)) pre.outerBoundary
      (P256.Proofs.Program.readyToStep pre.machine pre.bindingsSupported) pre.loaded
      (by decide +kernel) (codeOffset := 0xfa20) pre.rip
      (by constructor <;> decide +kernel)
  obtain ⟨t, hstep, hrt, het⟩ :=
    sub_r64_imm8_effect_step 0x10fa2a 0x48 0xec 104
      (by unfold RexWPrefix; decide +kernel) rfl rfl u hr
      (programText_slice (programLoaded_codeIn hl) 0xfa2a
        [0x48,0x83,0xec,0x68] (by decide +kernel) rfl) hip
  have hip' : t.RIP = 0x10fa2e := het.rip
  have hat : Advances boundary 1 u t := Advances.of_step hstep (.inl (by
    rw [hip']
    exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xfa2e (by decide +kernel))))
  have hext : t.external = u.external := het.agrees.external
    (by simp [subR64Imm8Effect_components, Component.Covers])
  refine ⟨t, ha.trans hat, hrt, ?_, het.rip, ?_, hext.trans hm, ?_⟩
  · intro a b hab
    rw [hext]
    exact hl a b hab
  · have hwrite : stackPtr t = stackPtr u - 104 := het.writes
    rw [hwrite, hsp, BitVec.sub_sub]
    rfl
  · apply (hf.trans het.agrees).mono
    simp only [P256.Proofs.Program.saveFrame, subR64Imm8Effect_components,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    intro c hc
    rcases hc with h | (rfl | rfl | rfl)
    · exact .inl h
    · exact .inl (.inl rfl)
    · exact .inr rfl
    · exact .inl (.inr (.inl rfl))

end P256.Proofs.SignatureFromDer.Fixed.Scalar
