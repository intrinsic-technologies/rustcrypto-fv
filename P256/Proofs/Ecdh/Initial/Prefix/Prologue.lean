import P256.Proofs.Program.SaveRegisters
import P256.Proofs.Program.ScalarFrame.Prologue
import X86Proofs.Instructions.Sub.Generated.Imm32.Triple

set_option autoImplicit false

open P256.Proofs.Program (CalleePre boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice)

namespace P256.Proofs.Ecdh.Initial.Prefix

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem prologue [bindings : Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x100000 32 32 3464) :
    ∃ t, Advances boundary 7 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = 0x100011 ∧ stackPtr t = stackPtr s - 2056 ∧
      t.external = P256.Proofs.Program.saveMemory s ∧
      AgreesExcept (P256.Proofs.Program.saveFrame s ++ [.flags]) s t := by
  obtain ⟨u, ha, hr, hl, hip, hsp, hm, hf⟩ :=
    P256.Proofs.Program.save_registers pre.stack
      (pre.avoids (Stack.region s 3464) (by simp)) pre.outerBoundary
      (P256.Proofs.Program.readyToStep pre.machine pre.bindingsSupported) pre.loaded
      (by decide +kernel) (codeOffset := 0x0) pre.rip
      (by constructor <;> decide +kernel)
  obtain ⟨t, hstep, hrt, het⟩ :=
    sub_r64_imm32_effect_step 0x10000a 0x48 0xec 2008
      (by unfold RexWPrefix; decide +kernel) rfl rfl u hr
      (programText_slice (programLoaded_codeIn hl) 0xa
        [0x48,0x81,0xec,0xd8,7,0,0] (by decide +kernel) rfl) hip
  have hip' : t.RIP = 0x100011 := het.rip
  have hat : Advances boundary 1 u t := Advances.of_step hstep (.inl (by
    rw [hip']
    exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x11 (by decide +kernel))))
  have hext : t.external = u.external := het.agrees.external
    (by simp [subR64Imm32Effect_components, Component.Covers])
  refine ⟨t, ha.trans hat, hrt, ?_, het.rip, ?_, hext.trans hm, ?_⟩
  · intro a b hab
    rw [hext]
    exact hl a b hab
  · have hwrite : stackPtr t = stackPtr u - 2008 := het.writes
    rw [hwrite, hsp, BitVec.sub_sub]
    rfl
  · apply (hf.trans het.agrees).mono
    simp only [P256.Proofs.Program.saveFrame, subR64Imm32Effect_components,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    intro c hc
    rcases hc with h | (rfl | rfl | rfl)
    · exact .inl h
    · exact .inl (.inl rfl)
    · exact .inr rfl
    · exact .inl (.inr (.inl rfl))

theorem frame_entry [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x100000 32 32 3464) :
    ∃ t, Advances boundary 7 s t ∧
      P256.Proofs.Program.ScalarFrame.FrameState s t 32 3464 2056 ∧
      t.RIP = 0x100011 ∧ t.external = P256.Proofs.Program.saveMemory s ∧
      AgreesExcept (P256.Proofs.Program.saveFrame s ++ [.flags]) s t := by
  obtain ⟨t, run, ready, loaded, rip, rsp, memory, agrees⟩ := prologue pre
  exact ⟨t, run, P256.Proofs.Program.ScalarFrame.prologue_frame pre (by decide)
    ready loaded rsp memory agrees, rip, memory, agrees⟩

end P256.Proofs.Ecdh.Initial.Prefix
