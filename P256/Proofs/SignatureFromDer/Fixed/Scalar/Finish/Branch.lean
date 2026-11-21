import P256.Proofs.SignatureFromDer.Fixed.Scalar.Finish.State
import P256.Proofs.Common.Instructions.ByteOps.Effects
import P256.Proofs.Common.Field.Operations.Select.TestAl
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

open P256.Proofs.Program (CalleePre boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice readyToStep)

namespace P256.Proofs.SignatureFromDer.Fixed.Scalar.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem range_branch [Bindings] {s t : RamState} {boundary : ReturnBoundary} {valid : Bool}
    (pre : CalleePre s boundary 0x10fa20 32 40 288) (state : Stage s t boundary)
    (rip : t.RIP = 0x10fb79) (rax : t.regValue .rax = if valid then 1 else 0) :
    ∃ u, Stage s u boundary ∧ u.RIP = (if valid then 0x10fb7d else 0x10fb90) ∧
      AgreesExcept [.flags, .rip] t u := by
  obtain ⟨b, hb, rb, eb⟩ :=
    (P256.Proofs.Common.Instructions.ByteOps.ByteOps.cmp_al_imm8_effect_step 0x10fb79 1).advances (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded)
        0xfb79 _ (by decide) (by decide +kernel)) rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xfb7b (by decide)))
  have fb : AgreesExcept [.flags, .rip] t b := eb.agrees
  have mb := (fb.external (by simp [Component.Covers]))
  have zf : (StatusFlags.ofRFLAGS b.RFLAGS).ZF = valid := by
    have hz := eb.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS b.RFLAGS).ZF =
      (cmpSpec ((t.regValue .rax).setWidth 8) 1).ZF at hz
    rw [hz, rax]
    cases valid <;> decide +kernel
  have cond : condHolds 5 (StatusFlags.ofRFLAGS b.RFLAGS) = !valid := by
    change (!(StatusFlags.ofRFLAGS b.RFLAGS).ZF) = !valid
    rw [zf]
  have next : (jccEffect 0x10fb7b 2 5 ((0x13 : BitVec 8).signExtend 64) b).rip =
      if valid then 0x10fb7d else 0x10fb90 := by
    simp only [jccEffect, cond]
    cases valid <;> rfl
  obtain ⟨u, hu, ru, eu⟩ := (jcc_rel8_effect_step 0x10fb7b 5 0x13).advances rb
    (programText_slice ((programLoaded_codeIn state.loaded).of_external_eq mb)
      0xfb7b _ (by decide) (by decide +kernel)) ⟨eb.rip, by intro; decide⟩
    (by rw [next]; cases valid
        · exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xfb90 (by decide))
        · exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xfb7d (by decide)))
  have fu : AgreesExcept [.rip] b u := eu.agrees
  have f : AgreesExcept [.flags, .rip] t u :=
    (fb.trans fu).mono (by simp)
  exact ⟨u, state.after_registers (hb.trans hu) ru f
    (by simp [Component.Covers]) (by simp) (by simp), eu.rip.trans next, f⟩

end P256.Proofs.SignatureFromDer.Fixed.Scalar.Finish
