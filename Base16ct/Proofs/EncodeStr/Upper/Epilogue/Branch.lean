import Base16ct.Proofs.EncodeStr.Upper.Context
import Base16ct.Proofs.EncodeStr.Upper.WrapperInstructions
import X86Proofs.Instructions.Branch.Triple

namespace Base16ct.Proofs.EncodeStr.Upper.Epilogue

open Base16ct.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem branch_run [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s)
    (hip : s.RIP = 0x100476) (hm : MemReadable s (stackPtr s) 8)
    (ho : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧
      t.RIP = (if (Operand.mem (stackPtr s) : Operand 64).read s = 0
        then 0x10048d else 0x10047d) ∧ AgreesExcept [.flags, .rip] s t := by
  have hc1 : CodeIn (codeRange 0x100476 [0x48, 0x83, 0x3c, 0x24, 0x00]) s := by
    have hb : Extracted.textBytes.toListFrom 0x476 5 =
        [0x48, 0x83, 0x3c, 0x24, 0x00] := by decide +kernel
    have hx := program_text_slice hc 0x476 5 (by decide +kernel)
    rw [hb, show Extracted.textAddress + BitVec.ofNat 64 0x476 = 0x100476 by decide +kernel] at hx
    exact hx
  have hzero : stackPtr s + 0 = stackPtr s := BitVec.add_zero _
  obtain ⟨u, run1, ready1, e1⟩ :=
    (cmp_m64_imm8_effect_step 0x100476 (.sib 4 none 0 (.none))
      (by decide +kernel) rfl rfl 0).advances hr hc1 ⟨hip, by
        change MemReadable s (stackPtr s + 0) 8
        simpa only [hzero] using hm⟩
      (text_address_ne_return ho 0x47b (by decide +kernel))
  have a1 : AgreesExcept [.flags, .rip] s u := e1.agrees
  have hcu := a1.codeIn (by simp [Component.Covers]) hc
  have hc2 : CodeIn (codeRange 0x10047b [0x74, 0x10]) u := by
    have hb : Extracted.textBytes.toListFrom 0x47b 2 = [0x74, 0x10] := by decide +kernel
    have hx := program_text_slice hcu 0x47b 2 (by decide +kernel)
    rw [hb, show Extracted.textAddress + BitVec.ofNat 64 0x47b = 0x10047b by decide +kernel] at hx
    exact hx
  have hz := cmpM64Imm8Effect_ZF e1
  change (StatusFlags.ofRFLAGS u.RFLAGS).ZF =
    decide ((Operand.mem (stackPtr s + 0) : Operand 64).read s = 0) at hz
  rw [hzero] at hz
  obtain ⟨t, step2, ready2, e2⟩ := jcc_rel8_effect_step 0x10047b 4 0x10 u ready1 hc2
    ⟨e1.rip, fun _ => by decide⟩
  have ht : t.RIP = (if (Operand.mem (stackPtr s) : Operand 64).read s = 0
      then 0x10048d else 0x10047d) := by
    rw [e2.rip]
    simp [jccEffect, branchEffect, condHolds, hz, branchTarget]
  have run2 : Advances boundary 1 u t := by
    apply Advances.of_step step2
    left
    rw [ht]
    split
    · exact text_address_ne_return ho 0x48d (by decide +kernel)
    · exact text_address_ne_return ho 0x47d (by decide +kernel)
  exact ⟨t, run1.trans run2, ready2, ht,
    (a1.trans e2.agrees).mono (by simp [jccEffect, branchEffect, Effect.components])⟩

end Base16ct.Proofs.EncodeStr.Upper.Epilogue
