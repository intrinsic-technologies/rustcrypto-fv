import P256.Proofs.Sec1Serialize.Conversion.X.Machine
import P256.Proofs.Sec1Serialize.Conversion.Arithmetic

set_option autoImplicit false


namespace P256.Proofs.Sec1Serialize.Conversion

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

theorem convert_x_correct [bindings : Bindings] {s start t : RamState}
    {boundary : ReturnBoundary} {x : Nat}
    (pre : CalleePre s boundary 0x110d70 72 65 328)
    (stage : Stage s start t boundary)
    (rip : t.RIP = 0x110d88)
    (input : Field.MontgomeryAt t (s.regValue .rsi) x)
    (rsi : t.regValue .rsi = s.regValue .rsi)
    (r14 : t.regValue .r14 = s.regValue .rsi) :
    ∃ u, Stage s start u boundary ∧ u.RIP = 0x110ea5 ∧
      u.regValue .rbx = canonicalLimb x 0 ∧
      u.regValue .r15 = canonicalLimb x 1 ∧
      u.regValue .r12 = canonicalLimb x 2 ∧
      u.regValue .r13 = canonicalLimb x 3 ∧
      u.regValue .r9 = 0xffffffff00000001 ∧
      u.regValue .r14 = s.regValue .rsi ∧
      u.regValue .rdi = t.regValue .rdi ∧ u.external = t.external := by
  obtain ⟨u, stageu, ripu, values, constant, agrees⟩ := x_machine pre stage rip rsi r14
  rw [compilerConversionBV_of_montgomeryAt input] at values
  simp only [Prod.mk.injEq] at values
  refine ⟨u, stageu, ripu, values.1, values.2.1, values.2.2.1, values.2.2.2,
    constant, ?_, ?_, ?_⟩
  · exact (agrees.read (n := 64) (r := 14) (by simp [xRegisters])).trans r14
  · exact agrees.read (n := 64) (r := 7) (by simp [xRegisters])
  · exact agrees.external (by simp [xRegisters, Component.Covers])

end P256.Proofs.Sec1Serialize.Conversion
