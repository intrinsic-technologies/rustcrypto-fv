import X86Proofs

namespace Base16ct.Proofs.Base16ctUpperDecodeCorrect.Instructions

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem nop_cs_10_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p)
      (codeRange p [0x66, 0x2e, 0x0f, 0x1f, 0x84, 0, 0, 0, 0, 0])
      (fun _ => nopEffect p 10) :=
  nop_m_effect_step p [0x66, 0x2e] (by decide) (by decide)
    (.sib 0 (some 0) 0 (.d32 0)) ⟨by decide, fun h => by cases h⟩ rfl rfl

theorem nop_osz_6_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p)
      (codeRange p [0x66, 0x0f, 0x1f, 0x44, 0, 0])
      (fun _ => nopEffect p 6) :=
  nop_m_effect_step p [0x66] (by decide) (by decide)
    (.sib 0 (some 0) 0 (.d8 0)) ⟨by decide, fun h => by cases h⟩ rfl rfl

end Base16ct.Proofs.Base16ctUpperDecodeCorrect.Instructions
