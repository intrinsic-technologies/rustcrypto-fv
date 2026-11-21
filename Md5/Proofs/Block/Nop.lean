import X86Proofs.Instructions.NopMem.Triple

namespace Md5.Proofs.Block

open X86 X86.Machine X86.UserProcess X86Proofs

theorem nop_66_sib_disp8_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = p) (codeRange p [0x66, 0x0f, 0x1f, 0x44, 0x00, 0x00])
      (fun _ ↦ nopEffect p 6) :=
  nop_m_effect_step p [0x66] (by decide) (by decide)
    (.sib 0 (some 0) 0 (.d8 0)) ⟨by decide, fun h ↦ by cases h⟩ rfl rfl

theorem nop_66_sib_disp8_triple [Bindings] (p : BitVec 64) :
    Triple (fun s ↦ s.RIP = p) (codeRange p [0x66, 0x0f, 0x1f, 0x44, 0x00, 0x00])
      (Effect.post fun _ ↦ nopEffect p 6) :=
  Triple.of_effect (fun _ _ ↦ nopEffect_avoids p 6 _) (nop_66_sib_disp8_effect_step p)

end Md5.Proofs.Block
