import X86Proofs.Instructions.Pop.Triple

set_option autoImplicit false

namespace P256.Proofs.Program

open X86 X86.Machine X86.UserProcess X86Proofs

theorem pop_register_effect_step [Bindings] (p : BitVec 64) (dst : BitVec 4)
    (hdst : dst.setWidth 5 ≠ 4) :
    StepEffect (PopPre p) (codeRange p (encodePopR64 dst))
      (popR64Effect p (encodePopR64 dst).length (dst.setWidth 5)) := by
  rcases encodePopR64_spec dst with ⟨op, hb, hop, hr⟩ | ⟨rex, op, hb, hre, hop, hr⟩
  · rw [hb, ← hr]
    exact pop_r64_effect_step p op hop (hr ▸ hdst)
  · rw [hb, ← hr]
    exact pop_r64_rex_effect_step p rex op hre hop (hr ▸ hdst)

end P256.Proofs.Program
