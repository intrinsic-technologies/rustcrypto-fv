import X86Proofs.Instructions.Pop.Triple

set_option autoImplicit false

namespace Sha2.Proofs.Common.Encoding.Serialize

open X86 X86.Machine X86.UserProcess X86Proofs

theorem pop_register_effect_step [Bindings] (p : BitVec 64) (dst : BitVec 4)
    (hdst : dst.setWidth 5 ≠ 4) :
    StepEffect (PopPre p) (codeRange p (encodePopR64 dst))
      (popR64Effect p (encodePopR64 dst).length (dst.setWidth 5)) := by
  apply StepEffect.of_pop hdst
  intro t ready code pre
  have hip := pre.rip
  subst hip
  have hlen : 0 < (encodePopR64 dst).length ∧ (encodePopR64 dst).length ≤ 15 := by
    rcases encodePopR64_spec dst with ⟨op, hb, _, _⟩ | ⟨rex, op, hb, _, _, _⟩ <;>
      simp [hb]
  exact pop_r64_step_of_register t ready dst code.bytesAt
    (code.low hlen.1 (by omega)) pre.read

end Sha2.Proofs.Common.Encoding.Serialize
