import X86Proofs.Instructions.MovStore.Triple
import Sha2.Proofs.Common.Encoding.Serialize.Store32.Decode
import Sha2.Proofs.Common.Encoding.Serialize.Store32.Step

set_option autoImplicit false

open X86Proofs

namespace Sha2.Proofs.Common.Instructions

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem mov_m32_r32_no_rex_effect_step [Bindings] (p : BitVec 64) (reg : BitVec 3)
    (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (StorePre p (2 + am.tail.length) (storeAddrAt p am (2 + am.tail.length)) 4)
      (codeRange p (0x89 :: am.modrm reg :: am.tail))
      (storeEffect p (2 + am.tail.length) (storeAddrAt p am (2 + am.tail.length))
        (fun s => (Operand.reg (gprNumber 0 0 reg) : Operand 32).read s)) :=
  StepEffect.of_store (n := 32) (by decide) (by decide) _ _
    fun s h hcode hpre => by
      obtain ⟨hp, hw, _⟩ := hpre
      subst hp
      have := am.tail_length_le
      exact mov_m32_r32_no_rex_step s h reg am hv hx hb hcode.bytesAt
        (hcode.low_len (by simp; omega) (by omega) (by omega)) hw

end Sha2.Proofs.Common.Instructions
