import Md5.Proofs.Buffered.Stores.Effect
import Md5.Proofs.Block.Rounds.Store.Step
import Md5.Proofs.Block.Rounds.Store.Compose

namespace Md5.Proofs.Block.Rounds.Store

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem mov_m32_r32_noRex_effect_step [Bindings] (p : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (Md5.Proofs.Memory.StorePre p (2 + am.tail.length)
      (storeAddrAt p am (2 + am.tail.length)) 4)
      (codeRange p (0x89 :: am.modrm reg :: am.tail))
      (movM32R32NoRexEffect p (gprNumber 0 0 reg) am) :=
  Md5.Proofs.Memory.stepEffect_of_store (n := 32) (by decide) (by decide) _ _
    fun s h hcode hpre => by
      obtain ⟨hp, hw, _⟩ := hpre
      subst hp
      have := am.tail_length_le
      exact mov_m32_r32_noRex_step s h reg am hv hx hb hcode.bytesAt
        (hcode.low_len (by simp only [List.length_cons]; omega) (by omega) (by omega)) hw

end Md5.Proofs.Block.Rounds.Store
