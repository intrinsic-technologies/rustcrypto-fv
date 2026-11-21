import Base16ct.Proofs.Copied.Md5.Proofs.Buffered.Stores.Step
import X86Proofs.Instructions.MovStore.Triple

namespace Base16ct.Proofs.Copied.Md5.Proofs.Buffered.Stores

open X86 X86.Machine X86.UserProcess X86Proofs X86.Helpers

theorem mov_m64_r64_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (Base16ct.Proofs.Copied.Md5.Proofs.Memory.StorePre p (3 + am.tail.length) (storeAddrAt p am (3 + am.tail.length)) 8)
      (codeRange p (rex :: 0x89 :: am.modrm reg :: am.tail))
      (movM64R64Effect p (gprNumber 0 (rexR rex.toBitVec) reg) am) :=
  Base16ct.Proofs.Copied.Md5.Proofs.Memory.stepEffect_of_store (n := 64) (by decide) (by decide) _ _
    fun s h hcode hpre => by
      obtain ⟨hp, hw, _⟩ := hpre
      subst hp
      have := am.tail_length_le
      exact mov_m64_r64_step s h rex hrex reg am hv hx hb hcode.bytesAt
        (hcode.low_len (by simp; omega) (by omega) (by omega)) hw

end Base16ct.Proofs.Copied.Md5.Proofs.Buffered.Stores
