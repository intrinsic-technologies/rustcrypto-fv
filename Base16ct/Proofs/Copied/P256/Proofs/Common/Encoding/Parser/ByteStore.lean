import X86Proofs.Instructions.MovStore.Triple
import Base16ct.Proofs.Copied.P256.Proofs.Common.Encoding.Parser.ByteStore.Decode
import Base16ct.Proofs.Copied.P256.Proofs.Common.Encoding.Parser.ByteStore.Form
import Base16ct.Proofs.Copied.P256.Proofs.Common.Encoding.Parser.ByteStore.Step
set_option autoImplicit false

open X86Proofs

namespace Base16ct.Proofs.Copied.P256.Proofs.Common.Instructions

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem mov_m8_r8_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (StorePre p (3 + am.tail.length) (storeAddrAt p am (3 + am.tail.length)) 1)
      (codeRange p (rex :: 0x88 :: am.modrm reg :: am.tail))
      (storeEffect p (3 + am.tail.length) (storeAddrAt p am (3 + am.tail.length))
        (fun s => (Operand.reg (gprNumber 0 (rexR rex.toBitVec) reg) : Operand 8).read s)) :=
  StepEffect.of_store (n := 8) (by decide) (by decide) _ _
    fun s h hcode hpre => by
      obtain ⟨hp, hw, _⟩ := hpre
      subst hp
      have := am.tail_length_le
      exact mov_m8_r8_step s h rex hrex reg am hv hx hb hcode.bytesAt
        (hcode.low_len (by simp; omega) (by omega) (by omega)) hw

end Base16ct.Proofs.Copied.P256.Proofs.Common.Instructions
