import P256.Proofs.Common.Instructions.Setb.Memory.Step
import X86Proofs.Instructions.MovStore.Triple

namespace P256.Proofs.Common.Instructions.Setb

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

def setccM8Effect (p : BitVec 64) (len : Nat) (am : AddrMode) (cc : BitVec 4) : RamState → Effect :=
  storeEffect p len (storeAddrAt p am len) (setccValue cc)

theorem setccM8Effect_components (p : BitVec 64) (len : Nat) (am : AddrMode) (cc : BitVec 4)
    (s : RamState) :
    (setccM8Effect p len am cc s).components = [.mem (storeAddrAt p am len s) 1, .rip] :=
  storeEffect_components p len (storeAddrAt p am len) (setccValue cc) s

theorem setcc_m8_effect_step [Bindings] (p : BitVec 64) (opcode : UInt8)
    (hop : SupportedOpcode opcode) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (StorePre p (3 + am.tail.length) (storeAddrAt p am (3 + am.tail.length)) 1)
      (codeRange p (0x0F :: opcode :: am.modrm reg :: am.tail))
      (setccM8Effect p (3 + am.tail.length) am (opcode.toBitVec.extractLsb' 0 4)) :=
  StepEffect.of_store (n := 8) (by decide) (by decide) _ _
    fun s h hcode hpre => by
      obtain ⟨hp, hw, _⟩ := hpre
      subst hp
      have := am.tail_length_le
      exact setcc_m8_step s h opcode hop reg am hv hx hb hcode.bytesAt
        (hcode.low_len (by simp; omega) (by omega) (by omega)) hw

end P256.Proofs.Common.Instructions.Setb
