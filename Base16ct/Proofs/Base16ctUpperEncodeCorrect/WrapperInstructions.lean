import Base16ct.Proofs.Copied.P256.Proofs.Keygen.Multiply.Inverse.SafeGcd.LinearCombination.CompareMemory
import Base16ct.Proofs.Copied.Md5.Proofs.Block.Rounds.Load.Mov
import Base16ct.Proofs.Base16ctUpperEncodeCorrect.LoopInstructions.Or

namespace Base16ct.Proofs.Base16ctUpperEncodeCorrect

open X86 X86.Machine X86.UserProcess X86Proofs

export Base16ct.Proofs.Copied.P256.Proofs.Keygen.Multiply.Inverse.SafeGcd.LinearCombination
  (cmpM64Imm8Effect cmpM64Imm8Effect_components cmpM64Imm8Effect_local
    cmp_m64_imm8_effect_step)

export Base16ct.Proofs.Copied.Md5.Proofs.Block.Rounds
  (movR32M32NoRexEffect movR32M32NoRexEffect_local mov_r32_m32_noRex_effect_step)

theorem cmpM64Imm8Effect_avoids (p : BitVec 64) (len : Nat) (am : AddrMode)
    (imm : BitVec 8) (s : RamState) (code : CodeMap) :
    (cmpM64Imm8Effect p len am imm s).Avoids code :=
  Effect.Avoids.of_noMem (by
    rw [cmpM64Imm8Effect_components]
    simp [Component.Covers]) code

theorem cmpM64Imm8Effect_ZF {p : BitVec 64} {len : Nat} {am : AddrMode} {imm : BitVec 8}
    {s t : RamState} (h : (cmpM64Imm8Effect p len am imm s).Holds s t) :
    (StatusFlags.ofRFLAGS t.RFLAGS).ZF =
      decide ((Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 64).read s =
        imm.signExtend 64) := by
  have hz : (StatusFlags.ofRFLAGS t.RFLAGS).ZF =
      (cmpSpec ((Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 64).read s)
        (imm.signExtend 64)).ZF := h.flags.2.2.2.1
  rw [hz]
  simp only [cmpSpec, subSpec]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq, BitVec.sub_eq_iff_eq_add]
  change (_ = BitVec.add 0#64 (imm.signExtend 64)) ↔ _
  have hzadd : BitVec.add 0#64 (imm.signExtend 64) = imm.signExtend 64 := BitVec.zero_add _
  rw [hzadd]

theorem movR32M32NoRexEffect_components (p : BitVec 64) (dst : BitVec 5) (am : AddrMode)
    (s : RamState) :
    (movR32M32NoRexEffect p dst am s).components = [.reg dst, .rip] := rfl

theorem movR32M32NoRexEffect_avoids (p : BitVec 64) (dst : BitVec 5) (am : AddrMode)
    (s : RamState) (code : CodeMap) : (movR32M32NoRexEffect p dst am s).Avoids code :=
  Effect.avoids_of_components_reg_rip (movR32M32NoRexEffect_components p dst am s) code

end Base16ct.Proofs.Base16ctUpperEncodeCorrect
