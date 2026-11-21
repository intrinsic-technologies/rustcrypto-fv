import Base16ct.Proofs.Base16ctUpperDecodeCorrect.LoopStep.LoopConcrete
set_option linter.unusedSimpArgs false
namespace Base16ct.Proofs.Base16ctUpperDecodeCorrect
open Base16ct.Spec Base16ct.Spec.Program

end Base16ct.Proofs.Base16ctUpperDecodeCorrect

namespace Base16ct.Proofs.Base16ctUpperDecodeCorrect
open Base16ct.Spec Base16ct.Spec.Program Base16ct.Spec.Program.Extracted
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Base16ct.Proofs.Base16ctUpperDecodeCorrect.Instructions

theorem signext_low (c : BitVec 8) :
    (c.signExtend 64).extractLsb' 0 32 = c.signExtend 32 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.extractLsb', BitVec.signExtend]
  omega

theorem low32_add_signext8 (x : BitVec 64) (c : BitVec 8) :
    (x + c.signExtend 64).extractLsb' 0 32 = x.setWidth 32 + c.signExtend 32 := by
  rw [BitVec.extractLsb'_add (by decide)]
  rw [← BitVec.setWidth_eq_extractLsb' (by decide), signext_low]

theorem tail_mov_value {s t : RamState} {p : BitVec 64} {len : Nat} {dst : BitVec 5} {imm : BitVec 32}
    (he : (movR32Imm32Effect p len dst imm s).Holds s t) :
    (Operand.reg dst : Operand 32).read t = imm := by
  have hw := he.writes
  simp [movR32Imm32Effect, Write.AllHold] at hw
  change t.GPR[dst.toNat] = _ at hw
  change BitVec.setWidth 32 t.GPR[dst.toNat] = _
  rw [hw]
  simp [gprIndex]

theorem tail_bin_value {s t : RamState} {p : BitVec 64} {len : Nat} {dst src : BitVec 5}
    (he : (subR32R32Effect p len dst src s).Holds s t) :
    (Operand.reg dst : Operand 32).read t =
      ((Operand.reg dst : Operand 32).read s - (Operand.reg src : Operand 32).read s) := by
  have hw := he.writes
  simp [subR32R32Effect, Write.AllHold] at hw
  change t.GPR[dst.toNat] = _ at hw
  change BitVec.setWidth 32 t.GPR[dst.toNat] = _
  rw [hw]
  simp [gprIndex]

theorem tail_and_value {s t : RamState} {p : BitVec 64} {len : Nat} {dst src : BitVec 5}
    (he : (andR32R32Effect p len dst src s).Holds s t) :
    (Operand.reg dst : Operand 32).read t =
      ((Operand.reg dst : Operand 32).read s &&& (Operand.reg src : Operand 32).read s) := by
  have hw := he.writes
  simp [andR32R32Effect, Write.AllHold] at hw
  change t.GPR[dst.toNat] = _ at hw
  change BitVec.setWidth 32 t.GPR[dst.toNat] = _
  rw [hw]
  simp [gprIndex]

theorem tail_add8_value {s t : RamState} {p : BitVec 64} {len : Nat} {dst : BitVec 5} {imm : BitVec 8}
    (he : (addR32Imm8Effect p len dst imm s).Holds s t) :
    (Operand.reg dst : Operand 32).read t =
      ((Operand.reg dst : Operand 32).read s + imm.signExtend 32) := by
  have hw := he.writes
  simp [addR32Imm8Effect, Write.AllHold] at hw
  change t.GPR[dst.toNat] = _ at hw
  change BitVec.setWidth 32 t.GPR[dst.toNat] = _
  rw [hw]
  simp [gprIndex]

theorem tail_dec_value {s t : RamState} {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    (he : (decR32Effect p len dst s).Holds s t) :
    (Operand.reg dst : Operand 32).read t =
      ((Operand.reg dst : Operand 32).read s - 1) := by
  have hw := he.writes
  simp [decR32Effect, Write.AllHold] at hw
  change t.GPR[dst.toNat] = _ at hw
  change BitVec.setWidth 32 t.GPR[dst.toNat] = _
  rw [hw]
  simp [gprIndex]

theorem tail_lea_value {s t : RamState} {p : BitVec 64} {len : Nat} {dst : BitVec 5} {am : AddrMode}
    (he : (Instructions.leaR32Effect p len dst am s).Holds s t) :
    (Operand.reg dst : Operand 32).read t =
      (am.addr s (p + BitVec.ofNat 64 len)).extractLsb' 0 32 := by
  have hw := he.writes
  simp [Instructions.leaR32Effect, Write.AllHold] at hw
  change t.GPR[dst.toNat] = _ at hw
  change BitVec.setWidth 32 t.GPR[dst.toNat] = _
  rw [hw]
  simp [AddrMode.addr, Disp.value]

theorem tail_movsx_value {s t : RamState} {p : BitVec 64} {dst src : BitVec 5}
    (he : (Instructions.movsxR32R16Effect p dst src s).Holds s t) :
    (Operand.reg dst : Operand 32).read t =
      ((Operand.reg src : Operand 16).read s).signExtend 32 := by
  have hw := he.writes
  simp [Instructions.movsxR32R16Effect, Write.AllHold] at hw
  change t.GPR[dst.toNat] = _ at hw
  change BitVec.setWidth 32 t.GPR[dst.toNat] = _
  rw [hw]
  simp [gprIndex]

theorem tail_sar_value {s t : RamState} {p : BitVec 64} {len : Nat} {dst : BitVec 5} {c : Nat}
    (he : (Instructions.sarR32Effect p len dst c s).Holds s t) :
    (Operand.reg dst : Operand 32).read t =
      ((Operand.reg dst : Operand 32).read s).sshiftRight c := by
  have hw := he.writes
  simp [Instructions.sarR32Effect, Write.AllHold] at hw
  change t.GPR[dst.toNat] = _ at hw
  change BitVec.setWidth 32 t.GPR[dst.toNat] = _
  rw [hw]
  simp [gprIndex]

theorem tail_or_value {s t : RamState} {p : BitVec 64} {len : Nat} {dst src : BitVec 5}
    (he : (Instructions.orR32R32Effect p len dst src s).Holds s t) :
    (Operand.reg dst : Operand 32).read t =
      ((Operand.reg dst : Operand 32).read s ||| (Operand.reg src : Operand 32).read s) := by
  have hw := he.writes
  simp [Instructions.orR32R32Effect, Write.AllHold] at hw
  change t.GPR[dst.toNat] = _ at hw
  change BitVec.setWidth 32 t.GPR[dst.toNat] = _
  rw [hw]
  simp [gprIndex]

end Base16ct.Proofs.Base16ctUpperDecodeCorrect
namespace Base16ct.Proofs.Base16ctUpperDecodeCorrect
open Base16ct.Spec Base16ct.Spec.Program X86Proofs

def decodeTailExpanded (alphabet : RFC4648.Alphabet) (byte : UInt8) : BitVec 32 :=
  let low := byte.toBitVec.setWidth 32
  let offset := decodeLetterOffset alphabet
  (low - 47#32 &&&
    (BitVec.signExtend 32 (BitVec.extractLsb' 0 16
      ((low - 58#32) &&& (47#32 - low)))).sshiftRight (shiftCount 32 8#8)) +
    (low + ((10#32 - offset).setWidth 8).signExtend 32 &&&
      (BitVec.signExtend 32 (BitVec.extractLsb' 0 16
        ((low - (offset + 7#32)) &&& (offset - low)))).sshiftRight (shiftCount 32 8#8)) - 1

theorem decodeTailExpanded_correct (alphabet : RFC4648.Alphabet) (byte : UInt8) :
    decodeTailExpanded alphabet byte = decodeLowNibble [alphabet] byte := by
  have h : ∀ n : Fin 256, decodeTailExpanded alphabet (UInt8.ofNat n.val) =
      decodeLowNibble [alphabet] (UInt8.ofNat n.val) := by
    cases alphabet <;> decide +kernel
  simpa using h ⟨byte.toNat, byte.toFin.isLt⟩

end Base16ct.Proofs.Base16ctUpperDecodeCorrect
namespace Base16ct.Proofs.Base16ctUpperDecodeCorrect
open Base16ct.Spec Base16ct.Spec.Program X86 X86.Machine X86Proofs
open Base16ct.Proofs.Base16ctUpperDecodeCorrect.Instructions
 theorem tail_movzx_bh_value {s t : RamState} {p : BitVec 64}
    (he : (movzxEbxBhEffect p s).Holds s t) :
    (Operand.reg 3#5 : Operand 32).read t =
      BitVec.setWidth 32 (((Operand.reg 3#5 : Operand 64).read s).extractLsb' 8 8) := by
  have hw := he.writes
  simp [movzxEbxBhEffect, Write.AllHold] at hw
  change t.GPR[3] = _ at hw
  have hh := congrArg (fun x : BitVec 64 => x.setWidth 32) hw
  change BitVec.setWidth 32 t.GPR[3] = BitVec.setWidth 32 (BitVec.extractLsb' 8 8 s.GPR[3])
  simpa [BitVec.setWidth_setWidth] using hh
end Base16ct.Proofs.Base16ctUpperDecodeCorrect
