import AesGcm.Proofs.AES16.Layout
import AesGcm.Proofs.Machine.GHASH.Bytes
import Standards.NIST.AES.Cipher

namespace AesGcm.Proofs.Machine.GcmContext

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.Lift X86Proofs.Refine
open Standards.NIST.AES

def size (v : Variant) : Nat := 32 + 16 * (v.Nr + 1)

def blockWord (block : Block) (half : Fin 2) : BitVec 64 :=
  bswapSpec (Fixslice.packBytes (fun q : Fin 8 ↦
    block[8 * half.val + q.val]'(by omega) |>.toBitVec))

theorem getLsbD_blockWord (block : Block) (half : Fin 2) (i : Fin 64) :
    (blockWord block half).getLsbD i.val =
      (block[8 * half.val + (7 - i.val / 8)]'(by omega)).toBitVec.getLsbD (i.val % 8) := by
  rw [blockWord, bswapSpec, getLsbD_ofLanes _ i.val i.isLt]
  simp only [lane, Nat.reduceDiv, BitVec.getLsbD_extractLsb',
    show i.val % 8 < 8 by omega, decide_true, Bool.true_and,
    show i.val < 8 * 8 from i.isLt, ite_true, Nat.reduceSub]
  rw [Fixslice.getLsbD_packBytes _ ⟨(7 - i.val / 8) * 8 + i.val % 8, by omega⟩]
  have hd : ((7 - i.val / 8) * 8 + i.val % 8) / 8 = 7 - i.val / 8 := by omega
  have hm : ((7 - i.val / 8) * 8 + i.val % 8) % 8 = i.val % 8 := by omega
  simp only [hd, hm]


theorem blockWords_bytes (block : Block) :
    GHASH.toBigEndianBytes (blockWord block 0 ++ blockWord block 1) = block := by
  apply Vector.ext
  intro j hj
  apply UInt8.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [GHASH.toBigEndianBytes, Vector.getElem_ofFn, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_append, hi, decide_true, Bool.true_and]
  by_cases h : j < 8
  · simp only [show ¬ 8 * (15 - j) + i < 64 by omega, ite_false]
    rw [getLsbD_blockWord _ 0 ⟨8 * (15 - j) + i - 64, by omega⟩]
    have hd : 7 - (8 * (15 - j) + i - 64) / 8 = j := by omega
    have hm : (8 * (15 - j) + i - 64) % 8 = i := by omega
    simp only [Fin.val_zero, Nat.mul_zero, Nat.zero_add, hd, hm]
  · simp only [show 8 * (15 - j) + i < 64 by omega, ite_true]
    rw [getLsbD_blockWord _ 1 ⟨8 * (15 - j) + i, by omega⟩]
    have hd : 8 + (7 - (8 * (15 - j) + i) / 8) = j := by omega
    have hm : (8 * (15 - j) + i) % 8 = i := by omega
    simp only [Fin.val_one, Nat.mul_one, hd, hm]


def authenticationKey (v : Variant) (key : Vector UInt8 v.keyBytes) : BitVec 64 × BitVec 64 :=
  let h := cipher v key (Vector.replicate 16 0)
  GHASH.polyvalKeyWords (blockWord h 1) (blockWord h 0)

def ContextIn (v : Variant) (key : Vector UInt8 v.keyBytes)
    (dst : BitVec 64) (mem : Ram) : Prop :=
  AES16.ScheduleIn v key (dst + 32) mem ∧
    memLoad mem dst 64 = (authenticationKey v key).1 ∧
    memLoad mem (dst + 8) 64 = (authenticationKey v key).2 ∧
    memLoad mem (dst + 16) 64 = 0 ∧ memLoad mem (dst + 24) 64 = 0

end AesGcm.Proofs.Machine.GcmContext
