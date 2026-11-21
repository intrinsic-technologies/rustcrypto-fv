import AesGcm.Proofs.Machine.GcmContext
import AesGcm.Proofs.Machine.GHASHInterface
import AesGcm.Proofs.Common.Detached

namespace AesGcm.Proofs.Machine.Tag

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.GHASH AesGcm.Proofs.Machine.GHASHInterface

def stateBits (s : BitVec 64 × BitVec 64) : Vector Bool 128 :=
  toGcmBits (s.2 ++ s.1).reverse

theorem stateBits_xor (s x : BitVec 64 × BitVec 64) :
    stateBits (s.1 ^^^ x.1, s.2 ^^^ x.2) =
      Standards.NIST.GCM.xor (stateBits s) (stateBits x) := by
  dsimp only [stateBits]
  rw [← BitVec.xor_append, reverse_xor, toGcmBits_xor]

theorem stateBits_zero : stateBits (0, 0) = Standards.NIST.GCM.zeros 128 := by
  decide +kernel

theorem stateBits_multiply (h : Vector UInt8 16) (s x : BitVec 64 × BitVec 64) :
    let k := polyvalKeyWords (GcmContext.blockWord h 1) (GcmContext.blockWord h 0)
    stateBits (polyvalMultiplyWords (s.1 ^^^ x.1) (s.2 ^^^ x.2) k.1 k.2) =
      Standards.NIST.GCM.mul (Standards.NIST.GCM.xor (stateBits s) (stateBits x))
        (Standards.NIST.GCM.bitsOfBytes h) := by
  dsimp only
  rw [stateBits, polyvalMultiplyWords_adjusted_eq_standard]
  rw [toGcmBits_reverse_eq_bitsOfBytes (GcmContext.blockWord h 0 ++ GcmContext.blockWord h 1),
    GcmContext.blockWords_bytes]
  rw [← stateBits_xor]
  rfl

def sourceBlockBits (mem : Ram) (src : BitVec 64) (j : Nat) : Vector Bool 128 :=
  stateBits (bswapSpec (memLoad mem (src + BitVec.ofNat 64 (16*j+8)) 64),
    bswapSpec (memLoad mem (src + BitVec.ofNat 64 (16*j)) 64))

theorem updateBlocks_bits (mem : Ram) (src : BitVec 64) (count : Nat)
    (h : Vector UInt8 16) (s : BitVec 64 × BitVec 64) :
    let k := polyvalKeyWords (GcmContext.blockWord h 1) (GcmContext.blockWord h 0)
    stateBits (updateBlocks mem src count k.1 k.2 s) =
      (List.range count).foldl (fun acc j ↦
        Standards.NIST.GCM.mul (Standards.NIST.GCM.xor acc (sourceBlockBits mem src j))
          (Standards.NIST.GCM.bitsOfBytes h)) (stateBits s) := by
  dsimp only [updateBlocks]
  apply Eq.symm
  apply List.foldl_hom stateBits
  intro acc j
  exact (stateBits_multiply h acc _).symm

theorem ghash_eq_foldl (h : Vector Bool 128) (xs : Array (Vector Bool 128)) :
    Standards.NIST.GCM.GHASH h xs = xs.toList.foldl
      (fun acc x ↦ Standards.NIST.GCM.mul (Standards.NIST.GCM.xor acc x) h)
      (Standards.NIST.GCM.zeros 128) := by
  rcases xs with ⟨xs⟩
  simp [Standards.NIST.GCM.GHASH]

end AesGcm.Proofs.Machine.Tag
