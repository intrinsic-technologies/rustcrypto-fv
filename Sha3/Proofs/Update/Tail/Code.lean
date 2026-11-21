import Sha3.Proofs.Update.Tail.Bytes
import Sha3.Proofs.Update.Tail.Chunks
import Sha3.Proofs.Update.Layout
import Sha3.Proofs.Permutation.Code

namespace Sha3.Proofs.Update.Tail

open X86 X86.Machine X86.UserProcess X86Proofs Sha3.Spec.Program

def chunkAddress : Variant → BitVec 64
  | .sha224 => 0x100ac0 | .sha256 => 0x1007a0
  | .sha384 => 0x100480 | .sha512 => 0x1001b0

def byteAddress (v : Variant) : BitVec 64 := chunkAddress v + 80

theorem chunkBytes_image (v : Variant) :
    Extracted.textBytes.toListFrom ((chunkAddress v).toNat - 0x100000) 51 = chunkBytes := by
  cases v <;> decide +kernel

theorem tailBytes_image (v : Variant) :
    Extracted.textBytes.toListFrom ((byteAddress v).toNat - 0x100000) 16 = tailBytes := by
  cases v <;> decide +kernel

theorem chunk_subset (v : Variant) :
    ∀ byte ∈ codeRange (chunkAddress v) chunkBytes, byte ∈ Extracted.programImage := by
  have h := textSlice_subset_programImage
    (show (chunkAddress v).toNat - 0x100000 + 51 ≤ Extracted.textBytes.size by
      cases v <;> decide +kernel) (chunkBytes_image v)
  have he : Extracted.textAddress + BitVec.ofNat 64 ((chunkAddress v).toNat - 0x100000) =
      chunkAddress v := by cases v <;> rfl
  rwa [he] at h

theorem tail_subset (v : Variant) :
    ∀ byte ∈ codeRange (byteAddress v) tailBytes, byte ∈ Extracted.programImage := by
  have h := textSlice_subset_programImage
    (show (byteAddress v).toNat - 0x100000 + 16 ≤ Extracted.textBytes.size by
      cases v <;> decide +kernel) (tailBytes_image v)
  have he : Extracted.textAddress + BitVec.ofNat 64 ((byteAddress v).toNat - 0x100000) =
      byteAddress v := by cases v <;> rfl
  rwa [he] at h

theorem chunk_ne_boundary (v : Variant) (boundary : ReturnBoundary)
    (hb : ¬ InProgram boundary.rip) (i : Nat) (hi : i ≤ 51) :
    chunkAddress v + BitVec.ofNat 64 i ≠ boundary.rip := by
  apply Permutation.permutation_address_ne_boundary hb
  all_goals cases v <;> simp only [chunkAddress, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat]
    <;> omega

theorem byte_ne_boundary (v : Variant) (boundary : ReturnBoundary)
    (hb : ¬ InProgram boundary.rip) (i : Nat) (hi : i ≤ 16) :
    byteAddress v + BitVec.ofNat 64 i ≠ boundary.rip := by
  apply Permutation.permutation_address_ne_boundary hb
  all_goals cases v <;> simp only [byteAddress, chunkAddress, BitVec.toNat_add,
    BitVec.toNat_ofNat, BitVec.reduceToNat] <;> omega

end Sha3.Proofs.Update.Tail
