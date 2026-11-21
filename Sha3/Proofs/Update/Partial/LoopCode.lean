import Sha3.Proofs.Update.Partial.Chunk
import Sha3.Proofs.Update.Partial.ByteLoop
import Sha3.Proofs.Update.Partial.ShortControl

namespace Sha3.Proofs.Update.Partial

open X86 X86.Machine X86.UserProcess X86Proofs Sha3.Spec.Program

def chunkAddress (k : ByteLoopKind) (v : Variant) : BitVec 64 :=
  match k with
  | .fill => v.updateAddress + 0x80
  | .short => Short.chunkPC v

theorem chunkBytes_image (k : ByteLoopKind) (v : Variant) :
    Extracted.textBytes.toListFrom ((chunkAddress k v).toNat - 0x100000) 51 = chunkBytes := by
  cases k <;> cases v <;> decide +kernel

theorem chunk_subset (k : ByteLoopKind) (v : Variant) :
    ∀ byte ∈ codeRange (chunkAddress k v) chunkBytes, byte ∈ Extracted.programImage := by
  have h := textSlice_subset_programImage
    (show (chunkAddress k v).toNat - 0x100000 + 51 ≤ Extracted.textBytes.size by
      cases k <;> cases v <;> decide +kernel) (chunkBytes_image k v)
  have he : Extracted.textAddress + BitVec.ofNat 64 ((chunkAddress k v).toNat - 0x100000) =
      chunkAddress k v := by cases k <;> cases v <;> rfl
  rwa [he] at h

theorem chunk_ne_boundary (k : ByteLoopKind) (v : Variant) (boundary : ReturnBoundary)
    (hb : ¬ InProgram boundary.rip) (i : Nat) (hi : i ≤ 51) :
    chunkAddress k v + BitVec.ofNat 64 i ≠ boundary.rip := by
  apply Permutation.permutation_address_ne_boundary hb
  all_goals cases k <;> cases v <;> simp only [chunkAddress, Short.chunkPC,
    Short.chunkSetupPC, Variant.updateAddress, BitVec.toNat_add, BitVec.toNat_ofNat,
    BitVec.reduceToNat] <;> omega

theorem byte_ne_boundary (k : ByteLoopKind) (v : Variant) (boundary : ReturnBoundary)
    (hb : ¬ InProgram boundary.rip) (i : Nat) (hi : i ≤ 17) :
    byteLoopAddress k v + BitVec.ofNat 64 i ≠ boundary.rip := by
  apply Permutation.permutation_address_ne_boundary hb
  all_goals cases k <;> cases v <;> simp only [byteLoopAddress,
    Variant.updateAddress, BitVec.toNat_add, BitVec.toNat_ofNat,
    BitVec.reduceToNat] <;> omega

end Sha3.Proofs.Update.Partial
