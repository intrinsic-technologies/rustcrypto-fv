import P256.Proofs.Sec1.Affine.State
import P256.Proofs.ReadBe.Input

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Parse

open P256.Spec P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem input_limb_readable [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} (pre : AffineDecodePre s boundary bytes) (state : Frame s t)
    (off : Nat) (bound : off + 8 ≤ 65) :
    MemReadable t (s.regValue .rsi + BitVec.ofNat 64 off) 8 := by
  apply readable_of_grow (t := t) _ state.allocated
  apply memoryRegion_memReadable pre.inputBounded pre.inputAllocated
  all_goals
    have h : (s.regValue .rsi).toNat + 65 < 2^32 := pre.inputBounded
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : off < 2^64),
      Nat.mod_eq_of_lt (by omega)]
    simp only [registerRegion]
    omega

theorem coordinate_bytes {s : RamState} {address : BitVec 64} {bytes : ByteArray}
    (size : bytes.size = 65) (input : EncodedPointAt s address bytes)
    (off : Nat) (bound : off + 32 ≤ 65) :
    (MemoryRegion.mk (address + BitVec.ofNat 64 off).toNat 32).HasBytes s.external
      (bytes.extract off (off+32)) := by
  refine ⟨by change (bytes.extract off (off+32)).size = 32; simp only [ByteArray.size_extract, size]; omega, ?_⟩
  intro i
  have hi : i.val < 32 := by
    have := i.isLt
    simp only [ByteArray.size_extract, size] at this
    omega
  change s.external[BitVec.ofNat 64 ((address + BitVec.ofNat 64 off).toNat + i.val)]? = _
  rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
    BitVec.add_assoc, ← BitVec.ofNat_add, input.2 _ (by omega)]
  congr 1
  rw [Array.getElem?_eq_getElem (by change off + i.val < bytes.size; omega)]
  simp only [Option.getD_some]
  exact (ByteArray.getElem_extract _).symm

theorem coordinate_limb {s : RamState} {address : BitVec 64} {bytes : ByteArray}
    (size : bytes.size = 65) (input : EncodedPointAt s address bytes)
    (off : Nat) (bound : off + 32 ≤ 65) (j : Nat) (hj : j < 4) :
    P256.Proofs.Common.Instructions.bswap64
      (memLoad s.external (address + BitVec.ofNat 64 (off+8*j)) 64) =
      BitVec.ofNat 64
        (Standards.SECG.ECC.Encoding.octetsToNat (bytes.extract off (off+32)) / 2^(64*(3-j))) := by
  simpa only [Arith.uint, Arith.decodeBigEndian, BitVec.add_assoc, ← BitVec.ofNat_add] using
    ReadBe.bswap_input_memLoad_limb (coordinate_bytes size input off bound) j hj

end P256.Proofs.Sec1.Affine.Uncompressed.Parse
