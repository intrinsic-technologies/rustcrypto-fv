import P256.Proofs.ReadBe.Interface
import P256.Proofs.SecretKeyFromBytes.Encoding
import P256.Proofs.Common.Instructions.Bswap
import X86Proofs.Program.ReadWrite.Bytes

set_option autoImplicit false

namespace P256.Proofs.ReadBe

open P256.Spec Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.SecretKeyFromBytes.Encoding

theorem storedByte_ofNat64 (x i : Nat) (hi : i < 8) :
    storedByte (BitVec.ofNat 64 x) i = UInt8.ofNat (x / 256^i % 256) := by
  apply UInt8.toNat.inj
  simp only [storedByte, UInt8.toNat_ofNat', BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

theorem input_memLoad_limb {s : RamState} {address : BitVec 64} {input : ByteArray}
    (hinput : (MemoryRegion.mk address.toNat 32).HasBytes s.external input)
    (j : Nat) (hj : j < 4) :
    memLoad s.external (address + BitVec.ofNat 64 (8*j)) 64 =
      P256.Proofs.Common.Instructions.bswap64 (BitVec.ofNat 64 (Arith.uint input / 2^(64*(3-j)))) := by
  have hsize : input.size = 32 := hinput.1
  apply Bytes.memLoad (n := 64) _ (by decide) (by decide)
  intro i hi
  have hib : 8*j+i < input.size := by omega
  have hb := hinput.2 ⟨8*j+i, hib⟩
  change s.external[BitVec.ofNat 64 (address.toNat+(8*j+i))]? =
    some input.data[8*j+i] at hb
  rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hb
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, hb]
  congr 1
  rw [octetsToNat_byte input _ hib, hsize, storedByte_eq_extract,
    P256.Proofs.Common.Instructions.bswap64_byte _ i hi, ← storedByte_eq_extract,
    storedByte_ofNat64 _ (7-i) (by omega), Nat.div_div_eq_div_mul]
  have he : 256^(32-1-(8*j+i)) = 2^(64*(3-j))*256^(7-i) := by
    rw [show 32-1-(8*j+i) = 8*(3-j)+(7-i) by omega, Nat.pow_add]
    congr 1
    rw [show (256:Nat)=2^8 by decide +kernel, ← Nat.pow_mul]
    congr 1
    omega
  rw [he]
  rfl

theorem bswap_input_memLoad_limb {s : RamState} {address : BitVec 64} {input : ByteArray}
    (bytes : (MemoryRegion.mk address.toNat 32).HasBytes s.external input)
    (j : Nat) (hj : j < 4) :
    P256.Proofs.Common.Instructions.bswap64
      (memLoad s.external (address + BitVec.ofNat 64 (8*j)) 64) =
      BitVec.ofNat 64 (Arith.uint input / 2^(64*(3-j))) := by
  rw [input_memLoad_limb bytes j hj, P256.Proofs.Common.Instructions.bswap64_bswap64]

end P256.Proofs.ReadBe
