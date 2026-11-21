import K256.Proofs.Verify.Hash.Padding.Standard.Serialization
import K256.Proofs.Common.Refine.Lemma.Store
import X86Proofs.Program.ReadWrite.Bytes

namespace K256.Proofs.Verify.Hash

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.Refine

def storeDigestWords (m : Ram) (dst : BitVec 64) (hash : Array UInt32) : Nat → Ram
  | 0 => m
  | n + 1 => memStore (storeDigestWords m dst hash n) (wordAddr dst 32 n)
      (bswapSpec hash[n]!.toBitVec)

private theorem storeDigestWords_bytes (m : Ram) (dst : BitVec 64) (hash : Array UInt32)
    {n : Nat} (count : n ≤ hash.size) (low : 4 * n ≤ 2^64) :
    Bytes (storeDigestWords m dst hash n) dst (4 * n) (fun i => (serializeHash hash)[i]!) := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    have step := (ih (by omega) (by omega)).append_store (bswapSpec hash[n]!.toBitVec)
      (by decide) (by omega : 4*n + 32 / 8 ≤ 2^64)
    rw [show 4 * (n+1) = 4*n + 32/8 by omega]
    apply step
    intro i hi
    have index : 4*n+i < (serializeHash hash).size := by rw [serializeHash_size]; omega
    rw [getElem!_pos (serializeHash hash) (4*n+i) index, serializeHash_getElem, storedByte_bswapSpec _ hi]
    simp only [show (4*n+i)/4=n by omega, show (4*n+i)%4=i by omega, Nat.reduceDiv,
      Nat.reduceSub, storedByte, Nat.shiftRight_eq_div_pow, UInt32.toNat_toBitVec]
    rw [show 256 ^ (3-i) = 2 ^ (8*(3-i)) from Nat.pow_mul 2 8 (3-i) |>.symm]
    apply UInt8.toNat_inj.mp
    simp

theorem storeDigestWords_hasBytes (m : Ram) (dst : BitVec 64) {hash : Array UInt32}
    (size : hash.size = 8) :
    (⟨dst.toNat, 32⟩ : MemoryRegion).HasBytes (storeDigestWords m dst hash 8)
      (serializeHash hash) := by
  refine ⟨by rw [serializeHash_size, size]; rfl, fun i => ?_⟩
  have hi : i.val < 32 := by simpa only [serializeHash_size, size] using i.isLt
  have hb := storeDigestWords_bytes m dst hash (n := 8) (by omega) (by decide) i.val hi
  simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
    getElem!_pos (serializeHash hash) i.val i.isLt] using hb

theorem storeDigestWords_frame {m : Ram} {dst : BitVec 64} {hash : Array UInt32}
    {regions : List MemoryRegion} {n : Nat}
    (within : ∀ i < n, InRegions regions (wordAddr dst 32 i) 4) :
    RamWriteFrame m (storeDigestWords m dst hash n) regions := by
  induction n with
  | zero => exact .refl _ _
  | succ n ih => exact (ih fun i hi => within i (by omega)).memStore _ (within n (by omega))

end K256.Proofs.Verify.Hash
