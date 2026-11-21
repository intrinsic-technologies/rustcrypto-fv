import K256.Proofs.Common.Encoding
import K256.Proofs.Common.Refine.Lemma.Region
import X86Proofs.Instructions.Bswap.Operation

namespace K256.Proofs.Generate.Wrapper

open Prelude X86.Machine X86Proofs K256.Proofs.Refine Standards.SECG.ECC

private theorem storedByte_bswap (w : BitVec 64) (k : Nat) (hk : k < 8) :
    storedByte (bswapSpec w) k = storedByte w (7 - k) := by
  simp only [storedByte_eq_extract, Nat.mul_comm 8]
  change UInt8.ofBitVec (lane 8 (bswapSpec w) k) = UInt8.ofBitVec (lane 8 w (7 - k))
  rw [bswapSpec, lane_ofLanes (n := 64) _ _ hk]

private theorem div_mod_word (d l k : Nat) (hk : k < 8) :
    ((d / 2 ^ (64 * l)) % 2 ^ 64) / 2 ^ (8 * k) % 256 =
      d / 256 ^ (8 * l + k) % 256 := by
  rw [show 2 ^ (64 : Nat) = 2 ^ (8 * k) * 2 ^ (64 - 8 * k) by
    rw [← Nat.pow_add, show 8 * k + (64 - 8 * k) = 64 by omega],
    Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd]
  · rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
    have power : 256 ^ (8 * l + k) = 2 ^ (8 * (8 * l + k)) := by
      rw [Nat.pow_mul]
    rw [power, show 64 * l + 8 * k = 8 * (8 * l + k) by omega]
  · change 2 ^ (8 : Nat) ∣ _
    exact Nat.pow_dvd_pow 2 (by omega)

theorem scalarOctets {mem : Ram} {p : BitVec 64} {d : Nat}
    (hw : WordsAt mem p 64 (Vector.ofFn fun i : Fin 4 =>
      bswapSpec (BitVec.ofNat 64 (d / 2 ^ (64 * (3 - i.val))))))
    (hr : Readable mem p 32) :
    (⟨p.toNat, 32⟩ : MemoryRegion).HasBytes mem (Encoding.natToOctets 32 d) := by
  have sz := Common.Encoding.natToOctets_size 32 d
  suffices h : (⟨p.toNat, (Encoding.natToOctets 32 d).size⟩ : MemoryRegion).HasBytes mem
    (Encoding.natToOctets 32 d) by simpa only [sz] using h
  refine hw.hasBytes hr sz ?_
  intro j hj hword
  have jlt : j < 32 := by rwa [sz] at hj
  rw [Vector.getElem_ofFn, storedByte_bswap _ _ (Nat.mod_lt _ (by decide))]
  change (Encoding.natToOctets 32 d).data[j] = _
  rw [Common.Encoding.natToOctets_getElem _ _ _ jlt]
  apply UInt8.toNat_inj.mp
  simp only [storedByte, UInt8.toNat_ofNat', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_mod]
  rw [div_mod_word _ _ _ (by omega)]
  congr 3
  omega

end K256.Proofs.Generate.Wrapper
