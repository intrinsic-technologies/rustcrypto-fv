import K256.Proofs.Verify.Core.Serializer.Memory

namespace K256.Proofs.Verify.Core.Serializer

open Prelude X86.Machine X86Proofs K256.Proofs.Refine

def prefixStore (m : Ram) (dst : BitVec 64) (w : Vector (BitVec 64) 4) : Nat → Ram
  | 0 => m
  | n + 1 => memStore (prefixStore m dst w n) (dst + BitVec.ofNat 64 n)
      (w[n / 8 % 4].extractLsb' (n % 8 * 8) 8)

theorem prefix_frame {m : Ram} {dst : BitVec 64} {w : Vector (BitVec 64) 4}
    (low : dst.toNat + 32 ≤ 2 ^ 64) {n : Nat} (fits : n ≤ 32) :
    RamWriteFrame m (prefixStore m dst w n) [⟨dst.toNat, 32⟩] := by
  induction n with
  | zero => exact .refl _ _
  | succ n ih =>
    apply (ih (by omega)).memStore
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    have addr : (dst + BitVec.ofNat 64 n).toNat = dst.toNat + n := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := n) (by omega),
        Nat.mod_eq_of_lt (by omega)]
    unfold InRegion
    rw [addr]
    simp only [Nat.reduceDiv]
    omega

end K256.Proofs.Verify.Core.Serializer
