import K256.Proofs.Common.WordCopy
import K256.Proofs.Ecdh.Wrapper.Frame

namespace K256.Proofs.Ecdh.Output

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.Lift K256.Proofs.Refine Ecdh.Wrapper

theorem localAddr (s : RamState) {i : Nat} (hi : i ≤ 6152) :
    localSp s + BitVec.ofNat 64 i = s.regValue .rsp - BitVec.ofNat 64 (6152 - i) := by
  have h : BitVec.ofNat 64 (6152 - i) + BitVec.ofNat 64 i = 6152 := by
    rw [← BitVec.ofNat_add, Nat.sub_add_cancel hi]
    rfl
  dsimp only [localSp]
  rw [← h, ← BitVec.sub_sub, BitVec.sub_add_cancel]

theorem outputStackApart {s : RamState} {secret peer : ByteArray}
    (call : ValidCall ecdhDiffieHellman s [secret, peer]) :
    (s.regValue .rdi).toNat + 32 ≤ (s.regValue .rsp).toNat - 10088 ∨
      (s.regValue .rsp).toNat + 8 ≤ (s.regValue .rdi).toNat := by
  have sep : (outputRegion ecdhDiffieHellman s).Disjoint
      (Stack.region s ecdhDiffieHellman.minStackBytes) :=
    (List.pairwise_cons.mp call.separation.1).1 _ List.mem_cons_self
  have pos : 0 < (Stack.region s ecdhDiffieHellman.minStackBytes).size := by
    change 0 < (s.regValue .rsp).toNat + 8 - ((s.regValue .rsp).toNat - 10088)
    omega
  have bounds := apart_of_disjoint sep (by decide : 0 < 32) pos
  change (s.regValue .rdi).toNat + 32 ≤ (s.regValue .rsp).toNat - 10088 ∨
    (s.regValue .rsp).toNat - 10088 + ((s.regValue .rsp).toNat + 8 -
      ((s.regValue .rsp).toNat - 10088)) ≤ (s.regValue .rdi).toNat at bounds
  omega

theorem outputOffset {dst : BitVec 64} (low : dst.toNat + 32 ≤ 2^32)
    {i : Nat} (hi : i ≤ 32) : (dst + BitVec.ofNat 64 i).toNat = dst.toNat + i := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := i) (by omega),
    Nat.mod_eq_of_lt (by omega)]

theorem wordStoreRead {dst : BitVec 64} (low : dst.toNat + 32 ≤ 2^32)
    (m : Ram) (x : BitVec 64) (i j : Nat) (hi : i + 8 ≤ 32) (hj : j + 8 ≤ 32)
    (sep : i + 8 ≤ j ∨ j + 8 ≤ i) :
    memLoad (memStore m (dst + BitVec.ofNat 64 j) x) (dst + BitVec.ofNat 64 i) 64 =
      memLoad m (dst + BitVec.ofNat 64 i) 64 := by
  apply memLoad_memStore_of_rangeApart
  apply RangeApart.of_toNat
  · rw [outputOffset low (by omega)]
    change dst.toNat + j + 8 ≤ 2^64
    omega
  · rw [outputOffset low (by omega)]
    change dst.toNat + i + 8 ≤ 2^64
    omega
  · rw [outputOffset low (by omega), outputOffset low (by omega)]
    change dst.toNat + j + 8 ≤ dst.toNat + i ∨ dst.toNat + i + 8 ≤ dst.toNat + j
    omega

def copyMemory (m : Ram) (sp dst : BitVec 64) : Ram :=
  let m1 := memStore m (dst + BitVec.ofNat 64 24) (memLoad m (sp + 368) 64)
  let m2 := memStore m1 (dst + BitVec.ofNat 64 16) (memLoad m (sp + 360) 64)
  let m3 := memStore m2 (dst + BitVec.ofNat 64 8) (memLoad m (sp + 352) 64)
  memStore m3 (dst + BitVec.ofNat 64 0) (memLoad m (sp + 344) 64)

def clearMemory (m : Ram) (sp : BitVec 64) : Nat → Ram
  | 0 => m
  | i + 1 => memStore (clearMemory m sp i) (sp + BitVec.ofNat 64 (344 + i)) (0 : BitVec 8)

set_option maxHeartbeats 600000 in
theorem copyHasBytes {m : Ram} {sp dst : BitVec 64} {bytes : ByteArray}
    (serialized : (⟨(sp + 344).toNat, 32⟩ : MemoryRegion).HasBytes m bytes)
    (readable : Readable m dst 32) :
    (⟨dst.toNat, 32⟩ : MemoryRegion).HasBytes (copyMemory m sp dst) bytes := by
  have hs : bytes.size = 32 := serialized.1
  rw [← hs]
  apply Common.hasBytes_of_word_copy (n := 4) serialized hs
  · unfold copyMemory
    exact (((readable.memStore _ _).memStore _ _).memStore _ _).memStore _ _
  · have copied (i : Nat) (hi : i < 4) : memLoad (copyMemory m sp dst)
        (dst + BitVec.ofNat 64 (8 * i)) 64 =
        memLoad m (sp + BitVec.ofNat 64 (344 + 8 * i)) 64 := by
      have h24 := wordStoreRead readable.low
      have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases cases with rfl | rfl | rfl | rfl <;> simp only [copyMemory, Nat.mul_zero, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd]
      · exact memLoad_memStore_same _ _ _ (by decide) (by decide)
      · rw [h24 _ _ 8 0 (by decide) (by decide) (by decide)]
        exact memLoad_memStore_same _ _ _ (by decide) (by decide)
      · rw [h24 _ _ 16 0 (by decide) (by decide) (by decide),
          h24 _ _ 16 8 (by decide) (by decide) (by decide)]
        exact memLoad_memStore_same _ _ _ (by decide) (by decide)
      · rw [h24 _ _ 24 0 (by decide) (by decide) (by decide),
          h24 _ _ 24 8 (by decide) (by decide) (by decide),
          h24 _ _ 24 16 (by decide) (by decide) (by decide)]
        exact memLoad_memStore_same _ _ _ (by decide) (by decide)
    intro i hi
    simp only [wordAddr, Nat.reduceDiv, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rw [BitVec.add_assoc]
    change memLoad _ _ _ = memLoad m (sp + (BitVec.ofNat 64 344 + BitVec.ofNat 64 (8 * i))) 64
    rw [← BitVec.ofNat_add]
    exact copied i hi

end K256.Proofs.Ecdh.Output
