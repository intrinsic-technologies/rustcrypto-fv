import Sha1.Proofs.Compress.StateMemory
import X86Proofs.Program.Compose
import Sha1.Proofs.Common.Refine

namespace Sha1.Proofs.Compress

open Prelude X86 X86.Machine X86Proofs Sha1.Proofs.Refine Sha1.Spec

def stateMemory (mem : Ram) (out : BitVec 64) (H : Vector (BitVec 32) 5) : Ram :=
  memStore (memStore (memStore (memStore (memStore mem
    (out + 4) H[1]) (out + 8) H[2]) (out + 12) H[3]) (out + 16) H[4]) out H[0]

theorem stateMemory_words (mem : Ram) (out : BitVec 64) (H : Vector (BitVec 32) 5) :
    ∀ i : Fin 5, memLoad (stateMemory mem out H) (out + BitVec.ofNat 64 (4 * i.val)) 32 = H[i] := by
  intro ⟨i, hi⟩
  have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl
  all_goals
    simp (disch := (first | decide +kernel | (unfold OffsetsApart; decide +kernel))) only [stateMemory, Nat.reduceMul,
      Fin.getElem_fin, BitVec.add_zero, memLoad_memStore_apart,
      memLoad_memStore_apart_left,
      memLoad_memStore_same]
  all_goals exact memLoad_memStore _ _ (by decide) (by decide) _

theorem stateMemory_hasBytes (mem : Ram) (out : BitVec 64) (H : Vector (BitVec 32) 5)
    (halloc : ∀ i < 20, (mem[out + BitVec.ofNat 64 i]?).isSome) :
    (MemoryRegion.mk out.toNat 20).HasBytes (stateMemory mem out H)
      (ByteArray.mk (Hasher.stateBytes H).toArray) := by
  apply stateBytes_of_words (stateMemory_words mem out H)
  intro i hi
  unfold stateMemory
  repeat apply memStore_isSome
  exact halloc i hi

theorem stateMemory_readOutput {initial final : RamState} {mem : Ram}
    {H : Vector (BitVec 32) 5}
    (halloc : ∀ i < 20, (mem[initial.regValue .rdi + BitVec.ofNat 64 i]?).isSome)
    (hfinal : final.external = stateMemory mem (initial.regValue .rdi) H) :
    Sha1.Spec.Program.Compress.readOutput initial final = .ok (Hasher.stateBytes H) := by
  apply Common.compress_readOutput_of_hasBytes
  rw [hfinal]
  exact stateMemory_hasBytes mem _ H halloc

theorem stateMemory_frame (mem : Ram) (out : BitVec 64) (H : Vector (BitVec 32) 5)
    (hbound : out.toNat + 20 ≤ 2 ^ 64) :
    RamWriteFrame mem (stateMemory mem out H) [MemoryRegion.mk out.toNat 20] := by
  have hin (off : Nat) (hoff : off + 4 ≤ 20) :
      InRegions [MemoryRegion.mk out.toNat 20] (out + BitVec.ofNat 64 off) 4 := by
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    have ho : off < 2 ^ 64 := by omega
    have ha : out.toNat + off < 2 ^ 64 := by omega
    simp only [InRegion, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt ho, Nat.mod_eq_of_lt ha]
    exact ⟨by omega, by omega, by omega⟩
  have hz : InRegions [MemoryRegion.mk out.toNat 20] out 4 := by
    simpa only [BitVec.reduceOfNat, BitVec.add_zero] using hin 0 (by omega)
  exact (((((RamWriteFrame.refl mem _).memStore H[1] (hin 4 (by omega))).memStore
    H[2] (hin 8 (by omega))).memStore H[3] (hin 12 (by omega))).memStore
    H[4] (hin 16 (by omega))).memStore H[0] hz

end Sha1.Proofs.Compress
