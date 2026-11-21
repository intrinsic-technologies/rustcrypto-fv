import Sha1.Proofs.Common.Reads
import Sha1.Proofs.Common.OutputFrame
import X86Proofs.Program.ReadWrite.Bytes

namespace Sha1.Proofs.Compress

open Prelude X86 X86.Machine X86Proofs Sha1.Proofs.Refine Sha1.Spec Sha1.Spec.Program

theorem stateBytes_byte (H : Vector (BitVec 32) 5) (i : Fin 20) :
    (Sha1.Spec.Hasher.stateBytes H)[i] =
      storedByte (H[i.val / 4]'(by omega)) (i.val % 4) := by
  apply UInt8.eq_of_toBitVec_eq
  apply BitVec.eq_of_toNat_eq
  simp [Sha1.Spec.Hasher.stateBytes, storedByte_eq_extract,
    BitVec.toNat_setWidth, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

theorem stateBytes_words {m : Ram} {base : BitVec 64}
    {H : Vector (BitVec 32) 5}
    (hbytes : (⟨base.toNat, 20⟩ : MemoryRegion).HasBytes m
      ⟨(Sha1.Spec.Hasher.stateBytes H).toArray⟩) :
    ∀ i : Fin 5, memLoad m (base + BitVec.ofNat 64 (4 * i.val)) 32 = H[i] := by
  have hlen : (⟨(Sha1.Spec.Hasher.stateBytes H).toArray⟩ : ByteArray).size = 20 := by
    change (Sha1.Spec.Hasher.stateBytes H).toArray.size = 20
    exact Vector.size_toArray _
  intro i
  have hb : Bytes m (base + BitVec.ofNat 64 (4 * i.val)) 4 (storedByte H[i]) := by
    intro j hj
    have hk : 4 * i.val + j < 20 := by omega
    have hmem := hbytes.2 ⟨4 * i.val + j, by rw [hlen]; exact hk⟩
    have haddr : BitVec.ofNat 64 (base.toNat + (4 * i.val + j)) =
        (base + BitVec.ofNat 64 (4 * i.val)) + BitVec.ofNat 64 j := by
      rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
        BitVec.ofNat_add, BitVec.add_assoc]
    rw [haddr] at hmem
    have hv : (⟨(Sha1.Spec.Hasher.stateBytes H).toArray⟩ : ByteArray)[4 * i.val + j]'(by
        rw [hlen]
        exact hk) = storedByte H[i] j := by
      have he := stateBytes_byte H ⟨4 * i.val + j, hk⟩
      have hdiv : (4 * i.val + j) / 4 = i.val := by omega
      have hmod : (4 * i.val + j) % 4 = j := by omega
      simpa only [ByteArray.getElem_eq_getElem_data, Vector.getElem_toArray,
        Fin.getElem_fin, hdiv, hmod] using he
    exact hmem.trans (congrArg some hv)
  exact Bytes.memLoad hb (by decide) (by decide)

set_option maxHeartbeats 1000000 in
theorem stateBytes_of_words {m : Ram} {base : BitVec 64}
    {H : Vector (BitVec 32) 5}
    (hwords : ∀ i : Fin 5,
      memLoad m (base + BitVec.ofNat 64 (4 * i.val)) 32 = H[i])
    (halloc : ∀ i < 20, (m[base + BitVec.ofNat 64 i]?).isSome) :
    (⟨base.toNat, 20⟩ : MemoryRegion).HasBytes m
      ⟨(Sha1.Spec.Hasher.stateBytes H).toArray⟩ := by
  constructor
  · change (Sha1.Spec.Hasher.stateBytes H).toArray.size = 20
    rw [Vector.size_toArray]
  · intro i
    have hi := i.isLt
    have hiVec : i.val < (Sha1.Spec.Hasher.stateBytes H).toArray.size := by
      change i.val < (Sha1.Spec.Hasher.stateBytes H).toArray.size at hi
      exact hi
    have hi20 : i.val < 20 := by
      rw [Vector.size_toArray] at hiVec
      exact hiVec
    let w := i.val / 4
    let b := i.val % 4
    have hw : w < 5 := by dsimp [w]; omega
    have hb : b < 4 := by dsimp [b]; omega
    have hlocalAlloc : ∀ j < 32 / 8,
        (m[(base + BitVec.ofNat 64 (4 * w)) + BitVec.ofNat 64 j]?).isSome := by
      intro j hj
      have hj20 : 4 * w + j < 20 := by dsimp [w]; omega
      have haddr : (base + BitVec.ofNat 64 (4 * w)) + BitVec.ofNat 64 j =
          base + BitVec.ofNat 64 (4 * w + j) := by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      rw [haddr]
      exact halloc (4 * w + j) hj20
    have hloaded := Bytes.of_memLoad (m := m)
      (a := base + BitVec.ofNat 64 (4 * w)) (n := 32) hlocalAlloc
    have hword := hwords ⟨w, hw⟩
    change memLoad m (base + BitVec.ofNat 64 (4 * w)) 32 = H[w] at hword
    have hlocal := hloaded b (by dsimp [b]; omega)
    have haddr : (base + BitVec.ofNat 64 (4 * w)) + BitVec.ofNat 64 b =
        BitVec.ofNat 64 (base.toNat + i.val) := by
      calc
        _ = base + BitVec.ofNat 64 (4 * w + b) := by
          rw [BitVec.add_assoc, ← BitVec.ofNat_add]
        _ = base + BitVec.ofNat 64 i.val := by congr 2; dsimp [w, b]; omega
        _ = _ := by rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    let fi : Fin 20 := ⟨i.val, hi20⟩
    have hbyte : storedByte H[w] b = (Sha1.Spec.Hasher.stateBytes H)[fi] := by
      have he := stateBytes_byte H fi
      change storedByte H[w] b = _
      simpa only [w, b] using he.symm
    have hresult : m[BitVec.ofNat 64 (base.toNat + i.val)]? =
        some ((Sha1.Spec.Hasher.stateBytes H)[fi]) := by
      rw [← haddr, hlocal, hword, hbyte]
    simpa only [fi, ByteArray.getElem_eq_getElem_data, Vector.getElem_toArray,
      Fin.getElem_fin] using hresult


theorem stateBytes_hasBytes_iff {m : Ram} {base : BitVec 64}
    {H : Vector (BitVec 32) 5} :
    (MemoryRegion.mk base.toNat 20).HasBytes m (ByteArray.mk (Hasher.stateBytes H).toArray) ↔
      (∀ i < 20, (m[base + BitVec.ofNat 64 i]?).isSome) ∧
      (∀ i : Fin 5, memLoad m (base + BitVec.ofNat 64 (4 * i.val)) 32 = H[i]) := by
  constructor
  · intro h
    refine ⟨?_, stateBytes_words h⟩
    intro i hi
    have hsize : (ByteArray.mk (Hasher.stateBytes H).toArray).size = 20 :=
      Vector.size_toArray _
    have hb := h.2 ⟨i, by rw [hsize]; exact hi⟩
    rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hb
    rw [hb]
    rfl
  · rintro ⟨ha, hw⟩
    exact stateBytes_of_words hw ha

theorem readOutput_of_words {initial final : RamState} {H : Vector (BitVec 32) 5}
    (halloc : ∀ i < 20, (final.external[initial.regValue .rdi + BitVec.ofNat 64 i]?).isSome)
    (hwords : ∀ i : Fin 5,
      memLoad final.external (initial.regValue .rdi + BitVec.ofNat 64 (4 * i.val)) 32 = H[i]) :
    Sha1.Spec.Program.Compress.readOutput initial final = .ok (Hasher.stateBytes H) := by
  exact Common.compress_readOutput_of_hasBytes (stateBytes_of_words hwords halloc)

theorem allocated_of_hasBytes {m : Ram} {region : MemoryRegion} {bytes : ByteArray}
    (h : region.HasBytes m bytes) : region.Allocated m := by
  intro a ha
  have hi : a.toNat - region.start < bytes.size := by
    have hlen : bytes.size = region.size := h.1
    have hc : region.start ≤ a.toNat ∧ a.toNat < region.start + region.size := ha
    omega
  have hb := h.2 ⟨a.toNat - region.start, hi⟩
  have he : region.start + (a.toNat - region.start) = a.toNat := by
    exact Nat.add_sub_of_le ha.1
  rw [he, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hb
  exact ⟨_, hb⟩

theorem outputFrame_of_validCall {bindings : Bindings} {initial : RamState}
    {H : Vector (BitVec 32) 5} {blocks : ByteArray}
    (h : Sha1.Spec.Program.Compress.ValidCall bindings initial H blocks) :
    Common.OutputFrameContract Extracted.programImage initial.external
      (Sha1.Spec.Program.Compress.outputRegion initial)
      (Stack.region initial Sha1.Spec.Program.Compress.minStackBytes) := by
  exact Common.OutputFrameContract.of_valid
    ⟨h.outputInMemory.1, h.outputInMemory.2.1, allocated_of_hasBytes h.outputInMemory.2.2⟩
    h.stackAvailable h.separation

end Sha1.Proofs.Compress
