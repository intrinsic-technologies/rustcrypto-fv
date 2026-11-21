import AesGcm.Proofs.Machine.Runtime.Contracts
import X86Proofs.Program.ReadWrite.Bytes

namespace AesGcm.Proofs.Machine.Runtime

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

def copyTagWords (mem : Ram) (dst src : BitVec 64) : Ram :=
  memStore (memStore mem (dst + 8) (memLoad mem (src + 8) 64)) dst (memLoad mem src 64)

theorem copyTagWords_hasBytes (mem : Ram) (dst src : BitVec 64) (tag : ByteArray)
    (hbytes : (span src 16).HasBytes mem tag) :
    (span dst 16).HasBytes (copyTagWords mem dst src) tag := by
  have hlen : tag.size = 16 := hbytes.1
  have hget (i : Nat) (hi : i < tag.size) :
      mem[src + BitVec.ofNat 64 i]? = some tag[i] := by
    simpa only [span, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using hbytes.2 ⟨i, hi⟩
  refine ⟨hlen, ?_⟩
  intro i
  change (copyTagWords mem dst src)[BitVec.ofNat 64 (dst.toNat + i.val)]? = some tag[i.val]
  simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hi16 : i.val < 16 := by have := i.isLt; omega
  by_cases hi8 : i.val < 8
  · unfold copyTagWords
    rw [memStore_getElem?_self _ _ _ (by decide) _ (by omega),
      storedByte_memLoad _ _ _ (by omega)]
    simp only [memByte, PhysicalMemory.read, hget i.val i.isLt, Option.getD_some]
  · have he : dst + BitVec.ofNat 64 i.val =
        (dst + 8) + BitVec.ofNat 64 (i.val - 8) := by
      change dst + BitVec.ofNat 64 i.val = (dst + BitVec.ofNat 64 8) + BitVec.ofNat 64 (i.val - 8)
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' (by omega)]
    unfold copyTagWords
    rw [memStore_getElem?_of_ne]
    · rw [he, memStore_getElem?_self _ _ _ (by decide) _ (by omega),
        storedByte_memLoad _ _ _ (by omega)]
      have hs : (src + 8) + BitVec.ofNat 64 (i.val - 8) = src + BitVec.ofNat 64 i.val := by
        change (src + BitVec.ofNat 64 8) + BitVec.ofNat 64 (i.val - 8) = _
        rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' (by omega)]
      rw [hs]
      simp only [memByte, PhysicalMemory.read, hget i.val i.isLt, Option.getD_some]
    · intro j hj hjEq
      have hb : BitVec.ofNat 64 j = BitVec.ofNat 64 i.val := by bv_omega
      have heq := congrArg BitVec.toNat hb
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : j < 2^64),
        Nat.mod_eq_of_lt (by omega : i.val < 2^64)] at heq
      change j < 8 at hj
      omega

theorem copyTagWords_frame (mem : Ram) (dst src : BitVec 64)
    (hbound : dst.toNat + 16 ≤ 2^64) :
    RamWriteFrame mem (copyTagWords mem dst src) [span dst 16] := by
  have h8 : (dst + 8).toNat = dst.toNat + 8 := by
    simp only [BitVec.toNat_add, BitVec.reduceToNat]
    exact Nat.mod_eq_of_lt (by omega)
  apply RamWriteFrame.memStore
  · apply RamWriteFrame.memStore (RamWriteFrame.refl _ _)
    refine ⟨span dst 16, by simp only [List.mem_singleton], ?_⟩
    change dst.toNat ≤ (dst + 8).toNat ∧
      (dst + 8).toNat + 8 ≤ dst.toNat + 16 ∧ (dst + 8).toNat + 8 ≤ 2^64
    rw [h8]
    omega
  · refine ⟨span dst 16, by simp only [List.mem_singleton], ?_⟩
    change dst.toNat ≤ dst.toNat ∧ dst.toNat + 8 ≤ dst.toNat + 16 ∧ dst.toNat + 8 ≤ 2^64
    omega

end AesGcm.Proofs.Machine.Runtime
