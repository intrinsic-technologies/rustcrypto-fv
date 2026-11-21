import X86Proofs.Program.ReadWrite.Bytes
import Prelude.Memory.Region

set_option autoImplicit false

namespace Hkdf.Proofs.Key.Tail

open Prelude X86 X86.Machine X86Proofs

theorem copy_qwords_hasBytes {s t : RamState} {src dst : BitVec 64} {bytes : ByteArray}
    (source : (⟨src.toNat, 64⟩ : MemoryRegion).HasBytes s.external bytes)
    (allocated : ∀ i < 64, (t.external[dst + BitVec.ofNat 64 i]?).isSome)
    (words : ∀ j < 8, memLoad t.external (dst + BitVec.ofNat 64 (8 * j)) 64 =
      memLoad s.external (src + BitVec.ofNat 64 (8 * j)) 64) :
    (⟨dst.toNat, 64⟩ : MemoryRegion).HasBytes t.external bytes := by
  have size : bytes.size = 64 := source.1
  have input (i : Nat) (hi : i < 64) :
      s.external[src + BitVec.ofNat 64 i]? = some (bytes[i]'(by omega)) := by
    have h := source.2 ⟨i, by omega⟩
    simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using h
  refine ⟨size, ?_⟩
  intro i
  have hi : i.val < 64 := by omega
  have out := Bytes.of_memLoad (n := 64) (a := dst + BitVec.ofNat 64 (8 * (i.val / 8)))
    (m := t.external) (by
      intro k hk
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact allocated _ (by omega))
  have inp := Bytes.of_memLoad (n := 64) (a := src + BitVec.ofNat 64 (8 * (i.val / 8)))
    (m := s.external) (by
      intro k hk
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, input _ (by omega)]
      trivial)
  have outByte := out (i.val % 8) (by omega)
  have inByte := inp (i.val % 8) (by omega)
  rw [words (i.val / 8) (by omega)] at outByte
  rw [BitVec.add_assoc, ← BitVec.ofNat_add,
    show 8 * (i.val / 8) + i.val % 8 = i.val by omega] at outByte inByte
  rw [← inByte, input _ hi] at outByte
  simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using outByte

end Hkdf.Proofs.Key.Tail
