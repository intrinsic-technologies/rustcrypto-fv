import Hkdf.Proofs.Key.Entry.Zero
import X86Proofs.Program.ReadWrite.Bytes
import Prelude.Memory.Region

set_option autoImplicit false

namespace Hkdf.Proofs.Key.Entry.Zero

open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem words {s t : RamState} (h : (effect s).Holds s t) :
    ∀ j < 8, memLoad t.external (rspOf s + BitVec.ofNat 64 (8*j)) 64 = 0 := by
  have stores := h.writes
  simp only [effect, Write.AllHold, Operand.read, rspOf] at stores
  intro j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨
      j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero, rspOf,
      Operand.read, BitVec.setWidth_eq] using stores.2.2.2.2.2.2.2
  · exact stores.2.2.2.2.2.2.1
  · exact stores.2.2.2.2.2.1
  · exact stores.2.2.2.2.1
  · exact stores.2.2.2.1
  · exact stores.2.2.1
  · exact stores.2.1
  · exact stores.1

theorem bytes_zero {s t : RamState} (h : (effect s).Holds s t)
    (read : MemReadable t (rspOf s) 64) :
    Bytes t.external (rspOf s) 64 (fun _ => 0) := by
  intro i hi
  have chunk := Bytes.of_memLoad (n := 64) (m := t.external)
    (a := rspOf s + BitVec.ofNat 64 (8*(i/8))) (by
      intro j hj
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact read.mem _ (by omega))
  rw [words h (i/8) (by omega)] at chunk
  have byte := chunk (i%8) (by omega)
  rw [BitVec.add_assoc, ← BitVec.ofNat_add,
    show 8*(i/8) + i%8 = i by omega] at byte
  simpa [storedByte] using byte

theorem hasBytes {s t : RamState} (h : (effect s).Holds s t)
    (read : MemReadable t (rspOf s) 64) :
    (⟨(rspOf s).toNat, 64⟩ : MemoryRegion).HasBytes t.external
      ⟨Array.replicate 64 0⟩ := by
  refine ⟨rfl, ?_⟩
  intro i
  have hi : i.val < 64 := by simpa only [ByteArray.size, Array.size_replicate] using i.isLt
  have byte := bytes_zero h read i.val hi
  change t.external[BitVec.ofNat 64 ((rspOf s).toNat + i.val)]? =
    some ((Array.replicate 64 (0 : UInt8))[i.val])
  rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  exact byte.trans (congrArg some (Array.getElem_replicate
    (n := 64) (v := (0 : UInt8)) (i := i.val) (by
      simpa only [Array.size_replicate] using hi)).symm)

end Hkdf.Proofs.Key.Entry.Zero
