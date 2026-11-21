import Hkdf.Proofs.Wrapper.Absorb.Mathematics
import Hkdf.Proofs.Program

set_option autoImplicit false

namespace Hkdf.Proofs.Wrapper.Absorb

open Prelude X86 X86.Machine

theorem hasBytes_append {memory : Ram} {address : BitVec 64} {a b : ByteArray}
    (front : (⟨address.toNat,a.size⟩ : MemoryRegion).HasBytes memory a)
    (back : (⟨(address+BitVec.ofNat 64 a.size).toNat,b.size⟩ : MemoryRegion).HasBytes memory b) :
    (⟨address.toNat,(a++b).size⟩ : MemoryRegion).HasBytes memory (a++b) := by
  refine ⟨rfl,fun i => ?_⟩
  by_cases hi : i.val < a.size
  · have byte := front.2 ⟨i.val,hi⟩
    simpa only [ByteArray.getElem_append_left hi] using byte
  · have hj : i.val-a.size < b.size := by
      have h : i.val < a.size+b.size := by simpa only [ByteArray.size_append] using i.isLt
      omega
    have byte := back.2 ⟨i.val-a.size,hj⟩
    change memory[BitVec.ofNat 64 ((address+BitVec.ofNat 64 a.size).toNat+(i.val-a.size))]? = _ at byte
    rw [BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq,BitVec.add_assoc,
      ← BitVec.ofNat_add,Nat.add_sub_of_le (by omega : a.size ≤ i.val)] at byte
    simpa only [BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq,
      ByteArray.getElem_append_right (by omega : a.size ≤ i.val)] using byte

end Hkdf.Proofs.Wrapper.Absorb
