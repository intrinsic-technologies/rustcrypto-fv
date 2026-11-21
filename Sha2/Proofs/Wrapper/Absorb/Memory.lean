import Sha2.Proofs.Wrapper.Absorb.Copy
import Sha2.Proofs.Wrapper.Absorb.Mathematics

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper.Absorb

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.SHA256

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

theorem copied_tail {v : Variant} [Bindings] {initial s t : RamState} {inputs : Array Input}
    {input : Input} {site : Copy.Site} {count : Nat} {previous : ByteArray}
    (ctx : Context (v := v) initial inputs) (buffered : Buffered (v := v) initial s previous)
    (copy : Copy.Result (v := v) initial s t input site 0 (previous.size%64) count)
    (sourceBound : count ≤ input.bytes.size) (bound : previous.size%64+count ≤ 64) :
    (⟨(stackPtr initial-152).toNat,
      (remainderBytes previous ++ input.bytes.extract 0 count).size⟩ : MemoryRegion).HasBytes
        t.external (remainderBytes previous ++ input.bytes.extract 0 count) := by
  apply hasBytes_append
  · refine ⟨rfl,fun i => ?_⟩
    have hi : i.val < previous.size%64 := by simpa only [remainderBytes_size] using i.isLt
    have byte := copy.bytes_unchanged ctx bound (offset:=152) (len:=previous.size%64)
      (by decide) (by omega) (.inl (by omega)) i.val hi
    have old := buffered.tailBytes.2 i
    change s.external[BitVec.ofNat 64 ((stackPtr initial-152).toNat+i.val)]? = _ at old
    rw [BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq] at old
    change t.external[BitVec.ofNat 64 ((stackPtr initial - 152#64).toNat+i.val)]? = _
    rw [BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq]
    exact byte.trans old
  · have size : (input.bytes.extract 0 count).size=count := by
      simp only [ByteArray.size_extract,Nat.sub_zero,Nat.min_eq_left sourceBound]
    simpa only [remainderBytes_size,Nat.zero_add,size] using copy.bytes

end Sha2.Proofs.Wrapper.Absorb
