import Sha2.Proofs.Wrapper512.Absorb.Copy
import Sha2.Proofs.Wrapper.Absorb.Memory
import Sha2.Proofs.Wrapper512.Absorb.Mathematics

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Absorb

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.SHA512

theorem copied_tail [Bindings] {v : Variant} {form : Form} {initial s t : RamState} {inputs : Array Input}
    {input : Input} {site : Copy.Site} {count : Nat} {previous : ByteArray}
    (ctx : Context v initial inputs form) (buffered : Buffered v initial s previous form form.activeMemory)
    (copy : Copy.Result v initial s t input site 0 (previous.size%128) count form)
    (sourceBound : count ≤ input.bytes.size) (bound : previous.size%128+count ≤ 128) :
    (⟨(stackPtr initial-BitVec.ofNat 64 form.activeMemory.buffer).toNat,
      (remainderBytes previous ++ input.bytes.extract 0 count).size⟩ : MemoryRegion).HasBytes
        t.external (remainderBytes previous ++ input.bytes.extract 0 count) := by
  have bufferLow : 128 ≤ form.activeMemory.buffer := by
    cases form <;> dsimp only [Form.activeMemory, Form.bufferedMemory, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory] <;> decide
  apply Sha2.Proofs.Wrapper.Absorb.hasBytes_append
  · refine ⟨rfl,fun i => ?_⟩
    have hi : i.val < previous.size%128 := by simpa only [remainderBytes_size] using i.isLt
    have byte := copy.bytes_unchanged ctx bound (offset:=form.activeMemory.buffer) (len:=previous.size%128)
      (by cases form <;> dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory] <;> decide) (by omega) (.inl (by omega)) i.val hi
    have old := buffered.tailBytes.2 i
    change s.external[BitVec.ofNat 64 ((stackPtr initial-BitVec.ofNat 64 form.activeMemory.buffer).toNat+i.val)]? = _ at old
    rw [BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq] at old
    change t.external[BitVec.ofNat 64 ((stackPtr initial - BitVec.ofNat 64 form.activeMemory.buffer).toNat+i.val)]? = _
    rw [BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq]
    exact byte.trans old
  · have size : (input.bytes.extract 0 count).size=count := by
      simp only [ByteArray.size_extract,Nat.sub_zero,Nat.min_eq_left sourceBound]
    simpa only [remainderBytes_size,Nat.zero_add,size] using copy.bytes

end Sha2.Proofs.Wrapper512.Absorb
