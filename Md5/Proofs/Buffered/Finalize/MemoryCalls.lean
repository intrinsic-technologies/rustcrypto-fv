import Md5.Proofs.Buffered.Finalize.Geometry
import Md5.Proofs.Buffered.Update.Calls

namespace Md5.Proofs.Buffered.Finalize

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable {kind : Kind} {s : RamState}

theorem Storage.pushAddress (h : Storage kind s) :
    (pushAddr s).toNat = (stackPtr s).toNat - 8 := by
  rw [pushAddr, BitVec.toNat_sub_of_le]
  · rfl
  · change 8 ≤ (stackPtr s).toNat
    have := h.stackLow
    omega

theorem Storage.pushRange (h : Storage kind s) :
    MemoryRoutines.WritableRange s (pushAddr s) 8 := by
  have he : stackPtr s - 320 + BitVec.ofNat 64 312 = pushAddr s := by
    simp only [pushAddr, BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  exact he ▸ h.belowRange.slice 312 8 (by decide)

theorem Storage.pushWritable (h : Storage kind s) :
    Memory.MemWritable s (pushAddr s) 8 :=
  ⟨h.pushRange.readable.low, h.pushRange.readable.mem, h.pushRange.tables⟩

theorem Storage.stackApartPush (h : Storage kind s) {offset len : Nat}
    (he : offset + len ≤ kind.stackBytes) :
    RangeApart (stackPtr s + BitVec.ofNat 64 offset) len (pushAddr s) 8 := by
  have hh : (stackPtr s).toNat + kind.stackBytes < 2^32 := h.stackHigh
  have hl := h.stackLow
  apply RangeApart.of_toNat
  · rw [h.stackAddress (by omega)]
    omega
  · rw [h.pushAddress]
    omega
  · rw [h.stackAddress (by omega), h.pushAddress]
    omega

theorem Storage.memsetSitePre (h : Storage kind s) {ret : BitVec 64}
    {offset len : Nat} (hdf : DirectionFlagClear s.RFLAGS)
    (hdst : rdi.read s = stackPtr s + BitVec.ofNat 64 offset)
    (hlen : (MemoryRoutines.rdx.read s).toNat = len)
    (he : offset + len ≤ kind.stackBytes)
    (hret : ret.toNat < 2^32) (hout : ret.toNat < 0x102460 ∨ 0x1024a5 ≤ ret.toNat) :
    MemsetSitePre ret s := by
  refine ⟨hdf, ?_, h.pushRange.readable, h.pushRange.code, ?_, hret, hout⟩
  · rw [hdst, hlen]
    exact h.stackRange offset len he
  · rw [hdst, hlen]
    exact h.stackApartPush he

end Md5.Proofs.Buffered.Finalize
