import Hkdf.Proofs.NewExpand.Expand.Frame

namespace Hkdf.Proofs.NewExpand.Expand

open Hkdf.Spec.Program Hkdf.Proofs.Common
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem roundInputs [Bindings] {entry s : RamState} {boundary : ReturnBoundary}
    {key info : ByteArray} {ptr : BitVec 64} {length : Nat}
    (pre : ExpandPre entry boundary key info ptr length)
    (frame : MemoryWriteFrame entry s
      #v[registerRegion entry .rcx (writtenLength length), Stack.region entry 2264])
    (pos : 0 < length) (bound : length ≤ 8160) :
    HmacAt s (entry.regValue .rdi) key ByteArray.empty ∧
      memLoad s.external (entry.regValue .rsi) 64 = ptr ∧
      memLoad s.external (entry.regValue .rsi + 8) 64 = BitVec.ofNat 64 info.size ∧
      ValidInput s.external ⟨ptr.toNat, info.size⟩ info := by
  simp only [writtenLength, bound, ↓reduceIte] at frame
  have sep := pre.separation pos bound
  have apart {region} (member : region ∈
        [registerRegion entry .rdi 144, registerRegion entry .rsi 16, ⟨ptr.toNat, info.size⟩]) :
      ∀ written ∈ #v[registerRegion entry .rcx length, Stack.region entry 2264],
        region.Disjoint written := fun written hw ↦ (sep.2 written hw).1 region member
  have keep (r : Syntax.Reg) (bytes : Nat) (hread : (registerRegion entry r bytes).Bounded)
      (member : registerRegion entry r bytes ∈
        [registerRegion entry .rdi 144, registerRegion entry .rsi 16, ⟨ptr.toNat, info.size⟩]) :
      (Component.mem (entry.regValue r) bytes).Agrees entry s := by
    apply CallFrame.frame_agrees_of_disjoint frame
    · change (entry.regValue r).toNat + bytes < 2^32 at hread
      omega
    · exact apart member
  have hmac := pre.hmac.of_copy (keep .rdi 144 (pre.call.readsBounded _ (by simp)) (by simp))
  have descriptor := keep .rsi 16 (pre.call.readsBounded _ (by simp)) (by simp)
  have pointer : memLoad entry.external (entry.regValue .rsi) 64 = ptr := by
    apply Memory.memLoad_of_loadBytes64
    simpa only [registerRegion, BitVec.ofNat_toNat, BitVec.setWidth_eq] using pre.pointer.2
  have count : memLoad entry.external (entry.regValue .rsi + 8) 64 = BitVec.ofNat 64 info.size := by
    apply Memory.memLoad_of_loadBytes64
    simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      BitVec.ofNat_eq_ofNat] using pre.infoLength.2
  have valid := pre.infoBytes pos bound
  refine ⟨hmac, ?_, ?_, valid.1, CallFrame.frame_hasBytes frame (apart (by simp)) ?_ valid.2⟩
  · simpa only [BitVec.add_zero, BitVec.ofNat_eq_ofNat] using
      (CallFrame.agrees_memLoad_offset (offset := 0) (width := 64) descriptor (by decide)).trans
        (by simpa only [BitVec.add_zero, BitVec.ofNat_eq_ofNat] using pointer)
  · exact (CallFrame.agrees_memLoad_offset (offset := 8) descriptor (by decide)).trans count
  · have h := valid.1
    change ptr.toNat + info.size < 2^32 at h
    change ptr.toNat + info.size ≤ 2^64
    omega

end Hkdf.Proofs.NewExpand.Expand
