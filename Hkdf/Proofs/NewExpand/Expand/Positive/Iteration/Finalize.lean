import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Finalize.Digest
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Finalize.Frame
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Finalize.Inner
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Finalize.InnerPrefix
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Finalize.Outer

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand.Finalize

open Hkdf.Spec.Program Hkdf.Proofs.Program Hkdf.Proofs.Common Hkdf.Proofs.Common.CallFrame
open Hkdf.Proofs.Common.SHA256 Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem run [Bindings] {entry s : RamState} {boundary : ReturnBoundary}
    {key info message : ByteArray} {ptr : BitVec 64} {length : Nat}
    (pre : ExpandPre entry boundary key info ptr length) (saved : SavedFrame entry s boundary length)
    (positive : 0 < length) (limit : length ≤ 8160)
    (pc : s.RIP = 0x10f95a) (hmac : HmacAt s (stackPtr s + 80) key message) :
    ∃ t, Result entry s t boundary length key message := by
  have stack := pre.call.stack
  have avoids : ∀ r ∈ #v[registerRegion entry .rcx (writtenLength length), Stack.region entry 2264],
      r.Avoids InProgram := by
    simp only [writtenLength, limit, ↓reduceIte]
    exact fun r hr a ha hp => ((pre.separation positive limit).2 r hr).2 a ha (.inl hp)
  obtain ⟨a, first⟩ := InnerPrefix.run pre saved.toRunning (by simp) avoids saved.sp pc hmac.inner
  have frameA := prefix_frame first.frame
  have savedA := saved_of_frame saved stack first.running first.sp frameA first.mxcsr first.fcw
  obtain ⟨b, inner⟩ := Inner.run pre positive limit savedA first.rip first.bytes
    first.remainder first.blocks first.hash
  obtain ⟨low, high⟩ := Inner.local_bounds stack savedA.sp
  have preserved (off size : Nat) (above : 176 ≤ off) (fit : off + size ≤ 256) :
      (Component.mem (stackPtr s + BitVec.ofNat 64 off) size).Agrees s b := by
    have ha := first.agrees_stack stack saved.sp (offset := off) (size := size) (by omega) (.inr above)
    have hb := Inner.agrees low high inner.frame (off := off) (size := size) (by omega)
      (.inr (.inr (.inl ⟨above,fit⟩)))
    rw [first.sp] at hb
    exact fun i hi => (hb i hi).trans (ha i hi)
  let outerHash := compressBlocks Hkdf.Proofs.NIST.SHA256.initialHash
    (HMAC.xorPad (HMAC.keyBlock key) 0x5c)
  have words : HashStateAt b (stackPtr b + 184) outerHash := by
    rw [inner.rsp, first.sp]
    apply hashState_of_bytes (a := stackPtr s + 184) _ (preserved 184 32 (by decide) (by decide))
    rw [show stackPtr s + 184 = (stackPtr s + 80) + 104 by bv_omega]
    exact hmac.outerHash
  have count : loadBytes b.external (stackPtr b + 216) 8 = .ok 1 := by
    rw [inner.rsp, first.sp]
    apply (agrees_loadBytes (preserved 216 8 (by decide) (by decide))).trans
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using hmac.outerBlocks
  obtain ⟨_, t, outerRun, savedT, pcT, spT, abi, frameT, digest⟩ :=
    Outer.finalizeOuter pre positive limit inner.saved inner.rip
      (inner.rsp ▸ inner.r13) (inner.rsp ▸ inner.r15) inner.hashWords words count
  have slotA (off : Nat) (above : 176 ≤ off) (fit : off + 8 ≤ 544) :
      slot a (BitVec.ofNat 64 off) = slot s (BitVec.ofNat 64 off) := by
    change memLoad a.external (stackPtr a + _) 64 = _
    rw [first.sp]
    exact agrees_memLoad (first.agrees_stack stack saved.sp fit (.inr above))
  have slotT := Outer.slot_of_frame stack inner.saved.sp spT frameT (offset := 256)
    (by decide) (by decide) (by decide)
  have totalFrame : MemoryWriteFrame s t (writes (stackPtr s)) := by
    have frameB := inner_frame high inner.frame
    have frameC := outer_frame frameT
    rw [inner.rsp, first.sp] at frameC
    rw [first.sp] at frameB
    exact memoryWriteFrame_trans frameA (memoryWriteFrame_trans frameB frameC)
  obtain ⟨_, runA⟩ := first.execution
  obtain ⟨_, runB⟩ := inner.execution
  refine ⟨t, {
    toSavedFrame := savedT
    advances := ⟨_, (runA.trans runB).trans outerRun⟩
    rip := pcT
    frameLocal := totalFrame
    r12Reg := (abi.1 .r12 (by simp)).trans (inner.r12.trans first.r12)
    r13Reg := ?_
    r14Reg := ?_
    chunk := ?_
    nextPtr := ?_
    counter := ?_
    digest := ?_ }⟩
  · rw [abi.1 .r13 (by simp), inner.r13, spT, inner.rsp]
  · exact (abi.1 .r14 (by simp)).trans (inner.r14.trans (slotA 432 (by decide) (by decide)))
  · exact (abi.1 .rbx (by simp)).trans (inner.rbx.trans (slotA 264 (by decide) (by decide)))
  · rw [abi.1 .rbp (by simp), inner.rbp]
    exact (congrArg (· + slot a 264) (slotA 432 (by decide) (by decide))).trans
      (congrArg (slot s 432 + ·) (slotA 264 (by decide) (by decide)))
  · exact slotT.trans (inner.counter.trans (congrArg (· + 1) (slotA 256 (by decide) (by decide))))
  · simpa only [Outer.digest, outerHash, digest_eq_hmac] using digest

end Hkdf.Proofs.NewExpand.Expand.Finalize
