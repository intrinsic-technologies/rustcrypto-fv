import K256.Proofs.Signing.UpdateV.Finalize.State
import K256.Proofs.Common.Tactic
import K256.Proofs.Verify.LIR.Fn107a50
import K256.Proofs.Verify.Hash.Output
import K256.Proofs.Ecdh.Output.Memory

namespace K256.Proofs.Signing.UpdateV.Finalize

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  K256.Proofs.Verify.Hash Standards.NIST.SHA2

private def outerWrites (sp : BitVec 64) (size : Nat) : List MemoryRegion :=
  [⟨(sp + 176).toNat, size⟩]

private theorem outerOffset {m : Ram} {sp : BitVec 64}
    (stack : Readable m sp 312) (i : Nat) (hi : i ≤ 312) :
    (sp + BitVec.ofNat 64 i).toNat = sp.toNat + i := by
  have low := stack.low
  exact toNat_add_ofNat sp i (by omega)

private theorem outerIn {m : Ram} {sp : BitVec 64} (stack : Readable m sp 312)
    {i n size : Nat} (regionSize : size ≤ 96) (lo : 176 ≤ i) (hi : i + n ≤ 176 + size) :
    InRegions (outerWrites sp size) (sp + BitVec.ofNat 64 i) n := by
  refine ⟨_, List.mem_cons_self, ?_⟩
  change (sp + BitVec.ofNat 64 176).toNat ≤ (sp + BitVec.ofNat 64 i).toNat ∧
    (sp + BitVec.ofNat 64 i).toNat + n ≤ (sp + BitVec.ofNat 64 176).toNat + size ∧
    (sp + BitVec.ofNat 64 i).toNat + n ≤ 2^64
  rw [outerOffset stack 176 (by decide), outerOffset stack i (by omega)]
  have low := stack.low
  omega

private theorem outerWord {m : Ram} {sp : BitVec 64} {hash : Array UInt32}
    (state : Compression.StateAt m (sp + 72) hash) {i : Nat} (hi : i < 8) :
    memLoad m (sp + BitVec.ofNat 64 (72 + 4 * i)) 32 = hash[i]!.toBitVec := by
  have w := state.2 i hi
  rw [Vector.getElem_ofFn] at w
  simpa only [wordAddr, Nat.reduceDiv, BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using w

private theorem serializedFrame {m : Ram} {sp : BitVec 64} (stack : Readable m sp 312)
    (hash : Array UInt32) :
    RamWriteFrame m (storeDigestWords m (sp + 176) hash 8) (outerWrites sp 32) := by
  apply storeDigestWords_frame
  intro i hi
  have h := outerIn stack (i := 176 + 4 * i) (n := 4) (size := 32) (by decide) (by omega) (by omega)
  simpa only [wordAddr, Nat.reduceDiv, BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using h

private theorem outerPreserveLoad {m t : Ram} {sp : BitVec 64} (stack : Readable m sp 312)
    {size : Nat} (frame : RamWriteFrame m t (outerWrites sp size)) (i width : Nat)
    (endIn : i + width / 8 ≤ 312) (apart : i + width / 8 ≤ 176 ∨ 176 + size ≤ i) :
    memLoad t (sp + BitVec.ofNat 64 i) width =
      memLoad m (sp + BitVec.ofNat 64 i) width := by
  apply frame.memLoad_eq
  refine ⟨?_, ?_⟩
  · rw [outerOffset stack i (by omega)]
    have low := stack.low
    omega
  · intro r hr
    obtain rfl := List.mem_singleton.mp hr
    change (sp + BitVec.ofNat 64 i).toNat + width / 8 ≤ (sp + BitVec.ofNat 64 176).toNat ∨
      (sp + BitVec.ofNat 64 176).toNat + size ≤ (sp + BitVec.ofNat 64 i).toNat
    rw [outerOffset stack i (by omega), outerOffset stack 176 (by decide)]
    omega

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4096 in
private theorem serializeInner {a : Registers} {m : Ram} {sp : BitVec 64} {hash : Array UInt32}
    (rsp : a[4] = ⟨64,sp⟩) (stack : Writable Extracted.programImage m sp 312)
    (innerHash : Compression.StateAt m (sp + 72) hash) (used : memLoad m (sp + 271) 8 = 0) :
    ∃ b, program.runBlock (dialect Extracted.programImage) ⟨.l107c66,a,m⟩ =
      .jump ⟨.l107ce6,b,storeDigestWords m (sp + 176) hash 8⟩ ∧
      b[4] = ⟨64,sp⟩ ∧ b[15] = ⟨64,0⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,22,39,50,51] → b[i] = a[i]) := by
  let t := storeDigestWords m (sp + 176) hash 8
  have cnt : memLoad t (sp + 271) 8 = 0 :=
    (outerPreserveLoad stack.readable (serializedFrame stack.readable hash) 271 8
      (by decide) (by decide)).trans used
  have rspBits := congrArg (Value.get 64) rsp
  change a[4].get 64 = sp at rspBits
  have w0 := outerWord innerHash (i := 0) (by decide)
  have w1 := outerWord innerHash (i := 1) (by decide)
  have w2 := outerWord innerHash (i := 2) (by decide)
  have w3 := outerWord innerHash (i := 3) (by decide)
  have w4 := outerWord innerHash (i := 4) (by decide)
  have w5 := outerWord innerHash (i := 5) (by decide)
  have w6 := outerWord innerHash (i := 6) (by decide)
  have w7 := outerWord innerHash (i := 7) (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd] at w0 w1 w2 w3 w4 w5 w6 w7
  simp only [t, storeDigestWords, wordAddr, Nat.reduceDiv, Nat.reduceMul,
    BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] at cnt
  refine ⟨?_, ?step, ?post⟩
  case step =>
    cfg_eval [rspBits]
    iterate 17 refine Eq.trans (ite_eq_left (by slot_guard using code_l107c66)) ?_
    simp only [BitVec.ofNat_eq_ofNat, w0, w1, w2, w3, w4, w5, w6, w7]
    simp only [storeDigestWords, wordAddr, Nat.reduceDiv, Nat.reduceMul,
      BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero]
    simp only [cnt]
    refine Eq.trans (ite_eq_right (by decide +kernel)) ?_
    rfl
  case post =>
    refine ⟨rsp, rfl, ?_⟩
    rintro ⟨i, _⟩ hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private def outerMemory (m : Ram) (sp : BitVec 64) : Ram :=
  memStore (Ecdh.Output.copyMemory m (sp - 168) (sp + 208)) (sp + 271) (32 : BitVec 8)

set_option maxHeartbeats 700000 in
private theorem appendDigest {a : Registers} {m : Ram} {sp : BitVec 64}
    (rsp : a[4] = ⟨64,sp⟩) (zero : a[15] = ⟨64,0⟩)
    (stack : Writable Extracted.programImage m sp 312) :
    ∃ b, program.runBlock (dialect Extracted.programImage) ⟨.l107ce6,a,m⟩ =
      .jump ⟨.l107da7,b,outerMemory m sp⟩ ∧
      b[4] = ⟨64,sp⟩ ∧ b[15].width = 64 ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,22,39,50,51] → b[i] = a[i]) := by
  have rspBits := congrArg (Value.get 64) rsp
  change a[4].get 64 = sp at rspBits
  have clearBits := congrArg (Value.get 64) zero
  change a[15].get 64 = 0 at clearBits
  have keep {t : Ram} (v : BitVec 64) (src dst : BitVec 64)
      (sep : 8 ≤ (src - dst).toNat ∧ 8 ≤ (dst - src).toNat) :
      memLoad (memStore t (sp + dst) v) (sp + src) 64 = memLoad t (sp + src) 64 :=
    memLoad_memStore_of_rangeApart _ _ _ _ _ (RangeApart.of_offsets rfl rfl sep)
  have keep192 {t : Ram} (v : BitVec 64) := keep (t := t) v 192 232 (by decide)
  have keep176a {t : Ram} (v : BitVec 64) := keep (t := t) v 176 232 (by decide)
  have keep176b {t : Ram} (v : BitVec 64) := keep (t := t) v 176 224 (by decide)
  have keep184a {t : Ram} (v : BitVec 64) := keep (t := t) v 184 232 (by decide)
  have keep184b {t : Ram} (v : BitVec 64) := keep (t := t) v 184 224 (by decide)
  simp only [BitVec.ofNat_eq_ofNat] at keep192 keep176a keep176b keep184a keep184b
  have mark : (mergeGPR 8 (32#8) (0#64)).setWidth 8 = 32#8 := by decide +kernel
  refine ⟨?_, ?step, ?post⟩
  case step =>
    cfg_eval [rspBits, zero, clearBits]
    iterate 9 refine Eq.trans (ite_eq_left (by slot_guard using code_l107ce6)) ?_
    simp only [outerMemory, Ecdh.Output.copyMemory, BitVec.ofNat_eq_ofNat,
      BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd]
    simp only [keep192, keep176a, keep176b, keep184a, keep184b, mark,
      show sp - 168#64 + 368#64 = sp + 200#64 by bv_omega,
      show sp - 168#64 + 360#64 = sp + 192#64 by bv_omega,
      show sp - 168#64 + 352#64 = sp + 184#64 by bv_omega,
      show sp - 168#64 + 344#64 = sp + 176#64 by bv_omega]
    rfl
  case post =>
    refine ⟨rsp, rfl, ?_⟩
    rintro ⟨i, _⟩ hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem appendedWrites {m : Ram} {sp : BitVec 64}
    (stack : Readable m sp 312) :
    RamWriteFrame m (outerMemory m sp) (outerWrites sp 96) := by
  unfold outerMemory Ecdh.Output.copyMemory
  simp only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero]
  apply RamWriteFrame.memStore _ _ (outerIn stack (i := 271) (by decide) (by decide) (by decide))
  apply RamWriteFrame.memStore _ _ (outerIn stack (i := 208) (by decide) (by decide) (by decide))
  apply RamWriteFrame.memStore _ _ (outerIn stack (i := 216) (by decide) (by decide) (by decide))
  apply RamWriteFrame.memStore _ _ (outerIn stack (i := 224) (by decide) (by decide) (by decide))
  apply RamWriteFrame.memStore _ _ (outerIn stack (i := 232) (by decide) (by decide) (by decide))
  exact .refl _ _

private theorem appendedBytes {m : Ram} {sp : BitVec 64} {bytes : ByteArray}
    (stack : Readable m sp 312)
    (source : (⟨(sp + 176).toNat, 32⟩ : MemoryRegion).HasBytes m bytes) :
    (⟨(sp + 208).toNat, 32⟩ : MemoryRegion).HasBytes (outerMemory m sp) bytes := by
  have readable : Readable m (sp + 208) 32 := stack.of_offsets rfl (addr_self _) (by decide)
  have localSource : (⟨(sp - 168 + 344).toNat, 32⟩ : MemoryRegion).HasBytes m bytes := by
    rwa [show sp - 168 + 344 = sp + 176 by bv_omega]
  have copied := Ecdh.Output.copyHasBytes localSource readable
  refine ⟨copied.1, fun i => ?_⟩
  have len : bytes.size = 32 := copied.1
  have hi : i.val < 32 := len ▸ i.isLt
  have apart : RangeApart (sp + 271) 1 (sp + 208) 32 := RangeApart.of_offsets rfl rfl (by decide)
  have hb := copied.2 i
  simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hb ⊢
  rw [outerMemory, memStore_getElem?_of_ne _ _ _ _ (fun j hj => apart j hj i.val hi)]
  exact hb

set_option maxRecDepth 4096 in
theorem outerBuffer {a : Registers} {m : Ram} {sp : BitVec 64} {inner pad : ByteArray}
    (rsp : a[4] = ⟨64,sp⟩) (stack : Writable Extracted.programImage m sp 312)
    (length : pad.size = 64) (small : inner.size % 64 < 56)
    (innerHash : Compression.StateAt m (sp + 72) (digestState inner))
    (outerHash : Compression.StateAt m (sp + 272) (compressBlocks initialHash pad))
    (used : memLoad m (sp + 271) 8 = 0) (count : memLoad m (sp + 304) 64 = 1) :
    ∃ b t, Reaches .l107c66 a m .l107da7 b t ∧ b[4] = ⟨64,sp⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,22,39,50,51] → b[i] = a[i]) ∧
      b[15].width = 64 ∧ RamWriteFrame m t [⟨(sp + 176).toNat,96⟩] ∧
      Buffered t (sp + 208) (pad ++ SHA256.hashBytes inner) := by
  let mid := storeDigestWords m (sp + 176) (digestState inner) 8
  let t := outerMemory mid sp
  have midFrame : RamWriteFrame m mid (outerWrites sp 32) :=
    serializedFrame stack.readable (digestState inner)
  have readable := stack.readable.of_frame midFrame
  have midFrameWide : RamWriteFrame m mid (outerWrites sp 96) :=
    (RamWriteFrame.refl m _).trans midFrame (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨_, List.mem_cons_self, Nat.le_refl _, Nat.add_le_add_left (show 32 ≤ 96 by decide) _⟩)
  have writes : RamWriteFrame m t (outerWrites sp 96) :=
    midFrameWide.trans (appendedWrites readable) (fun r hr => ⟨r, hr, Nat.le_refl _, Nat.le_refl _⟩)
  obtain ⟨b, run1, rsp1, zero, kept1⟩ := serializeInner rsp stack innerHash used
  obtain ⟨c, run2, rsp2, width15, kept2⟩ := appendDigest rsp1 zero (stack.of_frame midFrame)
  have serialize : serializeHash (digestState inner) = SHA256.hashBytes inner := by
    simpa only [digestState, small, ite_true] using serializeHash_finalize inner
  have digest : (⟨(sp + 208).toNat, 32⟩ : MemoryRegion).HasBytes t (SHA256.hashBytes inner) := by
    rw [← serialize]
    exact appendedBytes readable (storeDigestWords_hasBytes m (sp + 176) innerHash.1)
  have digestSize : (SHA256.hashBytes inner).size = 32 := digest.1
  have size : (pad ++ SHA256.hashBytes inner).size = 96 := by
    rw [ByteArray.size_append, length, digestSize]
  have remBytes : remainderBytes (pad ++ SHA256.hashBytes inner) = SHA256.hashBytes inner := by
    unfold remainderBytes
    rw [size]
    exact ByteArray.extract_append_eq_right length.symm (by rw [length, digestSize])
  have compress : compressBlocks initialHash (pad ++ SHA256.hashBytes inner) =
      compressBlocks initialHash pad := by
    rw [compressBlocks_append _ _ _ (by rw [length])]
    simp only [compressBlocks, digestSize, Nat.reduceDiv, compressBlocksFrom]
  refine ⟨c, t, ?reach, rsp2, fun i hi => (kept2 i hi).trans (kept1 i hi), width15, writes, ?_⟩
  case reach =>
    exact .step (congrArg (Transfer.next _ []) run1) (.step (congrArg (Transfer.next _ []) run2) (.refl _))
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [remBytes, size]
    exact digest
  · have marker : memLoad t (sp + 271) 8 = 32 :=
      memLoad_memStore_same (Ecdh.Output.copyMemory mid (sp - 168) (sp + 208)) (sp + 271)
        (32 : BitVec 8) (by decide) (by decide)
    have address : sp + 208 + 63 = sp + 271 := by bv_omega
    exact (congrArg (fun addr => memLoad t addr 8) address).trans
      (marker.trans (congrArg (fun n => BitVec.ofNat 8 (n % 64)) size.symm))
  · rw [compress]
    refine ⟨outerHash.1, fun i hi => ?_⟩
    have h := outerPreserveLoad stack.readable writes (272 + 4 * i) 32 (by omega) (by omega)
    have keep : memLoad t (wordAddr (sp + 272) 32 i) 32 =
        memLoad m (wordAddr (sp + 272) 32 i) 32 := by
      simpa only [wordAddr, Nat.reduceDiv, BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using h
    have address : sp + 208 + 64 = sp + 272 := by bv_omega
    exact (congrArg (fun base => memLoad t (wordAddr base 32 i) 32) address).trans
      (keep.trans (outerHash.2 i hi))
  · have finalCount : memLoad t (sp + 304) 64 = 1 :=
      (outerPreserveLoad stack.readable writes 304 64 (by decide) (by decide)).trans count
    have address : sp + 208 + 96 = sp + 304 := by bv_omega
    exact (congrArg (fun addr => memLoad t addr 64) address).trans
      (finalCount.trans (show (1 : BitVec 64) =
        BitVec.ofNat 64 ((pad ++ SHA256.hashBytes inner).size / 64) by
          rw [size]
          decide +kernel))

end K256.Proofs.Signing.UpdateV.Finalize
