import K256.Proofs.Signing.Hash.Update.Slice
import K256.Proofs.Verify.Hash.Update.Copy

namespace K256.Proofs.Signing.Hash.Update

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
open K256.Proofs.Verify.Hash

theorem inputAfter {sp src : BitVec 64} {msg : ByteArray} {m t : Ram}
    (frame : RamWriteFrame m t (regions sp))
    (depth : 512 ≤ sp.toNat) (low : src.toNat + msg.size < 2^32)
    (apart : src.toNat + msg.size ≤ sp.toNat - 512 ∨ sp.toNat + 1160 ≤ src.toNat)
    (bytes : (⟨src.toNat, msg.size⟩ : MemoryRegion).HasBytes m msg) :
    (⟨src.toNat, msg.size⟩ : MemoryRegion).HasBytes t msg := by
  refine ⟨bytes.1, fun i => ?_⟩
  let addr := BitVec.ofNat 64 (src.toNat + i.val)
  have h : addr.toNat = src.toNat + i.val := Nat.mod_eq_of_lt (by have := i.isLt; omega)
  change t[addr]? = _
  rw [frame.outside]
  · exact bytes.2 i
  · refine ⟨by rw [h]; have := i.isLt; omega, fun r hr => ?_⟩
    simp only [regions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> dsimp only <;> rw [h] <;> have := i.isLt <;> omega

theorem copyTail {a : Values Value Reg.count} {m t : Ram} {sp src tail n : BitVec 64}
    {msg : ByteArray}
    (dstReg : a[7].get 64 = sp + 488) (srcReg : a[6].get 64 = tail)
    (count : a[2].get 64 = n) (rsp : a[4].get 64 = sp - 8) (direction : a[22].get 1 = 0)
    (source : tail = src + BitVec.ofNat 64 (64 * (msg.size / 64))) (len : n.toNat = msg.size % 64)
    (frame : RamWriteFrame m t (regions sp))
    (bytes : (⟨src.toNat, msg.size⟩ : MemoryRegion).HasBytes m msg)
    (input : Readable m src msg.size) (stack : Writable Extracted.programImage m (sp - 512) 1672)
    (depth : 512 ≤ sp.toNat) (limit : sp.toNat + 1160 < 2^32)
    (inputLow : src.toNat + msg.size < 2^32)
    (apart : 0 < msg.size → src.toNat + msg.size ≤ sp.toNat - 512 ∨ sp.toNat + 1160 ≤ src.toNat)
    (retLow : (memLoad t (sp - 8) 64).toNat < 2^32) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l12a820, a, t⟩, []⟩ out ∧
      out.store = memCopy t (sp + 488) tail n.toNat ∧
      out.tag = some ⟨64, memLoad t (sp - 8) 64⟩ ∧ out.values[4] = ⟨64, sp⟩ ∧
      (∀ i : Fin 53, i.val ∈ [3,5,9,10,11,12,13,14,15,22,39,50,51] → out.values[i] = a[i]) ∧
      RamWriteFrame m out.store (regions sp) ∧
      (⟨(sp + 488).toNat, msg.size % 64⟩ : MemoryRegion).HasBytes out.store (remainderBytes msg) := by
  let full := 64 * (msg.size / 64)
  have ht : tail.toNat = src.toNat + full := by
    rw [source, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 64 * _),
      Nat.mod_eq_of_lt] <;> (try dsimp only [full]) <;> omega
  have hd : (sp + 488).toNat = sp.toNat + 488 := by
    change (sp.toNat + 488) % 2^64 = sp.toNat + 488
    exact Nat.mod_eq_of_lt (by omega)
  have hb : (sp - 512).toNat = sp.toNat - 512 :=
    BitVec.toNat_sub_of_le (show (512 : BitVec 64) ≤ sp from depth)
  have hr : (sp - 8).toNat = sp.toNat - 8 :=
    BitVec.toNat_sub_of_le (show (8 : BitVec 64) ≤ sp from (by change 8 ≤ sp.toNat; omega))
  have read : Readable t tail n.toNat := (input.of_frame frame).sub (by omega) (by dsimp only [full] at ht; omega)
  have write : Writable Extracted.programImage t (sp + 488) n.toNat :=
    (stack.of_frame frame).sub (by omega) (by omega)
  have ret : Readable t (sp - 8) 8 := (stack.readable.of_frame frame).sub (by omega) (by omega)
  obtain ⟨out, run, copy, tag, _, back, kept⟩ := Verify.Hash.Update.memcpy dstReg srcReg count rsp
    direction read write (by
      dsimp only [full] at ht
      by_cases positive : 0 < msg.size
      · have separated := apart positive
        omega
      · have zero : n.toNat = 0 := by omega
        rw [zero]
        omega)
    (RangeApart.of_offsets rfl (addr_sub _ _) ⟨by change n.toNat ≤ 18446744073709551120; omega, by decide⟩) ret retLow
  refine ⟨out, run, copy, tag, ?_, kept, ?_, ?_⟩
  · rw [back]
    rw [BitVec.sub_add_cancel]
  · rw [copy]
    apply Sec1.Wrapper.Copy.memCopy_frame frame
    refine ⟨⟨sp.toNat + 488, 104⟩, by simp [regions], ?_⟩
    change sp.toNat + 488 ≤ _ ∧ _ ≤ sp.toNat + 488 + 104 ∧ _ ≤ 2^64
    omega
  · rw [copy, ← len]
    apply Sec1.Wrapper.Copy.memCopy_hasBytes (by omega)
    refine ⟨(remainderBytes_size msg).trans len.symm, fun i => ?_⟩
    have hi : i.val < msg.size % 64 := (remainderBytes_size msg) ▸ i.isLt
    have original := inputAfter frame depth inputLow (apart (by omega)) bytes
    have x := original.2 ⟨full+i.val, by dsimp only [full]; omega⟩
    change t[BitVec.ofNat 64 (src.toNat + (full + i.val))]? = _ at x
    have idx : i.val < (msg.extract full msg.size).size := i.isLt
    change t[BitVec.ofNat 64 (tail.toNat + i.val)]? = some ((msg.extract full msg.size)[i.val]'idx)
    rw [ht, Nat.add_assoc, ByteArray.getElem_extract]
    exact x

end K256.Proofs.Signing.Hash.Update
