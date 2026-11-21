import K256.Proofs.Sec1.Wrapper.Contracts
import K256.Proofs.Sec1.Wrapper.Copy.Execution
import K256.Proofs.Sec1.Buffers

namespace K256.Proofs.Sec1.Wrapper.Copy

open K256.Spec.Program Prelude X86 X86.Machine X86Proofs K256.Proofs.CFG K256.Proofs.Lift
  K256.Proofs.Refine Sec1.LIR

theorem copyCall {s : RamState} {bytes : ByteArray}
    (call : ValidCall publicKeyFromSec1Bytes s [bytes]) : CopyCall s := by
  let sp := s.regValue .rsp
  let dst := s.regValue .rdi
  let src := sp - 233
  let slot := sp - 256
  let output := outputRegion publicKeyFromSec1Bytes s
  intro args mem encoded frame status hb
  let pushed := memStore mem slot (0x101e62 : BitVec 64)
  let child := (((args.set 2 ⟨64, 65⟩).set 4 ⟨64, slot⟩).set 6 ⟨64, src⟩).set 7 ⟨64, dst⟩
  have room : 1928 ≤ sp.toNat := call.stackAvailable.2.2.1
  have sub (off : Nat) (small : off ≤ 1928) :
      (sp - BitVec.ofNat 64 off).toNat = sp.toNat - off := by
    have hn : (BitVec.ofNat 64 off).toNat = off := Nat.mod_eq_of_lt (by omega)
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hn]; omega), hn]
  have ss : src.toNat = sp.toNat - 233 := sub 233 (by decide)
  have sl : slot.toNat = sp.toNat - 256 := sub 256 (by decide)
  have ⟨_, writable, outside, _⟩ := buffers call
  have dstSep := outside.2 (stack s) (by simp)
  change dst.toNat + 65 ≤ sp.toNat - 1928 ∨
    sp.toNat - 1928 + (sp.toNat + 8 - (sp.toNat - 1928)) ≤ dst.toNat at dstSep
  have read (off len : Nat) (depth : off ≤ 1928) (fits : len ≤ off + 8) (pos : 0 < len) :
      Readable pushed (sp - BitVec.ofNat 64 off) len :=
    ((stackWritable call depth fits pos).readable.of_frame frame.writes).memStore slot _
  have srcRead := read 233 65 (by decide) (by decide) (by decide)
  have slotRead := read 256 8 (by decide) (by decide) (by decide)
  have dstWrite : Writable Extracted.programImage pushed dst 65 :=
    (writable.of_frame frame.writes).memStore slot _
  have slotValue : memLoad pushed slot 64 = 0x101e62 :=
    memLoad_memStore_same _ _ _ (by decide) (by decide)
  have apartOut (off : Nat) (depth : off ≤ 1928) :
      RangeApart dst 65 (sp - BitVec.ofNat 64 off) 8 := by
    apply RangeApart.of_toNat
    · have := dstWrite.readable.low
      omega
    · have := (read off 8 depth (by omega) (by decide)).low
      omega
    · rw [sub off depth]
      omega
  have df : child[22].get 1 = 0 := by
    simp only [child, Vector.getElem_set]
    change args[22].get 1 = 0
    exact congrArg (Value.get 1) ((frame.kept 22 (by decide)).trans (Reg.read_df_iff.mpr call.directionFlagUnset))
  obtain ⟨out, run, store, tag, _, rsp, kept⟩ := memcpy (args := child) (count := 65)
    (mem := pushed) (dst := dst) (src := src) (rsp := slot) (by simp only [child, Vector.getElem_set]; rfl) (by simp only [child, Vector.getElem_set]; rfl)
    (by simp only [child, Vector.getElem_set]; rfl) (by simp only [child, Vector.getElem_set]; rfl) df srcRead dstWrite
    (by change src.toNat + 65 ≤ dst.toNat ∨ dst.toNat + 65 ≤ src.toNat; omega)
    (apartOut 256 (by decide)) slotRead (by rw [slotValue]; decide)
  change out.store = memCopy pushed dst src 65 at store
  have unchanged (off : Nat) (depth : off ≤ 16) :
      memLoad out.store (sp - BitVec.ofNat 64 off) 64 = memLoad mem (sp - BitVec.ofNat 64 off) 64 := by
    rw [store]
    unfold memCopy pushed
    rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (apartOut off (by omega)),
      memLoad_memStore_of_rangeApart _ _ _ _ _ (by
        apply RangeApart.of_toNat
        · have := slotRead.low; omega
        · have := (read off 8 (by omega) (by omega) (by decide)).low; omega
        · change slot.toNat + 8 ≤ (sp - BitVec.ofNat 64 off).toNat ∨ _
          rw [sub off (by omega)]
          omega)]
  have hb' : (⟨src.toNat, 65⟩ : MemoryRegion).HasBytes pushed encoded := by
    refine ⟨hb.1, fun i => ?_⟩
    have h := hb.2 i
    change pushed[BitVec.ofNat 64 (src.toNat + i.val)]? = _
    change mem[BitVec.ofNat 64 (src.toNat + i.val)]? = _ at h
    rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at h ⊢
    exact (memStore_getElem?_of_ne mem slot _ _ (fun j hj he => by
      have hap : RangeApart slot 8 src 65 := RangeApart.of_toNat
        (by have := slotRead.low; omega) (by have := srcRead.low; change src.toNat + 65 ≤ 2^32 at this; omega)
        (Or.inl (by omega))
      exact hap j hj i.val (by have hs : encoded.size = 65 := hb.1; omega) he)).trans h
  have saved (i : Fin 53) (hi : i.val ∈ [3,5,12,13,14,15,22]) :
      out.values[i] = args[i] := by
    apply (kept i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega)).trans
    change child[i.val] = args[i.val]
    simp only [child, Vector.getElem_set]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h | h | h | h | h | h | h <;> simp [h]
  refine ⟨out, run, tag.trans (by rw [slotValue]), ?_, (saved 3 (by decide)).trans status, ?_⟩
  · constructor
    · exact rsp.trans (congrArg (fun b : BitVec 64 => (⟨64, b⟩ : Value))
        (show slot + 8 = sp - 248 by dsimp [slot]; bv_omega))
    · exact (saved 14 (by decide)).trans frame.dst
    · intro i hi
      exact (saved i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega)).trans
        (frame.kept i hi)
    · exact (unchanged 16 (by decide)).trans frame.rbx
    · exact (unchanged 8 (by decide)).trans frame.r14
    · simpa only [BitVec.sub_zero] using (unchanged 0 (by decide)).trans (by simpa using frame.ret)
    · have wider : RamWriteFrame s.external mem [output, stack s] := by
        apply (RamWriteFrame.refl s.external _).trans frame.writes
        intro r hr
        obtain rfl := List.mem_singleton.mp hr
        exact ⟨_, by simp, Nat.le_refl _, Nat.le_refl _⟩
      have pushFrame : RamWriteFrame s.external pushed [output, stack s] := by
        apply wider.memStore
        refine ⟨stack s, by simp, ?_⟩
        change sp.toNat - 1928 ≤ slot.toNat ∧ slot.toNat + 8 ≤
          sp.toNat - 1928 + (sp.toNat + 8 - (sp.toNat - 1928)) ∧ slot.toNat + 8 ≤ 2 ^ 64
        have := slotRead.low
        change slot.toNat + 8 ≤ 2^32 at this
        omega
      rw [store]
      apply memCopy_frame pushFrame
      refine ⟨output, by simp, Nat.le_refl _, Nat.le_refl _, ?_⟩
      have := dstWrite.readable.low
      omega
  · rw [store]
    exact memCopy_hasBytes (by decide) hb'

end K256.Proofs.Sec1.Wrapper.Copy
