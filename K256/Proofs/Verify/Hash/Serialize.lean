import K256.Proofs.Verify.LIR.Program
import K256.Proofs.Verify.LIR.Generated.Values
import K256.Proofs.Common.Tactic
import K256.Proofs.Verify.Hash.Output

namespace K256.Proofs.Verify.Hash
open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Spec.Program
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

def coreReturn : StackFrame Value Label signature Reg.count :=
  ⟨.l1033a2, #v[], rfl, some ⟨64, 0x1033a2⟩⟩

def coreMemory (m : Ram) (sp : BitVec 64) (hash : Array UInt32) : Ram :=
  memStore (memCopy (storeDigestWords m (sp + 128) hash 8) (sp + 160) (sp + 416) 88)
    (sp - 8) (0x1033a2 : BitVec 64)

set_option maxRecDepth 4096 in
theorem serializeCall {a : Values Value 53} {m : Ram} {sp : BitVec 64} {hash : Array UInt32}
    (rsp : a[4].get 64 = sp)
    (read : Readable m (sp + 72) 32)
    (write : Writable Extracted.programImage m (sp + 128) 32)
    (hwords : WordsAt m (sp + 72) 32 (Vector.ofFn fun i : Fin 8 => hash[i.val]!.toBitVec))
    (rep : RepMovsOk Extracted.programImage (storeDigestWords m (sp + 128) hash 8)
      (a[22].get 1) (sp + 416) (sp + 160) 11 8 0x10338f 3)
    (push : StoreOk Extracted.programImage
      (memCopy (storeDigestWords m (sp + 128) hash 8) (sp + 160) (sp + 416) 88)
      (sp - 8) 8 0x10339d 5) :
    ∃ args, program.runBlock (dialect Extracted.programImage) ⟨.l103306, a, m⟩ =
      .call ⟨.l10fa10, args, coreMemory m sp hash⟩ coreReturn ∧
      args[3] = ⟨64, sp+8⟩ ∧ args[4] = ⟨64, sp-8⟩ ∧
      args[6] = ⟨64, sp+160⟩ ∧ args[7] = ⟨64, sp+8⟩ ∧
      (∀ i : Fin 53, i.val ∈ [5,12,13,14,15,22,39,50,51] → args[i] = a[i]) ∧
      (∀ i : Fin 53, i.val ∈ [1,2,8,9] → args[i].width = 64) := by
  have word (i : Nat) (hi : i < 8) :
      memLoad m (wordAddr (sp + 72) 32 i) 32 = hash[i]!.toBitVec := by
    have h := hwords i hi
    rw [Vector.getElem_ofFn] at h
    exact h
  have word0 := word 0 (by decide)
  have word1 := word 1 (by decide)
  have word2 := word 2 (by decide)
  have word3 := word 3 (by decide)
  have word4 := word 4 (by decide)
  have word5 := word 5 (by decide)
  have word6 := word 6 (by decide)
  have word7 := word 7 (by decide)
  simp only [wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.ofNat_eq_ofNat,
    BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] at word0 word1 word2 word3 word4 word5 word6 word7
  cfg_eval
  simp only [rsp, false_or]
  iterate 16 rw [ite_eq_left (by slot_guard using code_l103306)]
  simp only [BitVec.ofNat_eq_ofNat, word0, word1, word2, word3, word4, word5, word6, word7]
  simp only [storeDigestWords, wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.ofNat_eq_ofNat,
    BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] at rep push ⊢
  rw [ite_eq_left rep, ite_eq_left push]
  simp only [coreReturn, coreMemory, storeDigestWords, wordAddr, Nat.reduceDiv, Nat.reduceMul,
    BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero]
  refine ⟨_, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · rintro ⟨i, hi⟩ member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · rintro ⟨i, hi⟩ member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> rfl

theorem coreMemory_digest (m : Ram) (sp : BitVec 64) {hash : Array UInt32} (size : hash.size = 8) :
    (⟨(sp + 128).toNat, 32⟩ : MemoryRegion).HasBytes (coreMemory m sp hash)
      (serializeHash hash) := by
  have initial := storeDigestWords_hasBytes m (sp + 128) size
  refine ⟨initial.1, fun i => ?_⟩
  have hi : i.val < 32 := by simpa only [serializeHash_size, size] using i.isLt
  have atByte := initial.2 i
  simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at atByte ⊢
  unfold coreMemory memCopy
  rw [memStore_getElem?_of_ne _ _ _ _ (fun j hj =>
    (RangeApart.of_offsets (addr_sub sp 8) (rfl : sp+128 = sp+128) (by decide) :
      RangeApart (sp-8) 8 (sp+128) 32) j hj i.val hi)]
  rw [memStore_getElem?_of_ne _ _ _ _ (fun j hj =>
    (RangeApart.of_offsets (rfl : sp+160 = sp+160) (rfl : sp+128=sp+128) (by decide) :
      RangeApart (sp+160) 88 (sp+128) 32) j hj i.val hi)]
  exact atByte

end K256.Proofs.Verify.Hash
