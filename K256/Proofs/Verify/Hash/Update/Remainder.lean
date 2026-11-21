import K256.Proofs.Verify.Hash.Update.Copy
import K256.Proofs.Verify.Hash.Update.Dispatch
import K256.Proofs.Verify.Hash.Update.Memory
import K256.Proofs.Verify.Hash.Padding.Tail

namespace K256.Proofs.Verify.Hash.Update

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine Verify.Wrapper Verify.LIR

local macro "copy_reg " idx:term " := " bits:term : tactic =>
  `(tactic| exact congrArg (Value.get 64) (show (copyArgs _ _ _ _)[$idx] = ⟨64, $bits⟩ by
    simp only [copyArgs, Vector.getElem_set, Nat.reduceEqDiff, ↓reduceIte]))

theorem copyRemainder {s : RamState} {key msg sig : ByteArray} {m : Ram}
    {a : Vector Value Reg.count} (call : ValidCall verifyingKeyVerify s [key,msg,sig])
    (cur : Memory s m) {src n : BitVec 64}
    (source : src = s.regValue .rsi + BitVec.ofNat 64 (64 * (msg.size / 64)))
    (len : n.toNat = msg.size % 64) (df : a[22].get 1 = 0)
    (ret : (memLoad m (localSp s - 8) 64).toNat < 2^32) :
    let sp := localSp s
    let child := copyArgs a sp src n
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l12a820,child,m⟩,[]⟩ out ∧
      out.store = memCopy m (sp+248) src n.toNat ∧
      out.tag = some ⟨64,memLoad m (sp-8) 64⟩ ∧ out.values[4] = ⟨64,sp⟩ ∧
      (∀ i : Fin 53, i.val ∈ [3,5,9,10,11,12,13,14,15,22,39,50,51] → out.values[i] = a[i]) ∧
      (⟨(sp+248).toNat, msg.size % 64⟩ : MemoryRegion).HasBytes out.store (remainderBytes msg) := by
  dsimp only
  let sp := localSp s
  let full := 64 * (msg.size / 64)
  obtain ⟨original, readable⟩ := messageMemory call cur
  have endLow : (s.regValue .rsi).toNat + msg.size ≤ 2^32 := readable.low
  have hlen : n.toNat < 64 := by rw [len]; exact Nat.mod_lt _ (by decide)
  have srcNat : src.toNat = (s.regValue .rsi).toNat + full := by
    rw [source, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := full), Nat.mod_eq_of_lt]
    all_goals dsimp only [full]; omega
  have srcRead : Readable m src n.toNat := readable.sub (by omega) (by dsimp only [full] at srcNat; omega)
  have dstEq : sp + 248 = stackPtr s - (288 : BitVec 64) := by
    dsimp only [sp, localSp]
    bv_omega
  have retEq : sp - 8 = stackPtr s - (544 : BitVec 64) := by
    dsimp only [sp, localSp]
    bv_omega
  have dstWrite : Writable Extracted.programImage m (sp + 248) n.toNat :=
    (writable (len := 63) (off := 288) call cur dstEq (by decide) (by decide) (by decide)).sub
      (Nat.le_refl _) (by omega)
  have retRead : Readable m (sp - 8) 8 :=
    (writable (off := 544) call cur retEq (by decide) (by decide) (by decide)).readable
  have dstNat : (sp + 248).toNat = (stackPtr s).toNat - 288 := by
    rw [dstEq]
    exact Common.stackOffset call.stackAvailable (by decide)
  have stack := stackBounds call
  have dis : src.toNat + n.toNat ≤ (sp+248).toNat ∨ (sp+248).toNat + n.toNat ≤ src.toNat := by
    by_cases hz : n.toNat = 0
    · simp only [hz, Nat.add_zero]
      exact Nat.le_total _ _
    · have pos : 0 < msg.size := by omega
      rcases messageApart call pos with h | h <;> dsimp only [full] at srcNat <;> omega
  have apart : RangeApart (sp+248) n.toNat (sp-8) 8 :=
    RangeApart.of_offsets rfl (addr_sub _ _) ⟨by change n.toNat ≤ 18446744073709551360; omega, by decide⟩
  have saved : ∀ i : Fin 53, i.val ∈ [3,5,9,10,11,12,13,14,15,22,39,50,51] →
      (copyArgs a sp src n)[i] = a[i] := by
    intro ⟨i,hi⟩ h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [copyArgs, Fin.getElem_fin, Vector.getElem_set, Nat.reduceEqDiff, ↓reduceIte]
  have direction : (copyArgs a sp src n)[22].get 1 = 0 := by
    exact (congrArg (Value.get 1) (saved 22 (by decide))).trans df
  obtain ⟨out,run,copy,tag,_,sp',preserved⟩ := memcpy
    (args := copyArgs a sp src n) (by copy_reg 7 := sp+248) (by copy_reg 6 := src)
    (by copy_reg 2 := n) (by copy_reg 4 := sp-8)
    direction srcRead dstWrite dis apart retRead ret
  refine ⟨out,run,copy,tag,?_,fun i hi => (preserved i hi).trans (saved i hi),?_⟩
  · rw [sp']
    congr 1
    bv_omega
  · have tail : (⟨src.toNat,n.toNat⟩ : MemoryRegion).HasBytes m (remainderBytes msg) := by
      refine ⟨(remainderBytes_size msg).trans len.symm, fun i => ?_⟩
      have hi : i.val < msg.size % 64 := (remainderBytes_size msg) ▸ i.isLt
      have hb := original.2 ⟨full+i.val, by dsimp only [full]; omega⟩
      change m[BitVec.ofNat 64 ((s.regValue .rsi).toNat + (full + i.val))]? = _ at hb
      have iExtract : i.val < (msg.extract full msg.size).size := i.isLt
      change m[BitVec.ofNat 64 (src.toNat + i.val)]? =
        some ((msg.extract full msg.size)[i.val]'iExtract)
      rw [srcNat, Nat.add_assoc, ByteArray.getElem_extract]
      exact hb
    rw [copy, ← len]
    exact Sec1.Wrapper.Copy.memCopy_hasBytes (by omega) tail

end K256.Proofs.Verify.Hash.Update
