import K256.Proofs.Common.Image
import K256.Proofs.Common.Refine.Lemma.Region

namespace K256.Proofs.Common

open K256.Spec.Program Prelude X86 X86.Machine X86Proofs K256.Proofs.Refine

theorem signatureBuffers {initial : RamState} {bytes : ByteArray}
    (call : ValidCall signatureFromSlice initial [bytes]) (size : bytes.size = 64) :
    let src := initial.regValue .rsi
    let dst := initial.regValue .rdi
    let stack := Stack.region initial signatureFromSlice.minStackBytes
    Readable initial.external src 64 ∧ Writable Extracted.programImage initial.external dst 64 ∧
    Outside [stack] src 64 ∧ Outside [stack] dst 64 ∧
    Outside [outputRegion signatureFromSlice initial] src 64 := by
  let input := registerRegion initial .rsi bytes.size
  let output := outputRegion signatureFromSlice initial
  let stack := Stack.region initial signatureFromSlice.minStackBytes
  have hi : ValidInput initial input bytes := call.inputsInMemory.1
  have ho : ValidOutput initial output := call.outputInMemory rfl
  have sep : MemorySeparation [output, stack] [input] := call.separation
  have srcRead := Readable.of_hasBytes hi.2.2 hi.2.1
  change Readable initial.external (BitVec.ofNat 64 (initial.regValue .rsi).toNat) bytes.size at srcRead
  have hr : Readable initial.external (initial.regValue .rsi) 64 := by
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, size] using srcRead
  have hw : Writable Extracted.programImage initial.external (initial.regValue .rdi) 64 := by
    apply Writable.of_avoids ho.2.1 ho.2.2 (sep.2 output List.mem_cons_self).1
    · exact fun x hx => Or.inl ⟨x.2, programSections_fetchByte_of_mem hx⟩
    · intro b hb
      have h := not_pageTableEntriesApart_frames hb
      exact Or.inr (contains_iff.mpr (by simp only [pageTables]; omega))
    · exact Nat.le_refl _
    · exact Nat.le_refl _
    · decide
  have ip : 0 < input.size := by change 0 < bytes.size; omega
  have op : 0 < output.size := by change 0 < 64; decide
  have sp : 0 < stack.size := by
    change 0 < (initial.regValue .rsp).toNat + 8 - ((initial.regValue .rsp).toNat - _)
    omega
  have apart {r a : MemoryRegion} (h : r.Disjoint a) (rp : 0 < r.size) (ap : 0 < a.size)
      (low : a.Bounded) (reg : Syntax.Reg) (start : a.start = (initial.regValue reg).toNat) :
      Outside [r] (initial.regValue reg) a.size := by
    refine ⟨?_, ?_⟩
    · change a.start + a.size < 2^32 at low
      rw [← start]
      omega
    · intro x hx
      obtain rfl := List.mem_singleton.mp hx
      rw [← start]
      exact (apart_of_disjoint h rp ap).symm
  have hs : stack ∈ [output, stack] := by simp
  have hi' : input ∈ [input] := List.mem_cons_self
  have so := List.pairwise_cons.mp sep.1 |>.1 stack List.mem_cons_self
  have ds : stack.Disjoint output := fun x h₁ h₂ => so x h₂ h₁
  have inputSize : input.size = 64 := size
  exact ⟨hr, hw, inputSize ▸ apart ((sep.2 stack hs).2 input hi') sp ip hi.2.1 .rsi rfl,
    apart ds sp op ho.2.1 .rdi rfl,
    inputSize ▸ apart ((sep.2 output List.mem_cons_self).2 input hi') op ip hi.2.1 .rsi rfl⟩

end K256.Proofs.Common
