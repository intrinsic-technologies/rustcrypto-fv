import Sha2.Proofs.Common.SHA256.Finalize.Proof.Compress.Memory
import Sha2.Proofs.Wrapper.Hash.LengthEncoding

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Finalize.Compress

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

theorem last [Bindings] {L : Layout} {initial before s : RamState}
    {n reserve : Nat} {regions : Vector MemoryRegion n} {message : ByteArray} {hash : Array UInt32}
    (ctx : Context L initial regions reserve) (input : LengthReady L initial before s regions message hash) :
    ∃ t, HashAt L initial before t regions hash ∧ t.RIP = L.lastLower ∧
      (⟨(L.buffer (L.sp initial)).toNat,64⟩ : MemoryRegion).HasBytes t.external (finalBlock message) ∧
      memLoad t.external (L.scratch (L.sp initial)+56) 64 =
        memLoad t.external (L.buffer (L.sp initial)+56) 64 := by
  have pre : LastHead.Pre L.lastHead L.variant s := by
    refine ⟨input.rip,?_,?_,?_,?_⟩
    all_goals rw [show rspOf s = L.sp initial from input.rsp]
    · exact ctx.writable input.state (by have := ctx.wf.bufferFits; omega) (by decide)
    · exact ctx.writable input.state (by have := ctx.wf.scratchFits; omega) (by decide)
    · exact ctx.codeApart (by have := ctx.wf.bufferFits; omega) (ctx.code.inside .lastHead)
    · exact ctx.codeApart (by have := ctx.wf.scratchFits; omega) (ctx.code.inside .lastHead)
  obtain ⟨_,t,run,ready,_,effect⟩ := ctx.blocks.lastHead s
    (supportedMachine_readyToStep input.state.machine) (ctx.code.loaded .lastHead s input.state.loaded) pre
  have frame : AgreesExcept [.mem (L.sp initial+BitVec.ofNat 64 (L.variant.buffer.value+56)) 8,
      .mem (L.sp initial+BitVec.ofNat 64 (L.variant.scratch+56)) 8,.rip] s t := by
    simpa only [LastHead.effect,Effect.components,List.map_cons,List.map_nil,List.cons_append,
      List.nil_append,Write.component,Operand.component,show rspOf s = L.sp initial from input.rsp] using effect.agrees
  have writes : Writes L (L.sp initial) [.mem (L.sp initial+BitVec.ofNat 64 (L.variant.buffer.value+56)) 8,
      .mem (L.sp initial+BitVec.ofNat 64 (L.variant.scratch+56)) 8,.rip] := by
    intro c hc a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact .inl (buffer_cover (by decide) ha)
    · exact .inr (scratch_cover (by decide) ha)
    · exact ha.elim
  have state := preserve ctx input.toHashAt run ready frame writes
    (by intro r h0 h1; simp) (by simp)
  have kept : ∀ i < 56, t.external[L.buffer (L.sp initial)+BitVec.ofNat 64 i]? =
      s.external[L.buffer (L.sp initial)+BitVec.ofNat 64 i]? := by
    intro i hi
    apply frame.byte
    intro c hc ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl
    · obtain ⟨j,hj,he⟩ := ha
      have apart : OffsetsApart (BitVec.ofNat 64 (L.variant.buffer.value+56)) 8
          (BitVec.ofNat 64 L.variant.buffer.value) 56 := by
        cases L.variant <;> unfold OffsetsApart <;> decide +kernel
      apply apart.ne (L.sp initial) hj hi (by decide)
      simpa only [Layout.buffer] using he.symm
    · obtain ⟨j,hj,he⟩ := ha
      have apart : OffsetsApart (BitVec.ofNat 64 (L.variant.scratch+56)) 8
          (BitVec.ofNat 64 L.variant.buffer.value) 56 := by
        cases L.variant <;> unfold OffsetsApart <;> decide +kernel
      apply apart.ne (L.sp initial) hj hi (by decide)
      simpa only [Layout.buffer] using he.symm
    · exact ha.elim
  have sourceWord : memLoad t.external (L.buffer (L.sp initial)+56) 64 =
      Common.Instructions.bswap64 (BitVec.ofNat 64 (8*message.size)) := by
    have word := effect.writes.1
    change memLoad t.external (rspOf s + BitVec.ofNat 64 (L.variant.buffer.value+56)) 64 =
      (.reg L.variant.registers.tail : Operand 64).read s at word
    simpa only [Layout.buffer,show rspOf s = L.sp initial from input.rsp,input.lengthWord,
      BitVec.ofNat_add,BitVec.add_assoc,BitVec.ofNat_eq_ofNat] using word
  have destinationWord : memLoad t.external (L.scratch (L.sp initial)+56) 64 =
      Common.Instructions.bswap64 (BitVec.ofNat 64 (8*message.size)) := by
    have word := effect.writes.2
    change memLoad t.external (rspOf s + BitVec.ofNat 64 (L.variant.scratch+56)) 64 =
      (.reg L.variant.registers.tail : Operand 64).read s at word
    simpa only [Layout.scratch,show rspOf s = L.sp initial from input.rsp,input.lengthWord,
      BitVec.ofNat_add,BitVec.add_assoc,BitVec.ofNat_eq_ofNat] using word
  have prefixSize : (finalPrefix message).size = 56 := input.prefixBytes.1
  have blockSize : (finalBlock message).size = 64 := by
    simp only [finalBlock,Wrapper.Hash.Finalize.finalBlock,ByteArray.size_append,prefixSize,
      Common.Encoding.natToOctets_size]
  refine ⟨t,state,effect.rip.trans ctx.flow.lastHead,⟨blockSize,?_⟩,destinationWord.trans sourceWord.symm⟩
  intro i
  have hi : i.val < 64 := by have := i.isLt; omega
  have hi' : i.val < (finalPrefix message ++ NIST.Encoding.natToOctets 8 (8*message.size)).size := by
    simpa only [finalBlock,Wrapper.Hash.Finalize.finalBlock] using i.isLt
  change t.external[BitVec.ofNat 64 ((L.buffer (L.sp initial)).toNat+i.val)]? =
    some ((finalPrefix message ++ NIST.Encoding.natToOctets 8 (8*message.size))[i.val]'hi')
  rw [BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  by_cases low : i.val < 56
  · rw [ByteArray.getElem_append_left (by omega)]
    apply (kept i.val low).trans
    simpa only [BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq] using input.prefixBytes.2 ⟨i.val,by omega⟩
  · rw [ByteArray.getElem_append_right (by omega)]
    have readable : MemReadable t (L.buffer (L.sp initial)+56) 8 := by
      simpa only [Layout.buffer,BitVec.ofNat_add,BitVec.add_assoc,BitVec.ofNat_eq_ofNat] using
        ctx.readable state.state (offset := L.variant.buffer.value+56) (len := 8)
          (by have := ctx.wf.bufferFits; omega)
    have stored := Bytes.of_memLoad (n := 64) readable.mem
    rw [sourceWord] at stored
    have byte := stored (i.val-56) (by omega)
    rw [Wrapper.Hash.bswap64_ofNat_storedByte _ (by omega)] at byte
    have address : L.buffer (L.sp initial)+BitVec.ofNat 64 i.val =
        L.buffer (L.sp initial)+56+BitVec.ofNat 64 (i.val-56) := by
      rw [BitVec.add_assoc]
      change _ = L.buffer (L.sp initial)+(BitVec.ofNat 64 56+BitVec.ofNat 64 (i.val-56))
      rw [← BitVec.ofNat_add]
      congr 2
      omega
    rw [address]
    simpa only [prefixSize,BitVec.ofNat_eq_ofNat] using byte

end Sha2.Proofs.Common.SHA256.Finalize.Compress
