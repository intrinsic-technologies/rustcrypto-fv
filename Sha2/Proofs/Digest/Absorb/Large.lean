import Sha2.Proofs.Digest.Absorb.Execution
import Sha2.Proofs.Digest.Absorb.Memory
import Sha2.Proofs.Wrapper512.Absorb.Large.Blocks.Compression
import Sha2.Proofs.Wrapper512.Absorb.Large.Blocks.Arithmetic
import Sha2.Proofs.Wrapper512.Absorb.Arithmetic
import Sha2.Proofs.Common.Machine.MemoryFrame

set_option autoImplicit false

namespace Sha2.Proofs.Digest.Absorb

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine
  X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Wrapper512 Sha2.Proofs.Common.SHA512

set_option maxRecDepth 2048 in
theorem large [Bindings] (body : Compression.BlockCorrect)
    {v : Variant} {initial s : RamState} {data : ByteArray}
    (ctx : Context v initial #[⟨initial.regValue .rdi, data⟩] .digest)
    (input : Buffered v initial s ByteArray.empty .digest)
    (rip : s.RIP = v.pc 0xeb .digest) (large : 128 ≤ data.size)
    (source : s.regValue .rsi = initial.regValue .rdi)
    (length : s.regValue .r14 = BitVec.ofNat 64 data.size) :
    ∃ t, Buffered v initial t data .digest ∧ t.RIP = v.pc 0x143 .digest := by
  let i : Fin (#[⟨initial.regValue .rdi,data⟩] : Array Input).size := ⟨0, by simp⟩
  have bounded : data.size < 2^32 := by
    have h := (ctx.inputInMemory i).2.1
    change (initial.regValue .rdi).toNat + data.size < 2^32 at h
    omega
  have lengthNat : (s.regValue .r14).toNat = data.size := by
    rw [length, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have remBound : data.size % 128 < 128 := Nat.mod_lt _ (by decide)
  have endEq : 128 * (data.size / 128) + data.size % 128 = data.size := by omega
  obtain ⟨b,preservedB,setup⟩ := bulk_setup ctx input.toPreserved rip
  have addrHash : rspOf s + 336 = stackPtr initial - 264#64 := by
    change stackPtr s + 336 = _
    rw [input.rsp]; simp only [Form.frameBytes, BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have addrLow : rspOf s + 400 = stackPtr initial - 200#64 := by
    change stackPtr s + 400 = _
    rw [input.rsp]; simp only [Form.frameBytes, BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have addrHigh : rspOf s + 408 = stackPtr initial - 192#64 := by
    change stackPtr s + 408 = _
    rw [input.rsp]; simp only [Form.frameBytes, BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have sourceB : b.regValue .rsi = initial.regValue .rdi :=
    (setup.agrees.read (n := 64) (r := 6)
      (by simp [BulkSetup.effect, Effect.components, Write.component, Operand.component])).trans source
  have countB : b.regValue .rdx = BitVec.ofNat 64 (data.size / 128) :=
    setup.writes.2.1.trans ((Wrapper512.Absorb.block_count _).trans (by rw [lengthNat]))
  have tailB : b.regValue .r14 = BitVec.ofNat 64 (data.size % 128) :=
    setup.writes.2.2.2.1.trans ((Wrapper512.Absorb.tail_length _).trans (by rw [lengthNat]))
  have sourceTailB : b.regValue .r15 = initial.regValue .rdi + BitVec.ofNat 64 (128 * (data.size / 128)) := by
    have value : b.regValue .r15 = s.regValue .rsi + (s.regValue .r14 &&& 0x7fffffffffffff80) := setup.writes.2.2.1
    rw [value, source, BitVec.and_comm,
      Wrapper512.Absorb.Large.Blocks.full_length _ (by rw [lengthNat]; omega), lengthNat]
  have countLowB : memLoad b.external (stackPtr initial - 200#64) 64 = BitVec.ofNat 64 (data.size / 128) := by
    rw [← addrLow]
    exact setup.writes.2.2.2.2.1.trans ((Wrapper512.Absorb.block_count _).trans (by rw [lengthNat]))
  have countHighB : memLoad b.external (stackPtr initial - 192#64) 64 = 0#64 := by
    rw [← addrHigh]
    exact setup.writes.2.2.2.2.2
  have wordsB : HashStateAt b (stackPtr initial - 264#64) v.initialHash := by
    apply Wrapper512.Absorb.hashState_of_bytes (s := s)
      (by simpa only [hashPointer, hashOffset, compressBlocks, ByteArray.size_empty,
        Nat.zero_div, compressBlocksFrom] using input.hashWords)
    intro j hj
    apply setup.agrees.byte
    intro c hc covers
    simp only [BulkSetup.effect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, Nat.reduceDiv, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false, addrLow, addrHigh] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact covers.elim
    all_goals obtain ⟨k,hk,eq⟩ := covers
    · exact OffsetsApart.ne (by unfold OffsetsApart; decide +kernel : OffsetsApart (-200#64) 8 (-264#64) 64)
        (stackPtr initial) hk hj (by decide) (by simpa only [BitVec.sub_eq_add_neg] using eq.symm)
    · exact OffsetsApart.ne (by unfold OffsetsApart; decide +kernel : OffsetsApart (-192#64) 8 (-264#64) 64)
        (stackPtr initial) hk hj (by decide) (by simpa only [BitVec.sub_eq_add_neg] using eq.symm)
  obtain ⟨c,preservedC,ripC,wordsC,abiC,frameC,_,_⟩ :=
    Wrapper512.Absorb.Large.Blocks.compress_slice body ctx preservedB i
      (offset := 0) (count := data.size / 128) (by simp; omega)
      (setup.rip.trans (Variant.pc_add v 0xeb 55 .digest))
      (setup.writes.1.trans addrHash) (by simpa using sourceB) countB wordsB
  have tailC := (abiC.1 .r14 (by simp)).trans tailB
  have sourceTailC := (abiC.1 .r15 (by simp)).trans sourceTailB
  obtain ⟨d,preservedD,stored⟩ := tail_length ctx preservedC false ripC
  have addrC : rspOf c + 335 = stackPtr initial - 265#64 := by
    change stackPtr c + 335 = _
    rw [preservedC.rsp]
    simp only [Form.frameBytes, BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have frameD : AgreesExcept [.mem (stackPtr initial - 265#64) 1,.rip] c d := by
    simpa only [TailLength.effect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, Nat.reduceDiv, List.cons_append, List.nil_append,
      addrC] using stored.agrees
  have keptD (offset len : Nat)
      (apart : OffsetsApart (-265) 1 (-(BitVec.ofNat 64 offset)) len)
      (bound : 1 + len < 2^64) :=
    bytes_of_mem_frame frameD (by simp [Component.Covers]) apart bound
  have tailD : d.regValue .r14 = BitVec.ofNat 64 (data.size % 128) :=
    (frameD.read (n := 64) (r := 14) (by simp)).trans tailC
  have sourceTailD : d.regValue .r15 = initial.regValue .rdi + BitVec.ofNat 64 (128 * (data.size / 128)) :=
    (frameD.read (n := 64) (r := 15) (by simp)).trans sourceTailC
  have tailByteD : d.external[stackPtr initial - 265#64]? = some (UInt8.ofNat (data.size % 128)) := by
    have value : memLoad d.external (rspOf c + 335) 8 = (c.regValue .r14).setWidth 8 := stored.writes
    rw [addrC,tailC] at value
    have read := stack_frame_readable ctx.stack (frame := 600) (offset := 335) (len := 1)
      (s := d) (by change 600 ≤ 1152; decide) preservedD.allocated (by decide)
    have read' : MemReadable d (stackPtr initial - 265#64) 1 := by
      simpa only [stack_frame_address initial (frame := 600) (offset := 335) (by decide), Nat.reduceSub] using read
    have byte := Bytes.of_memLoad (n := 8) read'.mem 0 (by decide)
    rw [value] at byte
    simpa only [BitVec.add_zero, storedByte, Nat.mul_zero, Nat.shiftRight_zero,
      BitVec.toNat_setWidth, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : data.size % 128 < 2^64),
      Nat.mod_eq_of_lt (by omega : data.size % 128 < 2^8)] using byte
  obtain ⟨e,preservedE,copySetup⟩ := copy_setup ctx preservedD true
    (stored.rip.trans (Variant.pc_add v 0x127 8 .digest))
  have memoryE : e.external = d.external := copySetup.agrees.external
    (by simp [CopySetup.effect, Effect.components, Write.component, Operand.component, Component.Covers])
  have addrD : rspOf d + 208 = stackPtr initial - 392#64 := by
    change stackPtr d + 208 = _
    rw [preservedD.rsp]
    simp only [Form.frameBytes, BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  obtain ⟨t,copied⟩ := Wrapper512.Absorb.Copy.copy ctx preservedE .tail i
    (offset := 128 * (data.size / 128)) (position := 0) (count := data.size % 128)
    (by change 128 * (data.size / 128) + data.size % 128 ≤ data.size; omega) (by omega)
    (copySetup.rip.trans (Variant.pc_add v 0x12f 14 .digest))
    (by change e.regValue .rdi = stackPtr initial - 392#64 + 0#64; rw [BitVec.add_zero]; exact copySetup.writes.1.trans addrD)
    (copySetup.writes.2.1.trans sourceTailD) (copySetup.writes.2.2.trans tailD)
  have keptCopy (offset len : Nat) (lo : offset ≤ 600) (hi : len ≤ offset)
      (apart : offset + data.size % 128 ≤ 392) :=
    copied.bytes_unchanged ctx (by omega) (offset := offset) (len := len) lo hi (Or.inr apart)
  have counters (offset : Nat) (lo : 192 ≤ offset) (hi : offset ≤ 200)
      (apart : OffsetsApart (-265) 1 (-(BitVec.ofNat 64 offset)) 8) :
      memLoad t.external (stackPtr initial - BitVec.ofNat 64 offset) 64 =
        memLoad b.external (stackPtr initial - BitVec.ofNat 64 offset) 64 := by
    apply memLoad_congr
    intro j hj
    apply congrArg (fun byte : Option UInt8 => byte.getD 0)
    refine (keptCopy offset 8 (by omega) (by omega) (by omega) j hj).trans ?_
    rw [memoryE]
    exact (keptD offset 8 apart (by decide) j hj).trans
      (Wrapper512.Absorb.frame_bytes (output := 264) (count := 64) (reserve := 1024) ctx frameC
        (by decide) (by decide) (by decide) (by decide) (by change offset ≤ 600; omega)
        (by omega) (Or.inr (by omega)) j hj)
  refine ⟨t, ⟨copied.preserved, ?_, ?_, ?_, ?_, ?_⟩,
    copied.rip.trans (Variant.pc_add v 0x13d 6 .digest)⟩
  · apply Wrapper512.Absorb.hashState_of_bytes (s := c)
      (by
        have words : HashStateAt c (stackPtr initial - 264#64)
            (compressBlocks v.initialHash (fullBlocks data)) := by
          simpa [i, fullBlocks] using wordsC
        simpa only [compressBlocks_fullBlocks] using words)
    intro j hj
    refine (keptCopy 264 64 (by decide) (by decide) (by omega) j hj).trans ?_
    rw [memoryE]
    exact keptD 264 64 (by unfold OffsetsApart; decide +kernel) (by decide) j hj
  · have bytes := copied.bytes
    change (⟨(stackPtr initial - 392#64 + 0#64).toNat, data.size % 128⟩ : MemoryRegion).HasBytes
      t.external (data.extract (128 * (data.size / 128)) (128 * (data.size / 128) + data.size % 128)) at bytes
    simpa only [tailRegion, bufferPointer, bufferOffset, tailData, BitVec.add_zero, endEq] using bytes
  · have eq := keptCopy 265 1 (by decide) (by decide) (by omega) 0 (by decide)
    simpa only [BitVec.add_zero, memoryE, tailLengthPointer, tailLengthOffset] using eq.trans
      (by simpa only [BitVec.add_zero, memoryE] using tailByteD)
  · exact (counters 200 (by decide) (by decide) (by unfold OffsetsApart; decide +kernel)).trans countLowB
  · have high : (data.size / 128) / 2^64 = 0 := by omega
    simpa only [high, blockCountHighPointer, blockCountHighOffset] using
      (counters 192 (by decide) (by decide) (by unfold OffsetsApart; decide +kernel)).trans countHighB

end Sha2.Proofs.Digest.Absorb
