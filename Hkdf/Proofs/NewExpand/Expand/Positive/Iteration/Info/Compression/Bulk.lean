import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Info.Compression.Control
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Info.Compression.Residual
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Info.Compression.Copy
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Info.Compression.Input
import Hkdf.Proofs.Common.Streaming

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand.Info

open Hkdf.Spec.Program Hkdf.Proofs.Program Hkdf.Proofs.Common
open Hkdf.Proofs.Common.CallFrame Hkdf.Proofs.Common.Machine Hkdf.Proofs.Common.SHA256
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

private theorem bulkCompression [Bindings] {entry s : RamState} {boundary : ReturnBoundary}
    {key info : ByteArray} {ptr old : BitVec 64} {length offset count : Nat} {hash : Array UInt32}
    (pre : ExpandPre entry boundary key info ptr length) (pos : 0 < length) (limit : length ≤ 8160)
    (saved : SavedFrame entry s boundary length)
    (fit : offset + 64 * count ≤ info.size)
    (pc : s.RIP = if count = 0 then 0x10f7ae else 0x10f796)
    (source : s.regValue .rbx = ptr + BitVec.ofNat 64 offset)
    (countArg : s.regValue .rdx = BitVec.ofNat 64 count)
    (words : HashStateAt s (stackPtr s + 336) hash)
    (blocks : loadBytes s.external (stackPtr s + 368) 8 = .ok old) :
    ∃ t, SavedFrame entry t boundary length ∧ (∃ fuel, Advances boundary fuel s t) ∧
      t.RIP = 0x10f7ae ∧ CalleeSavedRegistersUnchanged s t ∧
      MemoryWriteFrame s t (longRegions s) ∧
      HashStateAt t (stackPtr s + 336)
        (compressBlocks hash (info.extract offset (offset + 64 * count))) ∧
      loadBytes t.external (stackPtr s + 368) 8 = .ok (old + BitVec.ofNat 64 count) := by
  by_cases zero : count = 0
  · subst count
    refine ⟨s, saved, ⟨0, (advances_zero _ _ _).mpr rfl⟩, by simpa using pc, fun _ _ ↦ rfl,
      memoryWriteFrame_refl _ _, ?_, by simpa using blocks⟩
    simpa [compressBlocks, compressBlocksFrom] using words
  have addr : stackPtr s + 368 = stackPtr entry - BitVec.ofNat 64 168 := by
    rw [show stackPtr s = stackPtr entry - 536 from saved.sp]
    bv_omega
  have writable : MemWritable s (stackPtr s + 368) 8 := by
    rw [addr]
    exact stack_writable8 pre.call.stack pre.call.stackAvoid saved.allocated (by decide) (by decide)
  have apart : RangeApart (stackPtr s + 368) 8 0x10f796 19 := by
    rw [addr]
    exact stack_codeApart pre.call.stack (fun a ha h ↦ pre.call.stackAvoid a ha (.inl h))
      (offset := 168) (codeOffset := 0xf796) (by decide) (by decide) (by decide)
  obtain ⟨f, u, runU, ready, effect⟩ := bulkArguments (supportedMachine_readyToStep saved.machine)
    saved.loaded pre.call.outerBoundary (by simpa only [zero, ↓reduceIte] using pc) writable apart
  have ag : AgreesExcept [.mem (rspOf s + 368) 8, .reg 7, .reg 6, .flags, .rip] s u :=
    by simpa [bulkEffect, Effect.components] using effect.agrees
  obtain ⟨savedU, frameU⟩ := savedOfStore pre pos limit saved runU ready ag (off := 368) (n := 8)
    (by decide) (by decide) (by
      intro c hc a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl <;> first | exact ha | exact ha.elim) (by simp)
  have spU : stackPtr u = stackPtr s := savedU.sp.trans saved.sp.symm
  have bounds := workBounds pre.call.stack saved
  have srcU : u.regValue .rsi = ptr + BitVec.ofNat 64 offset :=
    (show u.regValue .rsi = s.regValue .rbx from effect.writes.2.2).trans source
  obtain ⟨bounded, allocated, disjoint, bytes⟩ := inputSlice pre pos limit savedU srcU fit
  have counted : u.regValue .rdx = BitVec.ofNat 64 count :=
    (ag.read (n := 64) (r := 2) (by simp)).trans countArg
  have dest : u.regValue .rdi = stackPtr u + 336 := by
    rw [spU]
    exact effect.writes.2.1
  have wordsU : HashStateAt u (stackPtr u + 336) hash := by
    rw [spU]
    exact hashState_of_bytes words (localAgrees bounds frameU (keep := 336) (size := 32)
      (by decide) (by decide) (by decide) (by decide))
  obtain ⟨t, savedT, ⟨g, runT⟩, ripT, abi, frameT, wordsT⟩ := compressionCall pre savedU false
    effect.rip dest counted wordsU bytes (.inr ⟨bounded, allocated, disjoint⟩)
  change MemoryWriteFrame u t (localRegions (stackPtr u) 336 32 344) at frameT
  rw [spU] at frameT wordsT
  have same := localAgrees bounds frameT (keep := 368) (size := 8)
    (by decide) (by decide) (by decide) (by decide)
  have present := stack_readable pre.call.stack savedU.allocated (offset := 168) (len := 8)
    (by decide) (by decide)
  rw [← addr] at present
  have stored : memLoad u.external (stackPtr s + 368) 64 =
      memLoad s.external (stackPtr s + 368) 64 + s.regValue .rdx := effect.writes.1
  have counter := Bytes.of_memLoad (n := 64) present.mem
  rw [stored, Memory.memLoad_of_loadBytes64 blocks, countArg] at counter
  refine ⟨t, savedT, ⟨f+g, runU.trans runT⟩, ripT, ?_,
    memoryWriteFrame_trans (widenLocal bounds frameU (by decide) (by decide) (by decide)
      (by decide) (by decide)) (widenLocal bounds frameT (by decide) (by decide) (by decide)
      (by decide) (by decide)), wordsT, (agrees_loadBytes same).trans counter.loadBytes64⟩
  intro r hr
  apply (abi.1 r hr).trans
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ag.read (n := 64) (r := 3) (by simp)
  · exact ag.read (n := 64) (r := 5) (by simp)
  · exact ag.read (n := 64) (r := 12) (by simp)
  · exact ag.read (n := 64) (r := 13) (by simp)
  · exact ag.read (n := 64) (r := 14) (by simp)
  · exact ag.read (n := 64) (r := 15) (by simp)

private theorem copyRemainder [Bindings] {entry s : RamState} {boundary : ReturnBoundary}
    {key info : ByteArray} {ptr : BitVec 64} {length offset : Nat}
    (pre : ExpandPre entry boundary key info ptr length) (pos : 0 < length) (limit : length ≤ 8160)
    (saved : SavedFrame entry s boundary length) (fits : offset ≤ info.size)
    (pc : s.RIP = 0x10f7ae) (rbx : s.regValue .rbx = ptr + BitVec.ofNat 64 offset)
    (r15 : s.regValue .r15 = BitVec.ofNat 64 (info.size - offset))
    (target : s.regValue .r12 = 0x10dd60) :
    let input := info.extract offset info.size
    ∃ t, SavedFrame entry t boundary length ∧ (∃ fuel, Advances boundary fuel s t) ∧
      t.RIP = 0x10f7de ∧ t.regValue .r12 = s.regValue .r12 ∧ t.regValue .r13 = s.regValue .r13 ∧
      MemoryWriteFrame s t (localRegions (stackPtr s) 272 64 8) ∧
      (⟨(stackPtr s + 272).toNat, input.size % 64⟩ : MemoryRegion).HasBytes t.external
        (remainderBytes input) ∧
      t.external[stackPtr s + 335]? = some (UInt8.ofNat (input.size % 64)) := by
  let input := info.extract offset info.size
  dsimp only
  have inputSize : input.size = info.size - offset := by simp [input]
  have n : (s.regValue .r15).toNat = input.size := by
    have := pre.lengthFits
    rw [r15, BitVec.toNat_ofNat, inputSize, Nat.mod_eq_of_lt (by omega)]
  have low : (s.regValue .r15).toNat < 2^32 := by
    have bound : ptr.toNat + info.size < 2^32 := (pre.infoBytes pos limit).1
    rw [n, inputSize]
    omega
  have addr : stackPtr s + 335 = stackPtr entry - BitVec.ofNat 64 201 := by
    rw [show stackPtr s = stackPtr entry - 536 from saved.sp]
    bv_omega
  have writable : MemWritable s (stackPtr s + 335) 1 := by
    rw [addr]
    exact stack_writable1 pre.call.stack pre.call.stackAvoid saved.allocated (by decide)
  have apart : RangeApart (stackPtr s + 335) 1 0x10f7c5 22 := by
    rw [addr]
    exact stack_codeApart pre.call.stack (fun a ha h ↦ pre.call.stackAvoid a ha (.inl h))
      (offset := 201) (codeOffset := 0xf7c5) (by decide) (by decide) (by decide)
  obtain ⟨f, u, runU, ready, callPC, dest, source, count, _, _, _, _, index, _, _, ag⟩ :=
    residualArguments (supportedMachine_readyToStep saved.machine) saved.loaded pre.call.outerBoundary
      pc writable apart low
  rw [n] at source count index
  obtain ⟨savedU, frameU⟩ := savedOfStore pre pos limit saved runU ready ag (off := 335) (n := 1)
    (by decide) (by decide) (by
      intro c hc a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | exact ha | exact ha.elim) (by simp)
  have spU : stackPtr u = stackPtr s := savedU.sp.trans saved.sp.symm
  have destU : u.regValue .rdi = stackPtr u + 272 := by rw [spU]; exact dest
  have r12U : u.regValue .r12 = s.regValue .r12 := ag.read (n := 64) (r := 12) (by simp)
  have r13U : u.regValue .r13 = s.regValue .r13 := ag.read (n := 64) (r := 13) (by simp)
  let start := offset + 64 * (input.size / 64)
  have sourceU : u.regValue .rsi = ptr + BitVec.ofNat 64 start := by
    rw [source, rbx, BitVec.add_assoc, ← BitVec.ofNat_add]
  have endPos : start + input.size % 64 = info.size := by dsimp only [start]; omega
  obtain ⟨bounded, _, apartStack, bytes⟩ := inputSlice pre pos limit savedU sourceU (Nat.le_of_eq endPos)
  obtain ⟨t, savedT, ⟨g, runT⟩, rip, abi, mem, copied⟩ := copyCall pre savedU false callPC
    (r12U.trans target) (destOffset := 272) destU count (by decide) (by omega) bounded apartStack bytes
  have bounds := workBounds pre.call.stack saved
  have frameT := copyLocalFrame (workBounds pre.call.stack savedU) (offset := 272) destU mem
  rw [spU] at frameT
  have slice : info.extract start (start + input.size % 64) = remainderBytes input := by
    rw [endPos, remainderBytes, show input = info.extract offset info.size from rfl,
      ByteArray.extract_extract]
    change info.extract start info.size = info.extract start (min (offset + input.size) info.size)
    rw [show offset + input.size = info.size by omega, Nat.min_self]
  have addrU : u.regValue .rdi = stackPtr s + 272 := dest
  refine ⟨t, savedT, ⟨f+g,runU.trans runT⟩, rip, (abi.1 .r12 (by simp)).trans r12U,
    (abi.1 .r13 (by simp)).trans r13U, memoryWriteFrame_trans
      (widenLocal bounds frameU (by decide) (by decide) (by decide) (by decide) (by decide))
      (widenLocal bounds frameT (by decide) (by omega) (by decide) (by decide) (by decide)), ?_, ?_⟩
  · simpa only [registerRegion, addrU, slice] using copied
  · have keep := localAgrees bounds frameT (keep := 335) (size := 1)
      (by omega) (by decide) (by decide) (by omega)
    have eq := keep 0 (by decide)
    change u.external[stackPtr s + 335]? = some (UInt8.ofNat (input.size % 64)) at index
    simp only [BitVec.add_zero] at eq
    exact eq.trans index

theorem bulkInfoBlocks [Bindings] {entry s : RamState} {boundary : ReturnBoundary}
    {key info message : ByteArray} {ptr : BitVec 64} {length offset : Nat}
    (pre : ExpandPre entry boundary key info ptr length) (pos : 0 < length) (limit : length ≤ 8160)
    (saved : SavedFrame entry s boundary length) (hmac : HmacAt s (stackPtr s + 272) key message)
    (aligned : message.size % 64 = 0) (fits : offset ≤ info.size)
    (pc : s.RIP = if (info.size - offset) / 64 = 0 then 0x10f7ae else 0x10f796)
    (rbx : s.regValue .rbx = ptr + BitVec.ofNat 64 offset)
    (r15 : s.regValue .r15 = BitVec.ofNat 64 (info.size - offset))
    (rdx : s.regValue .rdx = BitVec.ofNat 64 ((info.size - offset) / 64))
    (target : s.regValue .r12 = 0x10dd60) :
    ∃ t, SavedFrame entry t boundary length ∧ (∃ fuel, Advances boundary fuel s t) ∧
      t.RIP = 0x10f7de ∧ t.regValue .r12 = s.regValue .r12 ∧ t.regValue .r13 = s.regValue .r13 ∧
      MemoryWriteFrame s t (longRegions s) ∧
      HmacAt t (stackPtr t + 272) key (message ++ info.extract offset info.size) := by
  let input := info.extract offset info.size
  let prior := HMAC.xorPad (HMAC.keyBlock key) 0x36 ++ message
  let hash := compressBlocks Hkdf.Proofs.NIST.SHA256.initialHash prior
  have size : input.size = info.size - offset := by simp [input]
  have alignedPrior : prior.size % 64 = 0 := by
    simp only [prior, ByteArray.size_append, HMAC.xorPad_keyBlock_size]
    omega
  have words : HashStateAt s (stackPtr s + 336) hash := by
    simpa only [hash, prior, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using
      hmac.inner.hashWords
  have blocks : loadBytes s.external (stackPtr s + 368) 8 = .ok (BitVec.ofNat 64 (prior.size / 64)) := by
    simpa only [prior, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using hmac.inner.blocks
  obtain ⟨u, savedU, ⟨f, runU⟩, pcU, regs, frameU, wordsU, blocksU⟩ := bulkCompression pre pos limit
    saved (offset := offset) (count := (info.size-offset)/64) (by omega) pc rbx rdx words blocks
  obtain ⟨t, savedT, ⟨g, runT⟩, pcT, r12, r13, frameT, tailT, indexT⟩ := copyRemainder pre pos limit
    savedU fits pcU ((regs _ (by simp)).trans rbx) ((regs _ (by simp)).trans r15)
    ((regs _ (by simp)).trans target)
  have spU : stackPtr u = stackPtr s := savedU.sp.trans saved.sp.symm
  have spT : stackPtr t = stackPtr s := savedT.sp.trans saved.sp.symm
  rw [spU] at frameT tailT indexT
  have bounds := workBounds pre.call.stack saved
  have frame := memoryWriteFrame_trans frameU
    (widenLocal bounds frameT (by decide) (by decide) (by decide) (by decide) (by decide))
  refine ⟨t, savedT, ⟨f + g, runU.trans runT⟩, pcT, r12.trans (regs _ (by simp)),
    r13.trans (regs _ (by simp)), frame, ?_⟩
  have full : info.extract offset (offset + 64 * ((info.size-offset)/64)) = fullBlocks input := by
    simp only [fullBlocks, size, input, ByteArray.extract_extract, Nat.add_zero]
    rw [Nat.min_eq_left (by omega)]
  have finalHash : compressBlocks Hkdf.Proofs.NIST.SHA256.initialHash (prior ++ input) =
      compressBlocks hash (fullBlocks input) := by
    rw [compressBlocks_append _ _ _ alignedPrior, compressBlocks_fullBlocks]
  have keepHash := localAgrees bounds frameT (keep := 336) (size := 32)
    (by decide) (by decide) (by decide) (by decide)
  have keepCount := localAgrees bounds frameT (keep := 368) (size := 8)
    (by decide) (by decide) (by decide) (by decide)
  have finalSize : (prior ++ input).size / 64 = prior.size / 64 + input.size / 64 := by
    rw [ByteArray.size_append]
    omega
  have remSize : (prior ++ input).size % 64 = input.size % 64 := by
    rw [ByteArray.size_append]
    omega
  rw [full] at wordsU
  rw [spT]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · change HashStateAt t (stackPtr s + 272 + 64)
      (compressBlocks Hkdf.Proofs.NIST.SHA256.initialHash
        (HMAC.xorPad (HMAC.keyBlock key) 0x36 ++ (message ++ input)))
    rw [← ByteArray.append_assoc]
    change HashStateAt t (stackPtr s + 272 + 64)
      (compressBlocks Hkdf.Proofs.NIST.SHA256.initialHash (prior ++ input))
    rw [finalHash]
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using
      hashState_of_bytes wordsU keepHash
  · rw [← ByteArray.append_assoc]
    change (⟨(stackPtr s + 272).toNat, (prior ++ input).size % 64⟩ : MemoryRegion).HasBytes
      t.external (remainderBytes (prior ++ input))
    rw [remSize, remainderBytes_append_aligned _ _ alignedPrior]
    exact tailT
  · rw [← ByteArray.append_assoc]
    change t.external[stackPtr s + 272 + 63]? = some (UInt8.ofNat ((prior ++ input).size % 64))
    rw [remSize]
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using indexT
  · rw [← ByteArray.append_assoc]
    change loadBytes t.external (stackPtr s + 272 + 96) 8 = .ok (BitVec.ofNat 64 ((prior ++ input).size / 64))
    rw [finalSize, size, BitVec.ofNat_add]
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using
      (agrees_loadBytes keepCount).trans blocksU
  · apply hashState_of_bytes hmac.outerHash
    intro i hi
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using
      localAgrees bounds frame (keep := 376) (size := 32) (by decide) (by decide) (by decide) (by decide) i hi
  · apply Eq.trans _ hmac.outerBlocks
    apply agrees_loadBytes
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using
      localAgrees bounds frame (keep := 408) (size := 8) (by decide) (by decide) (by decide) (by decide)

end Hkdf.Proofs.NewExpand.Expand.Info
