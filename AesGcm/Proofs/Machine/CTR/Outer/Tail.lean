import AesGcm.Proofs.Machine.CTR.BatchInput
import AesGcm.Proofs.Machine.CTR.Outer.Invariant
import AesGcm.Proofs.Machine.CTR.TailSetup
import AesGcm.Proofs.Machine.CTR.TailCounter
import AesGcm.Proofs.Machine.CTR.TailCopy
import AesGcm.Proofs.Machine.CTR.Return
import AesGcm.Proofs.Machine.Runtime.Root.Memory

namespace AesGcm.Proofs.Machine.CTR

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open Standards.NIST
open Standards.NIST.GCM AesGcm.Spec.GCM AesGcm.Proofs.Machine.Runtime

private theorem tail_sub_disjoint {a b c d : MemoryRegion} (h : a.Disjoint b)
    (ac : a.start ≤ c.start) (ca : c.start + c.size ≤ a.start + a.size)
    (bd : b.start ≤ d.start) (db : d.start + d.size ≤ b.start + b.size) : c.Disjoint d := by
  intro x hx hy
  apply h x _ _
  · change c.start ≤ x ∧ x < c.start + c.size at hx
    exact ⟨by omega, by omega⟩
  · change d.start ≤ x ∧ x < d.start + d.size at hy
    exact ⟨by omega, by omega⟩

private theorem tail_payload (v : AES.Variant) (key : Vector UInt8 v.keyBytes)
    (icb : Vector Bool 128) (input : ByteArray) (before after : Ram)
    (source destination sp : BitVec 64) (offset n : Nat)
    (len : input.size = offset + 16 * n) (off16 : offset % 16 = 0)
    (firstBytes : (span destination offset).HasBytes after
      ((byteArrayOfBits (GCTR (forwardCipher v key) icb (bitsOfByteArray input))).extract 0 offset))
    (srcBytes : (span (source + BitVec.ofNat 64 offset) (16 * n)).HasBytes before
      (input.extract offset input.size))
    (stream : ∀ j < 16 * n, memByte before (sp + 8 + BitVec.ofNat 64 j) =
      (AES.cipher v key (bytesOfBits (Nat.repeat (inc 32) ((offset + j) / 16) icb)))[j % 16]'(by omega))
    (bytes : ∀ j < 16 * n, after[destination + BitVec.ofNat 64 offset + BitVec.ofNat 64 j]? =
      some (memByte before (source + BitVec.ofNat 64 offset + BitVec.ofNat 64 j) ^^^
        memByte before (sp + 8 + BitVec.ofNat 64 j))) :
    (span destination input.size).HasBytes after
      (byteArrayOfBits (GCTR (forwardCipher v key) icb (bitsOfByteArray input))) := by
  let result := byteArrayOfBits (GCTR (forwardCipher v key) icb (bitsOfByteArray input))
  let srcTail := source + BitVec.ofNat 64 offset
  let dstTail := destination + BitVec.ofNat 64 offset
  have rsize : result.size = input.size := byteArrayOfBits_size _
  change (span destination offset).HasBytes after (result.extract 0 offset) at firstBytes
  change (span destination input.size).HasBytes after result
  refine ⟨rsize, ?_⟩
  intro i
  have hi := i.isLt
  by_cases hpre : i.val < offset
  · have plen : (result.extract 0 offset).size = offset := firstBytes.1
    have hb := firstBytes.2 ⟨i.val, by omega⟩
    change after[BitVec.ofNat 64 (destination.toNat + i.val)]? =
      some ((result.extract 0 offset).data[i.val]'(by change i.val < (result.extract 0 offset).size; omega)) at hb
    change after[BitVec.ofNat 64 (destination.toNat + i.val)]? = some result.data[i.val]
    simpa only [ByteArray.data_extract, Array.getElem_extract, Nat.zero_add] using hb
  · let j := i.val - offset
    have hj : j < 16 * n := by dsimp [j]; omega
    have ij : offset + j = i.val := by dsimp [j]; omega
    have ijmod : i.val % 16 = j % 16 := by omega
    have hlen : (input.extract offset input.size).size = (16 * n) := srcBytes.1
    have sb := srcBytes.2 ⟨j, by omega⟩
    have sourceByte : memByte before (srcTail + BitVec.ofNat 64 j) = input[i.val]'(by omega) := by
      change before[BitVec.ofNat 64 (srcTail.toNat + j)]? =
        some ((input.extract offset input.size).data[j]'(by change j < (input.extract offset input.size).size; omega)) at sb
      simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, ByteArray.data_extract,
        Array.getElem_extract, ij] at sb
      change (before[srcTail + BitVec.ofNat 64 j]?).getD 0 = _
      rw [sb]; rfl
    have db := bytes j hj
    rw [sourceByte, stream j hj] at db
    have atDest : dstTail + BitVec.ofNat 64 j = BitVec.ofNat 64 (destination.toNat + i.val) := by
      simp only [dstTail, BitVec.add_assoc, ← BitVec.ofNat_add, ij]
      rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rw [atDest] at db
    change after[BitVec.ofNat 64 (destination.toNat + i.val)]? = some result.data[i.val]
    have cipherByte := gctr_cipher_byte v key icb input i.val (by omega)
      _ (bitsOfBytes_bytesOfBits (k := 16) (Nat.repeat (inc 32) (i.val / 16) icb)).symm
    rw [db]
    change _ = some ((bytesOfBits (GCTR (forwardCipher v key) icb (bitsOfByteArray input)))[i.val]'(by omega))
    rw [cipherByte]
    change some (input[i.val] ^^^
      (AES.cipher v key (bytesOfBits (Nat.repeat (inc 32) ((offset + j) / 16) icb)))[j % 16]) = _
    simp only [ij, ijmod]

set_option maxHeartbeats 800000 in
theorem crypt_tail (use256 : Bool) (code : CodeMap) (fr : Activation)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (key : Vector UInt8 ((AES16.variant use256).keyBytes)) (input : ByteArray)
    (blockCount : Nat) (hsize : input.size = 16 * blockCount)
    (schedule counter source destination : BitVec 64)
    (exit : LIR.lifted.Location)
    (hExit : OuterExit use256 code fr key input blockCount schedule counter source destination exit) :
    ∃ next : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches ⟨exit, []⟩ ⟨next, []⟩ ∧
      next.label = (if use256 then .l109961 else .l1084c1) ∧
      ∃ output, LIR.program.runBlock (dialect code) next = .returned output ∧
        output.store = next.store ∧
        output.tag = some ⟨64, fr.ret⟩ ∧
        Atom.All code output.values output.store
          ((if use256 then LIR.Fn1084e0.frameInfo else LIR.Fn107050.frameInfo).doneAtoms fr) ∧
        GPRsTyped output.values ∧
        memLoad output.store (counter + 16) 32 = memLoad fr.original (counter + 16) 32 + BitVec.ofNat 32 blockCount ∧
        (span destination input.size).HasBytes output.store
          (byteArrayOfBits (GCTR (AesGcm.Spec.GCM.forwardCipher (AES16.variant use256) key)
            (bitsOfBytes (initialCounterBlock fr.original counter))
            (bitsOfByteArray input))) ∧
        RamWriteFrame fr.original output.store
          [fr.region, span (counter + 16) 4, span destination input.size] := by
  let sp := outerStackPointer fr use256
  let win : Nat := if use256 then 2688 else 2160
  let offset : Nat := input.size - input.size % 64
  let n := blockCount % 4
  let lower := fr.rsp - (if use256 then 2688 else 2160)
  let work := span lower (if use256 then 648 else 632)
  let ctr := span (counter + 16) 4
  let dst := span destination input.size
  let result := byteArrayOfBits (GCTR (forwardCipher (AES16.variant use256) key)
    (bitsOfBytes (initialCounterBlock fr.original counter)) (bitsOfByteArray input))
  have rsize : result.size = input.size := byteArrayOfBits_size _
  have len : input.size = offset + 16 * n := by dsimp [offset, n]; omega
  have remainderSize : input.size % 64 = 16 * n := by dsimp [n]; omega
  have off16 : offset % 16 = 0 := by dsimp [offset]; omega
  have frameAtoms : Atom.All code exit.arguments exit.store
      (if use256 then LIR.Fn1084e0.frameAt .l109509 fr else LIR.Fn107050.frameAt .l10805f fr) := by
    have f := hExit.frame
    cases use256 <;> simpa only [cryptFrameAt, hExit.label, Bool.false_eq_true, ↓reduceIte] using f
  have stackWrite : Writable code exit.store lower win ∧ fr.low.toNat + win ≤ fr.rsp.toNat ∧ Readable exit.store fr.rsp 8 := by
    cases use256 <;> obtain
      ⟨_, _, _, _, _, _, _, _, _, _, _, r, _, _, w, h, _⟩ := frameAtoms <;> exact ⟨w, h, r⟩
  obtain ⟨stackWrite, room, returnRead⟩ := stackWrite
  have stackPointerNat : sp.toNat = fr.rsp.toNat - (if use256 then 2312 else 1800) := by
    cases use256 <;> apply stack_sub_toNat fr room <;> decide
  have stackBaseNat : lower.toNat = fr.rsp.toNat - win := by
    cases use256 <;> exact stack_sub_toNat fr room (Nat.le_refl _)
  have sizes : win = (if use256 then 2312 else 1800) + (if use256 then 376 else 360) ∧
      (if use256 then 648 else 632) = (if use256 then 376 else 360) + 272 ∧
      (1800 : Nat) ≤ (if use256 then 2312 else 1800) ∧ 360 ≤ (if use256 then 376 else 360) := by
    cases use256 <;> decide
  obtain ⟨wsize, workSize, spSize, scratchSize⟩ := sizes
  have stackLow := returnRead.low
  have destW := hExit.toOuterState.destination_write
  have sourceR := hExit.toOuterState.source_read
  have counterW := hExit.toOuterState.counter_write
  have destinationLow := destW.readable.low
  have sourceLow := sourceR.low
  have counterLow := counterW.readable.low
  have cn : (counter + 16).toNat = counter.toNat + 16 := toNat_add_ofNat counter 16 (by omega)
  have sp8 : (sp + 8).toNat = sp.toNat + 8 := toNat_add_ofNat sp 8 (by omega)
  have sp120 : (sp + 120).toNat = sp.toNat + 120 := toNat_add_ofNat sp 120 (by omega)
  have savedRegistersNat : (fr.rsp - 48).toNat = fr.rsp.toNat - 48 := stack_sub_toNat fr room (n := 48) (by omega)
  have dn := toNat_add_ofNat destination offset (by omega)
  have sn := toNat_add_ofNat source offset (by omega)
  have stackSep : ∀ region ∈ [span fr.rdi 8, span fr.rsi 32,
      span schedule (16 * ((AES16.variant use256).Nr + 1)), span counter 20,
      span source input.size, span destination input.size], (callStack fr).Disjoint region :=
    atomsAll_mem (atom := .fact _) hExit.outer (by simp only [outerAtoms, List.mem_cons, true_or, or_true])
  have counterSep : ∀ region ∈ [span fr.rdi 8, span fr.rsi 32,
      span schedule (16 * ((AES16.variant use256).Nr + 1)), span source input.size,
      span destination input.size], (span counter 20).Disjoint region :=
    atomsAll_mem (atom := .fact _) hExit.outer (by simp only [outerAtoms, List.mem_cons, true_or, or_true])
  have stackCounter : (callStack fr).Disjoint (span counter 20) := stackSep _ (by simp)
  have stackDestination : (callStack fr).Disjoint dst := stackSep _ (by simp [dst])
  have stackSource : (callStack fr).Disjoint (span source input.size) := stackSep _ (by simp)
  have counterSource : (span counter 20).Disjoint (span source input.size) := counterSep _ (by simp)
  have counterDestination : (span counter 20).Disjoint dst := counterSep _ (by simp [dst])
  have retDisjoint (r : MemoryRegion) (hr : r ∈ [work, ctr, dst]) :
      (span (fr.rsp - 48) 56).Disjoint r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · intro x h₁ h₂
      simp only [MemoryRegion.Contains, span, work] at h₁ h₂
      omega
    · apply tail_sub_disjoint stackCounter <;> simp only [span, callStack, ctr] <;> omega
    · apply tail_sub_disjoint stackDestination <;> simp only [span, callStack, dst] <;> omega
  have finalFrame : RegionsWithin [work, ctr, dst] [fr.region, ctr, dst] := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · refine ⟨fr.region, by simp, ?_, ?_⟩ <;> simp only [work, span, Activation.region] <;> omega
    · exact ⟨ctr, by simp, Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨dst, by simp, Nat.le_refl _, Nat.le_refl _⟩
  suffices tail : ∃ next : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches ⟨exit,[]⟩ ⟨next,[]⟩ ∧
      next.label = (if use256 then .l109961 else .l1084c1) ∧
      GPRsTyped next.arguments ∧
      (∀ r : Fin 53, r.val ∈ [4, 22, 39, 50, 51] → next.arguments[r] = exit.arguments[r]) ∧
      RamWriteFrame exit.store next.store [work, ctr, dst] ∧
      memLoad next.store (counter + 16) 32 = memLoad fr.original (counter + 16) 32 + BitVec.ofNat 32 blockCount ∧
      dst.HasBytes next.store result by
    obtain ⟨next, hr, hl, ht, hk, hf, hc, hb⟩ := tail
    obtain ⟨o, run, mem, tag, done, types⟩ := return_of_tail use256 code fr _ _ _ _ frameAtoms _ hf retDisjoint hk ht
    have run' : LIR.program.runBlock (dialect code) next = .returned o := by
      cases next with | mk l a m => dsimp only at hl; subst l; exact run
    exact ⟨next, hr, hl, o, run', mem, tag, done, types, mem ▸ hc, mem ▸ hb, mem ▸ hExit.written.trans hf finalFrame⟩
  by_cases hz : blockCount % 4 = 0
  · have zeroWord : BitVec.ofNat 64 (blockCount % 4) = 0 := by simp [hz]
    have rem : memLoad exit.store (sp + 232) 64 = BitVec.ofNat 64 (blockCount % 4) :=
      atomsAll_mem (atom := .mem (sp + 232) 64 _) hExit.outer (by simp only [sp, outerAtoms, List.mem_cons, true_or, or_true])
    obtain ⟨next, run, hl, _, _, hk, ht, cf⟩ := tail_clear use256 code hcode _ _ sp source
      (BitVec.ofNat 64 (blockCount % 4)) hExit.typed (congrArg (Value.get 64) hExit.toOuterState.stackPointer)
      (stackWrite.sub (by change _ ≤ (sp + 8).toNat; omega)
        (by change (sp + 8).toNat + 240 ≤ _; omega))
      hExit.toOuterState.source_word rem
    have reach : (LIR.program.sem (dialect code)).Reaches ⟨exit,[]⟩ ⟨next,[]⟩ := by
      apply Semantics.Reaches.single
      change (LIR.program.runBlock (dialect code) exit).next (dialect code) [] = _
      have e := hExit.label
      have run' : LIR.program.runBlock (dialect code) exit = .jump next := by
        cases exit with | mk l a m => dsimp only at e; subst l; exact run
      exact congrArg (fun t => t.next (dialect code) []) run'
    refine ⟨next, reach, (by rw [ite_eq_left zeroWord] at hl; exact hl), ht,
      (fun r hr => hk r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; grind)), ?_, ?_, ?_⟩
    · apply (RamWriteFrame.refl _ _).trans cf
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      refine ⟨work, by simp, ?_, ?_⟩ <;> simp only [work, span] <;> omega
    · have countEq : 4 * (blockCount / 4) = blockCount := by omega
      rw [← countEq, ← hExit.counter_value]
      apply memLoad_eq_of_disjoint cf (by simp only [Nat.reduceDiv]; omega)
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      intro x hx hy
      apply stackCounter x _ _
      · simp only [MemoryRegion.Contains, callStack, span] at hy ⊢
        omega
      · simp only [MemoryRegion.Contains, span] at hx ⊢
        omega
    · have off : offset = input.size := by dsimp [offset]; omega
      have hp : (span destination offset).HasBytes exit.store (result.extract 0 offset) := hExit.destination_prefix
      have hr : result.extract 0 offset = result := by
        apply ByteArray.ext
        rw [off, ← rsize]
        rw [ByteArray.data_extract]
        exact Array.extract_size
      rw [hr, off] at hp
      apply hasBytes_of_frame cf hp (by change destination.toNat + input.size ≤ _; omega)
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      intro x hx hy
      apply stackDestination x _ hx
      simp only [MemoryRegion.Contains, callStack, span] at hy ⊢
      omega
  · obtain ⟨mid, reach, lab, tm, keep, sourceReg, destSlot, countSlot, finalCounter, keyFrame, stream⟩ :=
      tail_keystream use256 code fr hcode key input blockCount hsize hz schedule counter source destination exit hExit
    change RamWriteFrame exit.store mid.store [work, ctr] at keyFrame
    let srcTail := source + BitVec.ofNat 64 offset
    let dstTail := destination + BitVec.ofNat 64 offset
    have ms : Readable mid.store srcTail (16 * n) := (sourceR.sub (by dsimp only [srcTail]; omega)
      (by dsimp only [srcTail]; omega)).of_frame keyFrame
    have md : Writable code mid.store dstTail (16 * n) := (destW.sub (by dsimp only [dstTail]; omega)
      (by dsimp only [dstTail]; omega)).of_frame keyFrame
    have hstk : Writable code mid.store sp 240 := (stackWrite.sub (by omega) (by omega)).of_frame keyFrame
    have alias : source = destination ∨ (span source input.size).Disjoint dst :=
      atomsAll_mem (atom := .fact _) hExit.outer (by simp only [dst, outerAtoms, List.mem_cons, true_or, or_true])
    have tailAlias : srcTail = dstTail ∨ (span srcTail (16 * n)).Disjoint (span dstTail (16 * n)) := by
      rcases alias with h | h
      · exact Or.inl (congrArg (· + BitVec.ofNat 64 offset) h)
      · right
        apply tail_sub_disjoint h <;> simp only [srcTail, dstTail, dst, span] <;> omega
    obtain ⟨next, go, hl, ht, hk, xorFrame, bytes⟩ := tail_xor use256 code hcode mid sp srcTail dstTail n
      (by dsimp [n]; omega) lab tm
      (congrArg (Value.get 64) ((keep 4 (by decide)).trans hExit.toOuterState.stackPointer))
      sourceReg destSlot countSlot hstk ms md
      (by apply tail_sub_disjoint stackSource <;> simp only [span, callStack, srcTail] <;> omega)
      (by apply tail_sub_disjoint stackDestination <;> simp only [span, callStack, dstTail, dst] <;> omega)
      tailAlias
    have cf : RamWriteFrame exit.store next.store [work, ctr, span dstTail (16 * n)] := by
      have keyFrame' : RamWriteFrame exit.store mid.store [work, ctr, span dstTail (16 * n)] := by
        apply (RamWriteFrame.refl _ _).trans keyFrame
        intro r hr
        exact ⟨r, by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; grind,
          Nat.le_refl _, Nat.le_refl _⟩
      apply keyFrame'.trans xorFrame
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · refine ⟨work, by simp, ?_, ?_⟩ <;> simp only [work, span] <;> omega
      · exact ⟨_, by simp, Nat.le_refl _, Nat.le_refl _⟩
    refine ⟨next, reach.trans go, hl, ht, fun r h => (hk r h).trans (keep r h), ?_, ?_, ?_⟩
    · apply (RamWriteFrame.refl _ _).trans cf
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨work, by simp, Nat.le_refl _, Nat.le_refl _⟩
      · exact ⟨ctr, by simp, Nat.le_refl _, Nat.le_refl _⟩
      · refine ⟨dst, by simp, ?_, ?_⟩ <;> simp only [dst, dstTail, span] <;> omega
    · refine Eq.trans (memLoad_eq_of_disjoint xorFrame (by simp only [Nat.reduceDiv]; omega) ?_) finalCounter
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · intro x hc hs
        apply stackCounter x _ _
        · simp only [MemoryRegion.Contains, span, callStack] at hs ⊢; omega
        · simp only [MemoryRegion.Contains, span] at hc ⊢; omega
      · apply tail_sub_disjoint counterDestination <;> simp only [dstTail, dst, span, Nat.reduceDiv] <;> omega
    · have prefixBytes : (span destination offset).HasBytes exit.store (result.extract 0 offset) := hExit.destination_prefix
      have firstBytes := hasBytes_of_frame cf prefixBytes (by change destination.toNat + offset ≤ _; omega) (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · intro x hx hy
          apply stackDestination x _ _
          · simp only [MemoryRegion.Contains, callStack, work, span] at hy ⊢; omega
          · simp only [MemoryRegion.Contains, dst, span] at hx ⊢; omega
        · intro x hx hy
          apply counterDestination x _ _
          · simp only [MemoryRegion.Contains, ctr, span] at hy ⊢; omega
          · simp only [MemoryRegion.Contains, dst, span] at hx ⊢; omega
        · intro x hx hy
          simp only [MemoryRegion.Contains, dstTail, span] at hx hy
          omega)
      have srcBytes : (span srcTail (input.size % 64)).HasBytes mid.store (input.extract offset input.size) := by
        apply hasBytes_of_frame keyFrame hExit.source_bytes (by change srcTail.toNat + input.size % 64 ≤ _; dsimp only [srcTail]; omega)
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · intro x hx hy
          apply stackSource x _ _
          · simp only [MemoryRegion.Contains, callStack, work, span] at hy ⊢; omega
          · change srcTail.toNat ≤ x ∧ x < srcTail.toNat + input.size % 64 at hx
            simp only [MemoryRegion.Contains, srcTail, span] at hx ⊢; omega
        · intro x hx hy
          apply counterSource x _ _
          · simp only [MemoryRegion.Contains, ctr, span] at hy ⊢; omega
          · change srcTail.toNat ≤ x ∧ x < srcTail.toNat + input.size % 64 at hx
            simp only [MemoryRegion.Contains, srcTail, span] at hx ⊢; omega
      apply tail_payload _ _ _ input mid.store next.store source destination sp offset n
        len off16 firstBytes (remainderSize ▸ srcBytes) _ bytes
      intro j hj
      exact stream j (by omega)

end AesGcm.Proofs.Machine.CTR
