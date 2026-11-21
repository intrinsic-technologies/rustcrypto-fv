import Md5.Proofs.Block.Loop
import Md5.Proofs.Block.Rounds
import Md5.Proofs.Block.Tail

namespace Md5.Proofs.Block

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure BlocksData (stack base : BitVec 64) (buffer : Standards.RFC.MD5.Buffer)
    (input : ByteArray) (s : RamState) : Prop extends
    LoopData stack base buffer
      (Vector.ofFn fun i : Fin 16 ↦ (Standards.RFC.MD5.wordsOfBytes input).getD i.val 0) s where
  bytes : Bytes s.external base input.size (fun i ↦ input[i]!)
  fullReadable : MemReadable s base input.size
  fullApart : RangeApart stack 0x88 base input.size
  stop : memLoad s.external (stack + 104) 64 = base + BitVec.ofNat 64 input.size

def blocksComponents (stack : BitVec 64) : List Component :=
  loopComponents stack ++ [.reg 6]

theorem bytes_extract_tail {m : Ram} {base : BitVec 64} {input : ByteArray}
    (h : Bytes m base input.size (fun i ↦ input[i]!)) (offset : Nat) (hOffset : offset ≤ input.size) :
    Bytes m (base + BitVec.ofNat 64 offset) (input.extract offset input.size).size
      (fun i ↦ (input.extract offset input.size)[i]!) := by
  have hSize : (input.extract offset input.size).size = input.size - offset := by
    simp only [ByteArray.size_extract, Nat.min_self]
  rw [hSize]
  apply (h.sub offset (input.size - offset) (by omega)).congr
  intro i hi
  have hiInput : offset + i < input.size := by omega
  have hiTail : i < (input.extract offset input.size).size := by rw [hSize]; exact hi
  simp only [getElem!_pos input (offset + i) hiInput,
    getElem!_pos (input.extract offset input.size) i hiTail, ByteArray.getElem_extract]

theorem loop_inputWords_of_bytes {s : RamState} {base : BitVec 64} {input : ByteArray}
    (h : Bytes s.external base input.size (fun i ↦ input[i]!)) (hSize : 64 ≤ input.size) :
    ∀ i : Fin 16,
      (Operand.mem (base + BitVec.ofNat 64 (4 * i.val)) : Operand 32).read s =
        (Vector.ofFn fun j : Fin 16 ↦ (Standards.RFC.MD5.wordsOfBytes input).getD j.val 0)[i] := by
  intro i
  have hi : i.val < (Standards.RFC.MD5.wordsOfBytes input).size := by
    rw [Md5.Proofs.RFC1321.size_wordsOfBytes]
    have := i.isLt
    omega
  simp only [Fin.getElem_fin, Vector.getElem_ofFn]
  rw [← Array.getElem_eq_getD (h := hi)]
  exact memLoad_wordsOfBytes h i.val hi

theorem extract_tail_end (base : BitVec 64) (input : ByteArray) (offset : Nat)
    (hOffset : offset ≤ input.size) :
    base + BitVec.ofNat 64 offset + BitVec.ofNat 64 (input.extract offset input.size).size =
      base + BitVec.ofNat 64 input.size := by
  rw [ByteArray.size_extract, Nat.min_self, BitVec.add_assoc, ← BitVec.ofNat_add,
    Nat.add_sub_of_le hOffset]

theorem BlocksData.tail {s t u : RamState} {stack base : BitVec 64}
    {buffer next : Standards.RFC.MD5.Buffer} {input : ByteArray}
    (h : BlocksData stack base buffer input s) (hSize : 128 ≤ input.size)
    (hRound : LoopData stack base next
      (Vector.ofFn fun i : Fin 16 ↦ (Standards.RFC.MD5.wordsOfBytes input).getD i.val 0) t)
    (hRoundFrame : AgreesExcept (loopComponents stack) s t)
    (hTailFrame : AgreesExcept [.reg 6, .flags, .rip] t u)
    (hRsi : u.regValue .rsi = base + 64) :
    BlocksData stack (base + 64) next (input.extract 64 input.size) u := by
  have hMemory := hTailFrame.external (by simp [Component.Covers])
  have hBytes₀ := bytes_of_loop_frame h.bytes hRoundFrame h.fullApart
  have hBytes : Bytes u.external base input.size (fun i ↦ input[i]!) := by
    rw [hMemory]
    exact hBytes₀
  have hBytesTail := bytes_extract_tail hBytes 64 (by omega)
  have hTailSize : (input.extract 64 input.size).size = input.size - 64 := by
    simp only [ByteArray.size_extract, Nat.min_self]
  have hFullRead : MemReadable u base input.size :=
    ⟨h.fullReadable.low, fun i hi ↦ hTailFrame.grow _ (hRoundFrame.grow _ (h.fullReadable.mem i hi))⟩
  have hReadTail : MemReadable u (base + 64) (input.extract 64 input.size).size := by
    rw [hTailSize]
    simpa only [BitVec.ofNat_eq_ofNat] using
      MemoryRoutines.memReadable_slice hFullRead 64 (input.size - 64) (by omega)
  have hApartTail : RangeApart stack 0x88 (base + 64) (input.extract 64 input.size).size := by
    rw [hTailSize]
    simpa only [BitVec.ofNat_eq_ofNat] using
      MemoryRoutines.rangeApart_slice_right h.fullApart 64 (input.size - 64) (by omega)
  have hReg : LoopRegisters next u := by
    exact ⟨(hTailFrame.read (n := 32) (r := 1) (by simp)).trans hRound.registers.1,
      (hTailFrame.read (n := 32) (r := 8) (by simp)).trans hRound.registers.2.1,
      (hTailFrame.read (n := 32) (r := 2) (by simp)).trans hRound.registers.2.2.1,
      (hTailFrame.read (n := 32) (r := 0) (by simp)).trans hRound.registers.2.2.2⟩
  have hRsp : u.regValue .rsp = stack :=
    (hTailFrame.read (n := 64) (r := 4) (by simp)).trans hRound.stackPointer
  have hFirstRead : MemReadable u (base + 64) 64 := by
    simpa only [BitVec.add_zero] using MemoryRoutines.memReadable_slice hReadTail 0 64 (by omega)
  have hFirstApart : RangeApart stack 0x88 (base + 64) 64 := by
    simpa only [BitVec.add_zero] using MemoryRoutines.rangeApart_slice_right hApartTail 0 64 (by omega)
  refine ⟨⟨hReg, hRsp, hRsi, hRound.frame.of_external_eq hMemory, hFirstRead,
    loop_inputWords_of_bytes hBytesTail (by omega), hFirstApart, hRound.code⟩,
    hBytesTail, hReadTail, hApartTail, ?_⟩
  rw [hMemory]
  have hControl := memLoad_control_of_loop_frame hRoundFrame 8 (by decide +kernel)
  have hControl' : memLoad t.external (stack + 104) 64 =
      memLoad s.external (stack + 104) 64 := by simpa [BitVec.add_assoc] using hControl
  have hEnd := hControl'.trans h.stop
  rw [hEnd]
  simpa only [BitVec.ofNat_eq_ofNat] using (extract_tail_end base input 64 (by omega)).symm

theorem compression_block_step [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {stack base : BitVec 64} {buffer : Standards.RFC.MD5.Buffer} {input : ByteArray}
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hEntry : s.RIP = 0x101be0) (hData : BlocksData stack base buffer input s)
    (hBoundary : OutsideCompression boundary.rip) :
    let next := Standards.RFC.MD5.processBlock buffer
      (Vector.ofFn fun i : Fin 16 ↦ (Standards.RFC.MD5.wordsOfBytes input).getD i.val 0)
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧
      t.RIP = (if base + 64 = base + BitVec.ofNat 64 input.size then 0x102436 else 0x101be0) ∧
      t.regValue .rsi = base + 64 ∧ t.regValue .rsp = stack ∧ LoopRegisters next t ∧
      AgreesExcept (blocksComponents stack) s t ∧
      (128 ≤ input.size → BlocksData stack (base + 64) next (input.extract 64 input.size) t) := by
  obtain ⟨fuel, mid, hRound, hReady', hCode', hEntry', hData', hRoundFrame⟩ :=
    compression_rounds hReady hCode hEntry hData.toLoopData hBoundary
  have hRead : MemReadable mid (mid.regValue .rsp + 104) 8 := by
    rw [hData'.stackPointer]
    simpa only [BitVec.ofNat_eq_ofNat] using
      MemoryRoutines.memReadable_slice hData'.frame.readable 104 8 (by decide +kernel)
  have hEnd : memLoad mid.external (mid.regValue .rsp + 104) 64 =
      base + BitVec.ofNat 64 input.size := by
    rw [hData'.stackPointer]
    have hSaved := memLoad_control_of_loop_frame hRoundFrame 8 (by decide +kernel)
    have hSaved' : memLoad mid.external (stack + 104) 64 =
        memLoad s.external (stack + 104) 64 := by simpa [BitVec.add_assoc] using hSaved
    exact hSaved'.trans hData.stop
  obtain ⟨t, hTail, hReady'', hCode'', hExit, hRsi, hTailFrame⟩ :=
    compression_tail hReady' hCode' hEntry' hRead hEnd hBoundary
  rw [hData'.inputPointer] at hExit hRsi
  have hReg : LoopRegisters _ t :=
    ⟨(hTailFrame.read (n := 32) (r := 1) (by simp)).trans hData'.registers.1,
      (hTailFrame.read (n := 32) (r := 8) (by simp)).trans hData'.registers.2.1,
      (hTailFrame.read (n := 32) (r := 2) (by simp)).trans hData'.registers.2.2.1,
      (hTailFrame.read (n := 32) (r := 0) (by simp)).trans hData'.registers.2.2.2⟩
  have hRsp : t.regValue .rsp = stack :=
    (hTailFrame.read (n := 64) (r := 4) (by simp)).trans hData'.stackPointer
  refine ⟨fuel + 3, t, hRound.trans hTail, hReady'', hCode'', hExit, hRsi, hRsp, hReg, ?_, ?_⟩
  · exact (hRoundFrame.trans hTailFrame).mono (by simp [blocksComponents, loopComponents])
  · intro hSize
    exact hData.tail hSize hData' hRoundFrame hTailFrame hRsi

theorem compression_blocks [Bindings] {boundary : ReturnBoundary}
    (hBoundary : OutsideCompression boundary.rip) (n : Nat)
    {s : RamState} {stack base : BitVec 64} {buffer : Standards.RFC.MD5.Buffer} {input : ByteArray}
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hEntry : s.RIP = 0x101be0) (hData : BlocksData stack base buffer input s)
    (hSize : input.size = 64 * (n + 1)) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ t.RIP = 0x102436 ∧
      LoopRegisters (Standards.RFC.MD5.processBlocks buffer (Standards.RFC.MD5.wordsOfBytes input)) t ∧
      t.regValue .rsp = stack ∧ t.regValue .rsi = base + BitVec.ofNat 64 input.size ∧
      AgreesExcept (blocksComponents stack) s t := by
  induction n generalizing s base buffer input with
  | zero =>
    obtain ⟨fuel, t, hAdvance, hReady', hCode', hExit, hRsi, hRsp, hReg, hFrame, _⟩ :=
      compression_block_step hReady hCode hEntry hData hBoundary
    have h64 : input.size = 64 := by omega
    have hExit' : t.RIP = 0x102436 := by simpa only [h64, BitVec.ofNat_eq_ofNat, ite_true] using hExit
    have hProcess := Md5.Proofs.RFC1321.processBlocks_one buffer (Standards.RFC.MD5.wordsOfBytes input)
      (by rw [Md5.Proofs.RFC1321.size_wordsOfBytes, h64])
    refine ⟨fuel, t, hAdvance, hReady', hCode', hExit', ?_, hRsp, ?_, hFrame⟩
    · simpa only [hProcess] using hReg
    · simpa only [h64, BitVec.ofNat_eq_ofNat] using hRsi
  | succ n ih =>
    obtain ⟨fuel, t, hAdvance, hReady', hCode', hExit, hRsi, _, _, hFrame, hNext⟩ :=
      compression_block_step hReady hCode hEntry hData hBoundary
    have hAtLeast : 128 ≤ input.size := by omega
    have hLess : input.size < 2^64 := by have := hData.fullReadable.low; omega
    have hDifferent : base + 64 ≠ base + BitVec.ofNat 64 input.size := by
      intro he
      have hc := (BitVec.add_right_inj base).mp he
      have hn := congrArg BitVec.toNat hc
      change 64 = input.size % 2^64 at hn
      rw [Nat.mod_eq_of_lt hLess] at hn
      omega
    have hExit' : t.RIP = 0x101be0 := by simpa only [hDifferent, ite_false] using hExit
    have hTailSize : (input.extract 64 input.size).size = 64 * (n + 1) := by
      rw [ByteArray.size_extract, Nat.min_self]
      omega
    obtain ⟨fuel', final, hRest, hReady'', hCode'', hExit'', hRegs, hRsp, hEnd, hFrame'⟩ :=
      ih hReady' hCode' hExit' (hNext hAtLeast) hTailSize
    have hFour : 4 * (input.size / 4) = input.size := by omega
    have hTailWords : Standards.RFC.MD5.wordsOfBytes (input.extract 64 input.size) =
        (Standards.RFC.MD5.wordsOfBytes input).extract 16 (Standards.RFC.MD5.wordsOfBytes input).size := by
      simpa only [hFour, Nat.reduceMul, Md5.Proofs.RFC1321.size_wordsOfBytes] using
        Md5.Proofs.RFC1321.wordsOfBytes_extract input 16 (input.size / 4)
    have hProcess : Standards.RFC.MD5.processBlocks buffer (Standards.RFC.MD5.wordsOfBytes input) =
        Standards.RFC.MD5.processBlocks
          (Standards.RFC.MD5.processBlock buffer
            (Vector.ofFn fun i : Fin 16 ↦ (Standards.RFC.MD5.wordsOfBytes input).getD i.val 0))
          (Standards.RFC.MD5.wordsOfBytes (input.extract 64 input.size)) := by
      rw [Md5.Proofs.RFC1321.processBlocks_cons buffer _ (by
        rw [Md5.Proofs.RFC1321.size_wordsOfBytes]; omega), hTailWords]
    refine ⟨fuel + fuel', final, hAdvance.trans hRest, hReady'', hCode'', hExit'', ?_, hRsp, ?_, ?_⟩
    · simpa only [hProcess] using hRegs
    · exact hEnd.trans (by simpa only [BitVec.ofNat_eq_ofNat] using extract_tail_end base input 64 (by omega))
    · exact (hFrame.trans hFrame').mono (by simp [List.mem_append])

end Md5.Proofs.Block
