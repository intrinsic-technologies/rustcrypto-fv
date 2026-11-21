import Md5.Proofs.Block.Prologue
import Md5.Proofs.Block.Blocks

namespace Md5.Proofs.Block

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

def prologueComponents (s : RamState) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 4, .reg 8, .flags, .rip,
    .mem (stackPtr s - 184) 184]

theorem mem_covers_stack_slice {base address : BitVec 64} {total back count : Nat}
    (hBack : back ≤ total) (hCount : count ≤ back) (hLow : back < 2^64)
    (h : (Component.mem (base - BitVec.ofNat 64 back) count).Covers address) :
    (Component.mem (base - BitVec.ofNat 64 total) total).Covers address := by
  obtain ⟨i, hi, he⟩ := h
  refine ⟨total - back + i, by omega, ?_⟩
  rw [BitVec.ofNat_add, ← BitVec.add_assoc,
    ← BitVec.ofNat_sub_ofNat_of_le total back hLow hBack]
  rw [BitVec.sub_eq_add_neg (BitVec.ofNat 64 total), ← BitVec.add_assoc,
    BitVec.sub_add_cancel, ← BitVec.sub_eq_add_neg]
  exact he

theorem prologue_frame {s t : RamState} (h : (prologueEffect s).Holds s t) :
    AgreesExcept (prologueComponents s) s t := by
  apply h.agrees.widen
  · intro c hc hm
    simp only [prologueEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, or_assoc] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;> simp_all [Component.isMem, prologueComponents]
  · intro address c hc hCov
    simp only [prologueEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.append_assoc, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;> try exact False.elim hCov
    all_goals
      refine ⟨.mem (stackPtr s - 184) 184, by simp [prologueComponents], ?_⟩
      exact mem_covers_stack_slice (by decide +kernel) (by decide +kernel)
        (by decide +kernel) hCov


theorem compression_prologue_pre {s : RamState} {buffer : Standards.RFC.MD5.Buffer} {input : ByteArray}
    (hEntry : s.RIP = 0x101ba9) (hBuffer : Call.Compress.ValidBuffer s buffer)
    (hStack : Stack.Valid s Compress.minStackBytes)
    (hSeparation : Call.Compress.MemorySeparation s input) : ProloguePre s := by
  have hWrite := compression_stack_writable hStack hSeparation
  refine ⟨hEntry, ?_, ?_, (compression_output_writable hBuffer hSeparation).readable, ?_⟩
  · simpa only [BitVec.add_zero] using memoryWritable_slice hWrite 0 184 (by decide +kernel)
  · intro i hi
    exact compression_stack_avoids_code hStack hSeparation i (by omega)
  · have hp := MemoryRoutines.rangeApart_slice_left
      (compression_stack_output_apart hBuffer hStack hSeparation) 0 184 (by decide +kernel)
    rw [BitVec.add_zero] at hp
    exact hp


theorem prologue_input_bytes {s t : RamState} {input : ByteArray}
    (hInput : Call.Compress.ValidInput s input) (hStack : Stack.Valid s Compress.minStackBytes)
    (hSeparation : Call.Compress.MemorySeparation s input) (h : (prologueEffect s).Holds s t) :
    Bytes t.external (s.regValue .rsi) input.size (fun i ↦ input[i]!) := by
  have hb : Bytes s.external (s.regValue .rsi) input.size (fun i ↦ input[i]!) := by
    simpa only [Compress.inputRegion, registerRegion, BitVec.ofNat_toNat,
      BitVec.setWidth_eq] using bytes_of_hasBytes hInput.2.2
  apply hb.of_agreesExcept (prologue_frame h)
  intro i hi c hc hCov
  simp only [prologueComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try exact False.elim hCov
  obtain ⟨j, hj, he⟩ := hCov
  exact compression_stack_input_apart hInput hStack hSeparation j (by omega) i hi he.symm

theorem compression_count_bytes {s : RamState} {input : ByteArray}
    (hInput : Call.Compress.ValidInput s input) :
    s.regValue .rdx <<< 6 = BitVec.ofNat 64 input.size := by
  have hLength : 64 * (s.regValue .rdx).toNat = input.size := hInput.2.1
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  rw [← hLength, BitVec.ofNat_mul, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  exact BitVec.mul_comm _ _

theorem prologue_loopRegisters {s t : RamState} {buffer : Standards.RFC.MD5.Buffer}
    (hBuffer : Call.Compress.ValidBuffer s buffer) (h : (prologueEffect s).Holds s t) :
    LoopRegisters buffer t := by
  have ha := congrArg (BitVec.setWidth 32) (prologueEffect_words h (0 : Fin 4))
  have hb := congrArg (BitVec.setWidth 32) (prologueEffect_words h (1 : Fin 4))
  have hc := congrArg (BitVec.setWidth 32) (prologueEffect_words h (2 : Fin 4))
  have hd := congrArg (BitVec.setWidth 32) (prologueEffect_words h (3 : Fin 4))
  change ((Operand.reg 1 : Operand 64).read t).setWidth 32 =
    (((Operand.mem ((Operand.reg 7 : Operand 64).read s + 0) : Operand 32).read s).setWidth 64).setWidth 32 at ha
  change ((Operand.reg 8 : Operand 64).read t).setWidth 32 =
    (((Operand.mem ((Operand.reg 7 : Operand 64).read s + 4) : Operand 32).read s).setWidth 64).setWidth 32 at hb
  change ((Operand.reg 2 : Operand 64).read t).setWidth 32 =
    (((Operand.mem ((Operand.reg 7 : Operand 64).read s + 8) : Operand 32).read s).setWidth 64).setWidth 32 at hc
  change ((Operand.reg 0 : Operand 64).read t).setWidth 32 =
    (((Operand.mem ((Operand.reg 7 : Operand 64).read s + 12) : Operand 32).read s).setWidth 64).setWidth 32 at hd
  simp only [Operand.read, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64),
    BitVec.setWidth_eq] at ha hb hc hd
  have hr : (Operand.reg 7 : Operand 64).read s = s.regValue .rdi := by rfl
  change (s.GPR[gprIndex 7]).setWidth 64 = s.regValue .rdi at hr
  rw [hr] at ha
  have hz : s.regValue .rdi + (0 : BitVec 64) = s.regValue .rdi := by simp
  rw [hz] at ha
  rw [hr] at hb hc hd
  exact ⟨ha.trans (memLoad_buffer_A hBuffer), hb.trans (memLoad_buffer_B hBuffer),
    hc.trans (memLoad_buffer_C hBuffer), hd.trans (memLoad_buffer_D hBuffer)⟩


theorem prologue_blocksData {s t : RamState} {buffer : Standards.RFC.MD5.Buffer} {input : ByteArray}
    (hInput : Call.Compress.ValidInput s input) (hBuffer : Call.Compress.ValidBuffer s buffer)
    (hStack : Stack.Valid s Compress.minStackBytes)
    (hSeparation : Call.Compress.MemorySeparation s input)
    (hNonzero : s.regValue .rdx ≠ 0) (h : (prologueEffect s).Holds s t) :
    BlocksData (stackPtr s - 184) (s.regValue .rsi) buffer input t := by
  have hSize : 64 ≤ input.size := by
    have hl : 64 * (s.regValue .rdx).toNat = input.size := hInput.2.1
    have hn : (s.regValue .rdx).toNat ≠ 0 := fun he ↦ hNonzero (BitVec.eq_of_toNat_eq he)
    omega
  have hBytes := prologue_input_bytes hInput hStack hSeparation h
  have hRead : MemReadable t (s.regValue .rsi) input.size := by
    refine ⟨?_, fun i hi ↦ ?_⟩
    · have hl : (s.regValue .rsi).toNat + input.size < 2^32 := hInput.1
      omega
    · rw [hBytes i hi]
      rfl
  have hFullApart : RangeApart (stackPtr s - 184) 136 (s.regValue .rsi) input.size := by
    simpa only [BitVec.add_zero] using MemoryRoutines.rangeApart_slice_left
      (compression_stack_input_apart hInput hStack hSeparation) 0 136 (by decide +kernel)
  have hWrite : Memory.MemWritable t (stackPtr s - 184) 136 := by
    have hw : Memory.MemWritable s (stackPtr s - 184) 136 := by
      simpa only [BitVec.add_zero] using memoryWritable_slice
        (compression_stack_writable hStack hSeparation) 0 136 (by decide +kernel)
    exact ⟨hw.low, fun i hi ↦ h.agrees.grow _ (hw.bytes i hi), hw.tables⟩
  refine ⟨⟨prologue_loopRegisters hBuffer h, prologueEffect_rsp h, prologueEffect_rsi h,
    hWrite, ?_, loop_inputWords_of_bytes hBytes hSize, ?_, ?_⟩,
    hBytes, hRead, hFullApart, ?_⟩
  · simpa only [BitVec.add_zero] using MemoryRoutines.memReadable_slice hRead 0 64 hSize
  · simpa only [BitVec.add_zero] using MemoryRoutines.rangeApart_slice_right hFullApart 0 64 hSize
  · intro i hi
    exact compression_stack_avoids_code hStack hSeparation i (by omega)
  · have he := prologueEffect_end_pointer h
    rw [prologueEffect_rsp h] at he
    change memLoad t.external (stackPtr s - 184 + 104) 64 =
      s.regValue .rsi + (s.regValue .rdx <<< 6) at he
    rwa [compression_count_bytes hInput] at he

end Md5.Proofs.Block
