import Md5.Proofs.Block.Start
import Md5.Proofs.Block.Epilogue

namespace Md5.Proofs.Block

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem memLoad_control_of_blocks_frame {s t : RamState} {stack : BitVec 64}
    (hFrame : AgreesExcept (blocksComponents stack) s t) (offset : Nat)
    (hOffset : offset + 8 ≤ 16) :
    memLoad t.external (stack + 96 + BitVec.ofNat 64 offset) 64 =
      memLoad s.external (stack + 96 + BitVec.ofNat 64 offset) 64 := by
  apply memLoad_congr
  intro i hi
  apply congrArg (fun byte : Option UInt8 ↦ byte.getD 0)
  apply hFrame.byte
  intro c hc hCov
  simp only [blocksComponents, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  rcases hc with hc | rfl
  · have hn := loopComponents_control_apart stack (offset + i) (by omega) c hc
    apply hn
    simpa only [BitVec.add_assoc, ← BitVec.ofNat_add] using hCov
  · exact hCov

theorem memLoad_saved_of_blocks_frame {s t : RamState} {stack : BitVec 64}
    (hFrame : AgreesExcept (blocksComponents stack) s t) (offset : Nat)
    (hOffset : 136 ≤ offset) (hEnd : offset + 8 ≤ 192) :
    memLoad t.external (stack + BitVec.ofNat 64 offset) 64 =
      memLoad s.external (stack + BitVec.ofNat 64 offset) 64 := by
  apply memLoad_congr
  intro i hi
  apply congrArg (fun byte : Option UInt8 ↦ byte.getD 0)
  apply hFrame.byte
  intro c hc hCov
  simp only [blocksComponents, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  rcases hc with hc | rfl
  · obtain ⟨j, hj, he⟩ := loopComponents_covers hc hCov
    have ha := RangeApart.offsets stack (a := 0) (b := offset) (len := 136) (count := 8)
      (by decide +kernel) (by omega) (.inl (by omega))
    apply ha j hj i hi
    simpa only [BitVec.add_zero] using he.symm
  · exact hCov

theorem prologue_return_pointer {s t : RamState} (h : (prologueEffect s).Holds s t) :
    memLoad t.external (stackPtr s) 64 = stackTop s := by
  apply memLoad_congr
  intro i hi
  apply congrArg (fun byte : Option UInt8 ↦ byte.getD 0)
  apply (prologue_frame h).byte
  intro c hc hCov
  simp only [prologueComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try exact False.elim hCov
  obtain ⟨j, hj, he⟩ := hCov
  have ha := RangeApart.offsets (stackPtr s - 184) (a := 0) (b := 184)
    (len := 184) (count := 8) (by decide +kernel) (by decide +kernel) (.inl (by decide +kernel))
  apply ha j hj i hi
  simpa only [BitVec.add_zero, BitVec.ofNat_eq_ofNat, BitVec.sub_add_cancel] using he.symm

theorem mem_covers_of_contains {region : MemoryRegion} {address : BitVec 64}
    (h : region.Contains address.toNat) :
    (Component.mem (BitVec.ofNat 64 region.start) region.size).Covers address := by
  refine ⟨address.toNat - region.start, by have := h.2; have := h.1; omega, ?_⟩
  rw [← BitVec.ofNat_add, Nat.add_sub_of_le h.1, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem stack_component_covers {s : RamState} {budget used count : Nat} {address : BitVec 64}
    (hStack : Stack.Valid s budget) (hUsed : used ≤ budget) (hCount : count ≤ used + 8)
    (h : (Component.mem (stackPtr s - BitVec.ofNat 64 used) count).Covers address) :
    (Component.mem (BitVec.ofNat 64 (Stack.region s budget).start)
      (Stack.region s budget).size).Covers address := by
  obtain ⟨i, hi, rfl⟩ := h
  obtain ⟨hs, he⟩ := stack_subrange_bounds hStack hUsed
  apply mem_covers_of_contains
  exact contains_offset_of_subrange hStack.1 hs he i (by omega)

def compressionWorkComponents (s : RamState) : List Component :=
  compressionComponents s ++ [.reg 3, .reg 5, .reg 12, .reg 13, .reg 14, .reg 15]

theorem compression_frame_of_restored {s t : RamState}
    (h : AgreesExcept (compressionWorkComponents s) s t)
    (hSaved : CalleeSavedRegistersUnchanged s t) :
    AgreesExcept (compressionComponents s) s t := by
  apply h.narrow
  intro c hc hn
  simp only [compressionWorkComponents, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  rcases hc with hc | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (hn hc).elim
  · exact hSaved .rbx (by simp)
  · exact hSaved .rbp (by simp)
  · exact hSaved .r12 (by simp)
  · exact hSaved .r13 (by simp)
  · exact hSaved .r14 (by simp)
  · exact hSaved .r15 (by simp)

theorem prologue_compression_frame {s t : RamState}
    (hStack : Stack.Valid s Compress.minStackBytes) (h : (prologueEffect s).Holds s t) :
    AgreesExcept (compressionWorkComponents s) s t := by
  apply (prologue_frame h).widen
  · intro c hc hm
    simp only [prologueComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all [Component.isMem, compressionWorkComponents, compressionComponents]
  · intro address c hc hCov
    simp only [prologueComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try exact False.elim hCov
    refine ⟨_, ?_, stack_component_covers hStack (by decide +kernel) (by decide +kernel) hCov⟩
    simp [compressionWorkComponents, compressionComponents]

theorem blocks_compression_frame {origin s t : RamState}
    (hStack : Stack.Valid origin Compress.minStackBytes)
    (h : AgreesExcept (blocksComponents (stackPtr origin - 184)) s t) :
    AgreesExcept (compressionWorkComponents origin) s t := by
  apply h.widen
  · intro c hc hm
    simp only [blocksComponents, loopComponents, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, or_assoc] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all [Component.isMem, compressionWorkComponents, compressionComponents]
  · intro address c hc hCov
    simp only [blocksComponents, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with hc | rfl
    · refine ⟨_, ?_, stack_component_covers hStack (by decide +kernel) (by decide +kernel)
        (loopComponents_covers hc hCov)⟩
      simp [compressionWorkComponents, compressionComponents]
    · exact hCov.elim


theorem blocks_output_pointer {origin s t : RamState}
    (hPrologue : (prologueEffect origin).Holds origin s)
    (hFrame : AgreesExcept (blocksComponents (stackPtr origin - 184)) s t) :
    memLoad t.external (stackPtr origin - 184 + 96) 64 = origin.regValue .rdi := by
  have he := prologueEffect_output_pointer hPrologue
  rw [prologueEffect_rsp hPrologue] at he
  have hm := memLoad_control_of_blocks_frame hFrame 0 (by decide +kernel)
  rw [BitVec.add_zero] at hm
  exact hm.trans he

theorem blocks_saved {origin s t : RamState}
    (hPrologue : (prologueEffect origin).Holds origin s)
    (hFrame : AgreesExcept (blocksComponents (stackPtr origin - 184)) s t)
    (i : Fin 6) :
    memLoad t.external (stackPtr origin - 184 + BitVec.ofNat 64 (136 + 8 * i.val)) 64 =
      (Operand.reg (#[3, 12, 13, 14, 15, 5] : Array (BitVec 5))[i.val]! : Operand 64).read origin := by
  have he := prologueEffect_saved hPrologue i
  rw [prologueEffect_rsp hPrologue] at he
  exact (memLoad_saved_of_blocks_frame hFrame (136 + 8 * i.val) (by omega)
    (by have := i.isLt; omega)).trans he

theorem blocks_return_pointer {origin s t : RamState}
    (hPrologue : (prologueEffect origin).Holds origin s)
    (hFrame : AgreesExcept (blocksComponents (stackPtr origin - 184)) s t) :
    memLoad t.external (stackPtr origin - 184 + 184) 64 = stackTop origin := by
  have hm := memLoad_saved_of_blocks_frame hFrame 184 (by decide +kernel) (by decide +kernel)
  rw [show BitVec.ofNat 64 184 = (184 : BitVec 64) by rfl, BitVec.sub_add_cancel] at hm
  rw [BitVec.sub_add_cancel]
  exact hm.trans (prologue_return_pointer hPrologue)

theorem compression_body [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {buffer : Standards.RFC.MD5.Buffer} {input : ByteArray}
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hEntry : s.RIP = 0x101ba9) (hInput : Call.Compress.ValidInput s input)
    (hBuffer : Call.Compress.ValidBuffer s buffer) (hStack : Stack.Valid s Compress.minStackBytes)
    (hSeparation : Call.Compress.MemorySeparation s input) (hNonzero : s.regValue .rdx ≠ 0)
    (hBoundary : OutsideCompression boundary.rip) :
    ∃ fuel prepared t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ t.RIP = 0x102436 ∧
      LoopRegisters (Standards.RFC.MD5.processBlocks buffer (Standards.RFC.MD5.wordsOfBytes input)) t ∧
      t.regValue .rsp = stackPtr s - 184 ∧
      (prologueEffect s).Holds s prepared ∧
      AgreesExcept (blocksComponents (stackPtr s - 184)) prepared t := by
  obtain ⟨fuel, prepared, hStart, hPreparedReady, hPreparedCode, hEffect⟩ :=
    compression_prologue boundary hBoundary s hReady hCode
      (compression_prologue_pre hEntry hBuffer hStack hSeparation)
  have hData := prologue_blocksData hInput hBuffer hStack hSeparation hNonzero hEffect
  have hn : (s.regValue .rdx).toNat ≠ 0 := fun he ↦ hNonzero (BitVec.eq_of_toNat_eq he)
  have hSize : input.size = 64 * ((s.regValue .rdx).toNat - 1 + 1) := by
    have he : 64 * (s.regValue .rdx).toNat = input.size := hInput.2.1
    omega
  obtain ⟨fuel', t, hRun, hReady', hCode', hExit, hRegs, hRsp, _, hFrame⟩ :=
    compression_blocks hBoundary ((s.regValue .rdx).toNat - 1)
      hPreparedReady hPreparedCode hEffect.rip hData hSize
  exact ⟨fuel + fuel', prepared, t, hStart.trans hRun, hReady', hCode', hExit,
    hRegs, hRsp, hEffect, hFrame⟩

end Md5.Proofs.Block
