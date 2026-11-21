import P256.Proofs.SHA256.Entry.Memory
import P256.Proofs.SHA256.Loop
import P256.Proofs.SHA256.Compression.Interface

set_option autoImplicit false

namespace P256.Proofs.SHA256

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Program
open P256.Proofs.Common.Encoding.Serialize (read_mem_of_agrees)

variable [Bindings] {initial current : RamState} {boundary : ReturnBoundary}
  {initialHash hash : Array UInt32} {input : ByteArray} {count index : Nat}

theorem _root_.P256.Proofs.Program.ScalarFrame.FrameState.sha_block_stack (pre : CompressionPre initial boundary initialHash input count)
    (state : ScalarFrame.FrameState initial current 32 336 336) (rip : current.RIP = 0x1159e0) :
    Compression.FramePre 0x1159e0 10114 288 current := by
  have hs : (stackPtr current).toNat = (stackPtr initial).toNat - 336 := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.add_zero] using
      state.sha_stackOffset_toNat pre (offset := 0) (by decide)
  have bounds := stack_bounds pre.stack
  have align := pre.stack.2.2.2
  change (stackPtr initial).toNat % 16 = 8 at align
  refine ⟨rip, ?_, ?_, ?_, ?_, by decide, ?_⟩
  · change (stackPtr current).toNat % 8 = 0
    rw [hs]
    omega
  · change (stackPtr current).toNat + 288 ≤ 0x1000 ∨ 0x3000 ≤ (stackPtr current).toNat
    apply tables_interval_of_not_reserved (by decide)
      (by simpa only [BitVec.add_zero] using
        (state.sha_stackOffset_readable pre (offset := 0) (len := 288) (by decide)).low)
    intro i hi ht
    exact pre.avoids _ (by simp) _ (state.sha_stackOffset_contains pre hi) (.inr ht)
  · change (stackPtr current).toNat + 288 ≤ 2^32
    rw [hs]
    omega
  · intro i hi
    change (current.external[stackPtr current + BitVec.ofNat 64 i]?).isSome
    have h := (state.sha_stackOffset_readable pre (offset := 0) (len := 288) (by decide)).mem i hi
    simpa only [BitVec.add_zero] using h
  · change 0x1159e0 + 10114 ≤ (stackPtr current).toNat - 0 ∨
      (stackPtr current).toNat + 288 ≤ 0x1159e0
    apply Classical.byContradiction
    intro h
    have ha : max (stackPtr current).toNat 0x1159e0 < (stackPtr current).toNat + 288 ∧
        max (stackPtr current).toNat 0x1159e0 < 0x1159e0 + 10114 := by omega
    let a := max (stackPtr current).toNat 0x1159e0
    have hlow : a < 2^64 := by dsimp only [a]; omega
    apply pre.avoids (Stack.region initial 336) (by simp) (BitVec.ofNat 64 a)
    · change (stackPtr initial).toNat - 336 ≤ _ ∧
        _ < (Stack.region initial 336).start + (Stack.region initial 336).size
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlow, stack_region_end]
      dsimp only [a]
      omega
    · left
      have hp := inProgram_of_textOffset (a - 0x100000) (by dsimp only [a]; omega)
      have he : Extracted.textAddress + BitVec.ofNat 64 (a - 0x100000) = BitVec.ofNat 64 a := by
        change BitVec.ofNat 64 0x100000 + BitVec.ofNat 64 (a - 0x100000) = _
        rw [← BitVec.ofNat_add, Nat.add_sub_of_le]
        dsimp only [a]
        omega
      exact he ▸ hp

theorem LoopState.block_pre (pre : CompressionPre initial boundary initialHash input count)
    (state : LoopState initial current hash index count) (rip : current.RIP = 0x1159e0)
    (hi : index < count) :
    Compression.BlockPre current hash (input.extract (64*index) (64*(index+1))) := by
  have hsize : (input.extract (64*index) (64*(index+1))).size = 64 := by
    rw [ByteArray.size_extract, pre.inputSize, Nat.min_eq_left (by omega)]
    omega
  refine ⟨state.toFrameState.sha_block_stack pre rip, state.registers, ?_, ?_, ?_, ?_⟩
  · rw [state.inputPointer]
    exact state.toFrameState.sha_input_block_readable pre hi
  · refine ⟨hsize, ?_⟩
    intro ⟨j, hj⟩
    rw [ByteArray.getElem_extract]
    change current.external[BitVec.ofNat 64 ((current.regValue .rsi).toNat + j)]? = _
    have ptrNat := pre.inputPointer_toNat (Nat.le_of_lt hi)
    rw [state.inputPointer, ptrNat]
    have address : BitVec.ofNat 64 ((initial.regValue .rsi).toNat + 64*index + j) =
        initial.regValue .rsi + BitVec.ofNat 64 (64*index+j) := by
      rw [BitVec.ofNat_add, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_assoc, ← BitVec.ofNat_add]
    rw [address, state.toFrameState.sha_input_byte pre (by rw [hsize] at hj; omega)]
    have h := pre.inputBytes.2 ⟨64*index+j, by rw [pre.inputSize]; rw [hsize] at hj; omega⟩
    simpa only [registerRegion, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using h
  · intro i hi' j hj he
    have inputContains : (registerRegion initial .rsi (64*count)).Contains
        (current.regValue .rsi + BitVec.ofNat 64 i).toNat := by
      rw [state.inputPointer, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact memoryRegion_contains_add pre.inputBounded (Nat.le_refl _) (Nat.le_refl _)
        (by change 64*index+i<64*count; omega)
    apply pre.separation (0 : Fin 3) (2 : Fin 3) (by decide) _ inputContains
    rw [he]
    exact state.toFrameState.sha_stackOffset_contains pre hj
  · intro i hi' hip
    exact pre.avoids (Stack.region initial 336) (by simp) _
      (state.toFrameState.sha_stackOffset_contains pre hi') (Or.inl hip)

theorem LoopState.after_block (pre : CompressionPre initial boundary initialHash input count)
    (state : LoopState initial current hash index count) {next : RamState} {block : ByteArray}
    (result : Compression.BlockResult current next boundary hash block) :
    LoopState initial next (Reference.compress hash (Standards.NIST.SHA2.bytesToBits block)) index count := by
  refine ⟨?_, result.registers, result.rsi.trans state.inputPointer,
    result.statePointer.trans state.statePointer, result.endPointer.trans state.endPointer⟩
  apply state.toFrameState.sha_after_agrees pre result.ready result.agrees
  · simp [Compression.blockComponents]
  · intro c hc a ha
    simp only [Compression.blockComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    · have h : (Component.mem (stackPtr current + BitVec.ofNat 64 0) 192).Covers a := by
        simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using ha
      exact state.toFrameState.sha_stackOffset_local pre (offset := 0) (by decide) h
    · exact state.toFrameState.sha_stackOffset_local pre (offset := 208) (by decide) ha

end P256.Proofs.SHA256
