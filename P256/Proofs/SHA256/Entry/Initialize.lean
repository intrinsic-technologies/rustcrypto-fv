import P256.Proofs.SHA256.Entry.Memory
import P256.Proofs.SHA256.Entry.EndPointer
import P256.Proofs.SHA256.Entry.StatePointer

set_option autoImplicit false

namespace P256.Proofs.SHA256

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Program
open P256.Proofs.Common.Encoding.Serialize (read_mem_of_agrees)

variable [Bindings] {initial : RamState} {boundary : ReturnBoundary}
  {hash : Array UInt32} {input : ByteArray} {count : Nat}

theorem entry_initialize (pre : CompressionPre initial boundary hash input count)
    (positive : 0 < count) :
    ∃ fuel final, Advances boundary fuel initial final ∧ final.RIP = 0x1159e0 ∧
      LoopState initial final hash 0 count := by
  obtain ⟨s, runS, readyS, loadedS, ripS, rspS, memS, agreesS⟩ := entry_save pre positive
  have frameS := entry_saved_frame pre readyS loadedS rspS memS agreesS
  have siS : s.regValue .rsi = initial.regValue .rsi :=
    agreesS.read (n := 64) (r := 6) (by simp [saveFrame])
  have diS : s.regValue .rdi = initial.regValue .rdi :=
    agreesS.read (n := 64) (r := 7) (by simp [saveFrame])
  have dxS : s.regValue .rdx = BitVec.ofNat 64 count :=
    (agreesS.read (n := 64) (r := 2) (by simp [saveFrame])).trans pre.countRegister
  have ep : EndPointerPre s := by
    refine ⟨ripS, frameS.sha_stackOffset_writable pre (offset := 200) (by decide), ?_⟩
    apply frameS.sha_stackOffset_codeApart pre (offset := 200) (pos := 0x159aa) (by decide)
    intro j hj
    have h := inProgram_of_textOffset (0x159aa+j) (by omega)
    simpa only [Extracted.textAddress, BitVec.ofNat_add, ← BitVec.add_assoc,
      BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using h
  obtain ⟨fuelT, t, runT, readyT, _, effectT⟩ := end_pointer_correct boundary pre.outerBoundary s readyS
    (programText_slice (programLoaded_codeIn loadedS) 0x159aa endPointerBytes
      (by decide) (by decide +kernel)) ep
  have frameT : ScalarFrame.FrameState initial t 32 336 336 := by
    apply frameS.sha_after_agrees pre readyT effectT.agrees
    · simp [endPointerEffect, Effect.components]
    · intro c hc a ha
      simp only [endPointerEffect, Effect.components, List.map_cons, List.map_nil,
        List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false, Write.component] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals try exact ha.elim
      exact frameS.sha_stackOffset_local pre (offset := 200) (len := 8) (by decide) ha
  have spT : stackPtr t = stackPtr s := effectT.agrees.read (n := 64) (r := 4)
    (by simp [endPointerEffect, Effect.components])
  have siT : t.regValue .rsi = initial.regValue .rsi :=
    (effectT.agrees.read (n := 64) (r := 6) (by simp [endPointerEffect, Effect.components])).trans siS
  have diT : t.regValue .rdi = initial.regValue .rdi :=
    (effectT.agrees.read (n := 64) (r := 7) (by simp [endPointerEffect, Effect.components])).trans diS
  have endT : memLoad t.external (stackPtr t + 200) 64 =
      initial.regValue .rsi + BitVec.ofNat 64 (64 * count) := by
    have hw : memLoad t.external (stackPtr s + 200) 64 = (s.regValue .rdx <<< 6) + s.regValue .rsi :=
      effectT.writes.2
    rw [spT, hw, dxS, siS, BitVec.add_comm]
    congr 1
    rw [BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 64 count * BitVec.ofNat 64 64 = BitVec.ofNat 64 (64 * count)
    rw [← BitVec.ofNat_mul, Nat.mul_comm]
  have hashT (i : Nat) (hi : i < 8) :
      memLoad t.external (initial.regValue .rdi + BitVec.ofNat 64 (4*i)) 32 = hash[i]!.toBitVec := by
    have he : (Operand.mem (initial.regValue .rdi + BitVec.ofNat 64 (4*i)) : Operand 32).read t =
        (Operand.mem (initial.regValue .rdi + BitVec.ofNat 64 (4*i)) : Operand 32).read s := by
      apply read_mem_of_agrees effectT.agrees
      intro j hj c hc ha
      simp only [endPointerEffect, Effect.components, List.map_cons, List.map_nil,
        List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false, Write.component] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals try exact ha.elim
      obtain ⟨k, hk, he⟩ := ha
      exact frameS.sha_stackOffset_hashApart pre (offset := 200) (len := 8) (by decide) hi k hk j hj he.symm
    exact he.trans (entry_saved_hashWord pre agreesS hi)
  have lp : LoadWordsPre t := ⟨effectT.rip, fun i hi => by
    rw [diT]; exact frameT.sha_hashWord_readable pre (by omega)⟩
  obtain ⟨fuelU, u, runU, readyU, _, effectU⟩ := load_words_correct boundary pre.outerBoundary t readyT
    (programText_slice (programLoaded_codeIn frameT.loaded) 0x159bc loadWordsBytes
      (by decide) (by decide +kernel)) lp
  have noMemU : ∀ c ∈ (loadWordsEffect t).components, ∀ a, ¬ c.Covers a := by
    simp [loadWordsEffect, Effect.components, Component.Covers]
  have frameU := frameT.after_registers readyU effectU.agrees noMemU
    (by simp [loadWordsEffect, Effect.components])
  have memoryU := effectU.agrees.external noMemU
  have spU : stackPtr u = stackPtr t := effectU.agrees.read (n := 64) (r := 4)
    (by simp [loadWordsEffect, Effect.components])
  have siU : u.regValue .rsi = initial.regValue .rsi :=
    (effectU.agrees.read (n := 64) (r := 6) (by simp [loadWordsEffect, Effect.components])).trans siT
  have diU : u.regValue .rdi = initial.regValue .rdi :=
    (effectU.agrees.read (n := 64) (r := 7) (by simp [loadWordsEffect, Effect.components])).trans diT
  have wp : StatePointerPre u := by
    refine ⟨effectU.rip, frameU.sha_stackOffset_writable pre (offset := 192) (by decide), ?_, ?_, ?_⟩
    · rw [diU]; exact frameU.sha_hashWord_readable pre (i := 7) (by decide)
    · apply frameU.sha_stackOffset_codeApart pre (offset := 192) (pos := 0x159d4) (by decide)
      intro j hj
      have h := inProgram_of_textOffset (0x159d4+j) (by omega)
      simpa only [Extracted.textAddress, BitVec.ofNat_add, ← BitVec.add_assoc,
        BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using h
    · rw [diU]; exact frameU.sha_stackOffset_hashApart pre (offset := 192) (i := 7) (by decide) (by decide)
  obtain ⟨fuelV, v, runV, readyV, _, effectV⟩ := state_pointer_correct boundary pre.outerBoundary u readyU
    (programText_slice (programLoaded_codeIn frameU.loaded) 0x159d4 statePointerBytes
      (by decide) (by decide +kernel)) wp
  have frameV : ScalarFrame.FrameState initial v 32 336 336 := by
    apply frameU.sha_after_agrees pre readyV effectV.agrees
    · simp [statePointerEffect, Effect.components]
    · intro c hc a ha
      simp only [statePointerEffect, Effect.components, List.map_cons, List.map_nil,
        List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false, Write.component] at hc
      rcases hc with rfl | rfl | rfl
      all_goals try exact ha.elim
      exact frameU.sha_stackOffset_local pre (offset := 192) (len := 8) (by decide) ha
  have spV : stackPtr v = stackPtr u := effectV.agrees.read (n := 64) (r := 4)
    (by simp [statePointerEffect, Effect.components])
  have regV (r : BitVec 5) (hr : r ≠ 1#5) : (Operand.reg r : Operand 64).read v =
      (Operand.reg r : Operand 64).read u := effectV.agrees.read
    (by simp [statePointerEffect, Effect.components, hr])
  refine ⟨((9 + fuelT) + fuelU) + fuelV, v, ((runS.trans runT).trans runU).trans runV,
    effectV.rip, ⟨frameV, ?_, ?_, ?_, ?_⟩⟩
  · have hw := effectU.writes
    change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ at hw
    have word (r : BitVec 5) (hr : r ≠ 1#5) (i : Nat) (hi : i < 8)
        (hw : (Operand.reg r : Operand 64).read u =
          (memLoad t.external (t.regValue .rdi + BitVec.ofNat 64 (4*i)) 32).setWidth 64) :
        ((Operand.reg r : Operand 64).read v).setWidth 32 = hash[i]!.toBitVec := by
      rw [regV r hr, hw, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64),
        BitVec.setWidth_eq, diT]
      exact hashT i hi
    refine ⟨pre.hashWords.1,
      word 3 (by decide) 0 (by decide) hw.1,
      word 14 (by decide) 1 (by decide) hw.2.1,
      word 0 (by decide) 2 (by decide) hw.2.2.1,
      word 9 (by decide) 3 (by decide) hw.2.2.2.1,
      word 8 (by decide) 4 (by decide) hw.2.2.2.2.1,
      word 10 (by decide) 5 (by decide) hw.2.2.2.2.2.1,
      word 2 (by decide) 6 (by decide) hw.2.2.2.2.2.2, ?_⟩
    have h : v.regValue .rcx = (memLoad u.external (u.regValue .rdi + 28) 32).setWidth 64 := effectV.writes.2
    rw [h, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq, memoryU, diU]
    exact hashT 7 (by decide)
  · change v.regValue .rsi = initial.regValue .rsi + BitVec.ofNat 64 (64*0)
    rw [show BitVec.ofNat 64 (64*0) = 0#64 from rfl, BitVec.add_zero]
    exact (regV 6 (by decide)).trans siU
  · rw [spV]
    exact effectV.writes.1.trans diU
  · rw [spV]
    have he : memLoad v.external (stackPtr u + 200) 64 = memLoad u.external (stackPtr u + 200) 64 := by
      apply read_mem_of_agrees effectV.agrees
      intro i hi c hc ha
      simp only [statePointerEffect, Effect.components, List.map_cons, List.map_nil,
        List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false, Write.component] at hc
      rcases hc with rfl | rfl | rfl
      all_goals try exact ha.elim
      obtain ⟨j, hj, he⟩ := ha
      exact OffsetsApart.ne (c₁ := 192) (len₁ := 8) (c₂ := 200) (len₂ := 8)
        (by unfold OffsetsApart; decide +kernel) (stackPtr u) hj hi (by decide) he.symm
    rw [he, memoryU, spU]
    exact endT

end P256.Proofs.SHA256
