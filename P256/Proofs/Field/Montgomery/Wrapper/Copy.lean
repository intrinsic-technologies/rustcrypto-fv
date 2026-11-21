import P256.Proofs.Field.Montgomery.Wrapper.CopyBlock
import P256.Proofs.Field.Montgomery.Wrapper.State
import P256.Proofs.Program.Output

set_option autoImplicit false

open P256.Proofs.Program

namespace P256.Proofs.Field.Montgomery.Wrapper

open P256.Spec.Program.Routines
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [Bindings] {s t u : RamState} {boundary : ReturnBoundary} {entryPC : BitVec 64} {square : Bool}

omit [Bindings] in
theorem scratch_add {offset : Nat} (h : offset ≤ 136) :
    scratch s + BitVec.ofNat 64 offset = stackPtr s - BitVec.ofNat 64 (136 - offset) := by
  rw [← BitVec.ofNat_sub_ofNat_of_le 136 offset (by omega) h]
  change stackPtr s - 136 + BitVec.ofNat 64 offset = _
  rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.neg_sub, BitVec.add_assoc]
  rfl

theorem stack_codeApart (pre : CalleePre s boundary entryPC 32 32 280)
    {offset len codeOffset codeLen : Nat} (hoffset : offset ≤ 280)
    (hlen : len ≤ offset + 8) (hcode : codeOffset + codeLen ≤ 118431) :
    RangeApart (stackPtr s - BitVec.ofNat 64 offset) len
      (Extracted.textAddress + BitVec.ofNat 64 codeOffset) codeLen := by
  intro i hi j hj he
  apply pre.avoids (Stack.region s 280) (by simp) _
    (ScalarFrame.stack_contains pre hoffset hlen ⟨i, hi, rfl⟩) (.inl ?_)
  rw [he, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact inProgram_of_textOffset (codeOffset + j) (by omega)

theorem copy_pre (pre : CalleePre s boundary entryPC 32 32 280)
    (state : FrameState s t) (rip : t.RIP = (if square then 0x113823 else 0x1138b3)) : CopyPre square t := by
  refine ⟨rip, ?_, ?_, ?_⟩
  · intro k hk
    change MemReadable t (stackPtr t + BitVec.ofNat 64 (8*k)) 8
    rw [state.rsp, scratch_add (by omega)]
    exact readable_of_grow
      (stack_sub_readable pre.stack (by omega) (by omega)) state.allocated
  · intro k hk
    change MemWritable t (stackPtr t + BitVec.ofNat 64 (8*k)) 8
    rw [state.rsp, scratch_add (by omega)]
    exact writable_of_grow
      (stack_sub_writable8 pre.stack (fun a ha hp => pre.avoids _ (by simp) a ha (.inr hp)) (by omega) (by omega)) state.allocated
  · intro k hk off len hlen
    change RangeApart (stackPtr t + BitVec.ofNat 64 (8*k)) 8 _ len
    rw [state.rsp, scratch_add (by omega)]
    exact stack_codeApart pre (by omega) (by omega) hlen

omit [Bindings] in
theorem copy_memory_component {c : Component} {a : BitVec 64}
    (hc : c ∈ (copyEffect square t).components) (ha : c.Covers a) :
    ∃ k < 8, ∃ i < 8, a = stackPtr t + BitVec.ofNat 64 (8*k) + BitVec.ofNat 64 i := by
  simp only [copyEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component_reg, Write.component_mem, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  all_goals obtain ⟨i, hi, rfl⟩ := ha
  · exact ⟨0, by decide, i, hi, rfl⟩
  · exact ⟨1, by decide, i, hi, rfl⟩
  · exact ⟨2, by decide, i, hi, rfl⟩
  · exact ⟨3, by decide, i, hi, rfl⟩
  · exact ⟨4, by decide, i, hi, rfl⟩
  · exact ⟨5, by decide, i, hi, rfl⟩
  · exact ⟨6, by decide, i, hi, rfl⟩
  · exact ⟨7, by decide, i, hi, rfl⟩

theorem copy_state (pre : CalleePre s boundary entryPC 32 32 280)
    (state : FrameState s t) (ready : ReadyToStep u) (effect : (copyEffect square t).Holds t u) :
    FrameState s u := by
  have saved := state.toSavedState.after_agrees pre ready effect.agrees
  have stateU : SavedState s u := saved (by
    intro c hc a ha
    obtain ⟨k, hk, i, hi, rfl⟩ := copy_memory_component hc ha
    refine ⟨workRegion s, by simp, ?_⟩
    rw [state.rsp, scratch_add (by omega)]
    exact ScalarFrame.Work.contains pre (by omega) (by omega) ⟨i, hi, rfl⟩)
    (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      all_goals first
        | exact effect.agrees.read (r := 5) (n := 64) (by simp [copyEffect, Effect.components])
        | exact effect.agrees.read (r := 12) (n := 64) (by simp [copyEffect, Effect.components])
        | exact effect.agrees.read (r := 13) (n := 64) (by simp [copyEffect, Effect.components])
        | exact effect.agrees.read (r := 14) (n := 64) (by simp [copyEffect, Effect.components])
        | exact effect.agrees.read (r := 15) (n := 64) (by simp [copyEffect, Effect.components]))
    (by simp [copyEffect, Effect.components]) (by simp [copyEffect, Effect.components])
    (by simp [copyEffect, Effect.components])
  exact ⟨stateU,
    (effect.agrees.read (r := 4) (n := 64) (by simp [copyEffect, Effect.components])).trans state.rsp,
    (effect.agrees.read (r := 3) (n := 64) (by simp [copyEffect, Effect.components])).trans state.rbx⟩

theorem copy_bytes_at (pre : CalleePre s boundary entryPC 32 32 280)
    (state : FrameState s t) (effect : (copyEffect square t).Holds t u) :
    ∀ i < 64, u.external[scratch s + BitVec.ofNat 64 i]? =
      t.external[scratch s + 64 + BitVec.ofNat 64 i]? := by
  have hw := effect.writes
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ at hw
  rcases hw with ⟨_, _, _, _, _, h0, h1, h2, h3, h4, h5, h6, h7⟩
  have hsp : rspOf t = scratch s := state.rsp
  intro i hi
  have hread : memLoad u.external (scratch s + BitVec.ofNat 64 (i / 8 * 8)) 64 =
      memLoad t.external (scratch s + 64 + BitVec.ofNat 64 (i / 8 * 8)) 64 := by
    have hdiv : i / 8 = 0 ∨ i / 8 = 1 ∨ i / 8 = 2 ∨ i / 8 = 3 ∨
        i / 8 = 4 ∨ i / 8 = 5 ∨ i / 8 = 6 ∨ i / 8 = 7 := by omega
    rcases hdiv with h | h | h | h | h | h | h | h
    all_goals simp only [h, Nat.reduceMul, BitVec.add_assoc, BitVec.reduceAdd]
    · simpa [hsp, Write.AllHold, Operand.read] using h0
    · simpa [hsp, Write.AllHold, Operand.read] using h1
    · simpa [hsp, Write.AllHold, Operand.read] using h2
    · simpa [hsp, Write.AllHold, Operand.read] using h3
    · simpa [hsp, Write.AllHold, Operand.read] using h4
    · simpa [hsp, Write.AllHold, Operand.read] using h5
    · simpa [hsp, Write.AllHold, Operand.read] using h6
    · simpa [hsp, Write.AllHold, Operand.read] using h7
  have hbytes := memByte_of_memLoad_eq hread (i % 8) (by omega)
  have hi' : i / 8 * 8 + i % 8 = i := by omega
  simp only [BitVec.add_assoc, ← BitVec.ofNat_add, hi'] at hbytes
  have dest : (u.external[scratch s + BitVec.ofNat 64 i]?).isSome :=
    effect.agrees.grow _ (state.allocated _
      ((stack_sub_readable pre.stack (offset := 136) (len := 64)
        (by decide) (by decide)).mem i hi))
  have source : (t.external[scratch s + 64 + BitVec.ofNat 64 i]?).isSome := by
    have hd : scratch s + 64 = stackPtr s - 72 := by
      simp only [scratch, BitVec.sub_eq_add_neg, BitVec.add_assoc]
      rfl
    rw [hd]
    exact state.allocated _
      ((stack_sub_readable pre.stack (offset := 72) (len := 64)
        (by decide) (by decide)).mem i hi)
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp dest
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp source
  have he : a = b := by simpa only [← BitVec.add_assoc, memByte, PhysicalMemory.read, ha, hb, Option.getD_some] using hbytes
  rw [ha, hb, he]

theorem copy_stage_at (square : Bool) (pre : CalleePre s boundary entryPC 32 32 280)
    (state : FrameState s t) (rip : t.RIP = (if square then 0x113823 else 0x1138b3)) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u ∧
      (copyEffect square t).Holds t u := by
  obtain ⟨fuel, u, run, ready, _, effect⟩ := copy_block square boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (by
      cases square
      · exact programText_slice (programLoaded_codeIn state.loaded) 0x138b3 copyBytes
          (by decide) (copy_bytes_code false)
      · exact programText_slice (programLoaded_codeIn state.loaded) 0x13823 copyBytes
          (by decide) (copy_bytes_code true)) (copy_pre pre state rip)
  exact ⟨fuel, u, run, copy_state pre state ready effect, effect⟩


theorem copy_stage (pre : MultiplyPre s boundary)
    (state : FrameState s t) (rip : t.RIP = 0x1138b3) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u ∧
      (copyEffect false t).Holds t u := by
  exact copy_stage_at false pre.toCalleePre state rip

theorem copy_bytes (pre : MultiplyPre s boundary)
    (state : FrameState s t) (effect : (copyEffect false t).Holds t u) :
    ∀ i < 64, u.external[scratch s + BitVec.ofNat 64 i]? =
      t.external[scratch s + 64 + BitVec.ofNat 64 i]? := by
  exact copy_bytes_at pre.toCalleePre state effect

end P256.Proofs.Field.Montgomery.Wrapper
