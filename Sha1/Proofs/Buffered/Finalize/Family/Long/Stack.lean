import Sha1.Proofs.Buffered.Finalize.Family.Contracts
import Sha1.Proofs.Buffered.Finalize.Family.Long.Steps
import Sha1.Proofs.Buffered.Finalize.Digest.Final

namespace Sha1.Proofs.Buffered.Finalize.Family.Long

open Sha1.Spec Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha1.Proofs.Compress.Machine
open Sha1.Proofs.Buffered.Finalize.Steps (PartPre)
open Digest (covers_apart stack_offset)

private def stackWrites (s : RamState) (offset len : Nat) : List Component :=
  [.reg 0, .reg 1, .rip, .mem (stackPtr s + BitVec.ofNat 64 offset) len]

private theorem stack_bytes_preserved {s t : RamState} {offset len base count : Nat}
    (h : AgreesExcept (stackWrites s offset len) s t)
    (hwrite : offset + len ≤ 2^64) (hread : base + count ≤ 2^64)
    (hapart : offset + len ≤ base ∨ base + count ≤ offset) :
    ∀ i < count, t.external[stackPtr s + BitVec.ofNat 64 base + BitVec.ofNat 64 i]? =
      s.external[stackPtr s + BitVec.ofNat 64 base + BitVec.ofNat 64 i]? := by
  intro i hi
  apply h.byte
  intro c hc
  simp only [stackWrites, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  all_goals first | exact fun hcov ↦ hcov | exact covers_apart rfl hi hwrite hread hapart

private theorem stack_effect_run [Bindings] {b : ReturnBoundary} {s : RamState}
    {p : BitVec 64} {map : CodeMap} {effect : RamState → Effect} {offset len : Nat}
    (exec : AdvancesBlock b (PartPre .updateFinalizeCopy p) map effect)
    (storage : Storage .updateFinalizeCopy s) (ready : ReadyToStep s)
    (code : CodeIn Extracted.programImage s) (bytes : CodeIn map s) (rip : s.RIP = p)
    (hlimit : offset + len ≤ 192)
    (regs : ∀ c ∈ (effect s).components, c.isMem = false → c ∈ [.reg 0, .reg 1, .rip])
    (range : ∀ x c, c ∈ (effect s).components → c.Covers x →
      Component.Covers (.mem (stackPtr s + BitVec.ofNat 64 offset) len) x) :
    ∃ t, Run b s t ∧ AgreesExcept (stackWrites s offset len) s t ∧ (effect s).Holds s t := by
  obtain ⟨n, t, ha, ht, _, he⟩ := exec s ready bytes ⟨storage, rip⟩
  have ha' : AgreesExcept (stackWrites s offset len) s t := by
    apply he.agrees.widen
    · intro c hc hm
      change c ∈ ([.reg 0, .reg 1, .rip] ++ [.mem (stackPtr s + BitVec.ofNat 64 offset) len])
      exact List.mem_append.mpr (.inl (regs c hc hm))
    · intro x c hc hx
      exact ⟨_, by simp [stackWrites], range x c hc hx⟩
  have hout : offset + len ≤ Kind.updateFinalizeCopy.stackBytes := by
    simp only [Kind.stackBytes]
    omega
  have hsp : stackPtr t = stackPtr s :=
    ha'.read (n := 64) (r := 4) (by simp [stackWrites])
  refine ⟨t, ⟨⟨n, ha⟩, ht, ?_, hsp, ?_, ?_⟩, ha', he⟩
  · apply he.codeIn _ code
    intro x hx c hc hcov
    exact storage.stackAvoids x.1 (storage.stackCover hout (range x.1 c hc hcov))
      (.inl ⟨x.2, hx⟩)
  · unfold savedOutput
    rw [hsp]
    apply Digest.read_of_agrees ha'
    intro i hi c hc
    simp only [stackWrites, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    all_goals first | exact fun hcov ↦ hcov |
      exact covers_apart (b := 192) (count := 8) rfl hi
        (by omega) (by decide) (.inl hlimit)
  · apply agrees_changes ha'
    · intro c hc hm
      simp only [stackWrites, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl <;>
        simp_all [Component.isMem, Kind.changes]
    · intro x c hc hcov
      simp only [stackWrites, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals first | exact hcov.elim | exact storage.localWithin hout hcov

private theorem keep_state {H : Vector (BitVec 32) 5} {s t : RamState} {offset len : Nat}
    (h : AgreesExcept (stackWrites s offset len) s t) (hsp : stackPtr t = stackPtr s)
    (hwrite : offset + len ≤ 2^64) (hapart : offset + len ≤ 8 ∨ 28 ≤ offset)
    (hs : StateBytes s H) : StateBytes t H := by
  unfold StateBytes at hs ⊢
  rw [hsp]
  apply Digest.hasBytes_resize' _ (Wrapper.Hash.Serialize.stateBytes_size H)
  apply hasBytes_of_copy _ (Digest.hasBytes_resize hs (Wrapper.Hash.Serialize.stateBytes_size H).symm)
  intro i hi
  rw [Wrapper.Hash.Serialize.stateBytes_size] at hi
  exact stack_bytes_preserved h hwrite (base := 8) (count := 20)
    (by decide) hapart i hi

private theorem keep_position {m : ByteArray} {s t : RamState} {offset len : Nat}
    (h : AgreesExcept (stackWrites s offset len) s t) (hp : Position m s) : Position m t := by
  exact ⟨(h.read (by simp [stackWrites])).trans hp.position,
    (h.read (by simp [stackWrites])).trans hp.blocks⟩

local macro "solve_stack_copy_regs " effect:term : tactic =>
  `(tactic| (
  intro c hc hm
  simp only [$effect:term, Effect.components, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, Write.component, Operand.component,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  repeat' rcases hc with rfl | hc
  all_goals simp_all [Component.isMem]))

private theorem cover_stack_word {base x d : BitVec 64} {off total : Nat}
    (hx : Component.Covers (.mem (base + d) 8) x) (hle : off ≤ d.toNat)
    (hend : d.toNat + 8 ≤ off + total) :
    Component.Covers (.mem (base + BitVec.ofNat 64 off) total) x := by
  apply Digest.BlockCopy.cover_shift (d := d.toNat) _ hle hend
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using hx

local macro "solve_stack_copy_cover " effect:term : tactic =>
  `(tactic| (
  intro x c hc hx
  simp only [$effect:term, Effect.components, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, Write.component, Operand.component,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  repeat' rcases hc with rfl | hc
  all_goals try subst c
  all_goals first | exact hx.elim | exact cover_stack_word hx (by decide) (by decide)))

theorem copy_block [Bindings] {b : ReturnBoundary} {m : ByteArray} {s : RamState}
    (hOutside : ¬ InProgram b.rip) (storage : Storage .updateFinalizeCopy s)
    (ready : ReadyToStep s) (code : CodeIn Extracted.programImage s)
    (h : Padded m s) (hlong : 56 ≤ m.size % 64) :
    ∃ t, Run b s t ∧ t.RIP = 0x101e9d ∧ DirectionFlagClear t.RFLAGS ∧ Position m t ∧
      StateBytes t (absorbedHash m) ∧
      (⟨(stackPtr t + 128).toNat, 64⟩ : MemoryRegion).HasBytes t.external (Digest.firstBlock m) := by
  have hip : s.RIP = 0x101e35 := by
    simpa only [show ¬ m.size % 64 < 56 by omega, ite_false] using h.rip
  obtain ⟨u, hu, hagHigh, heHigh⟩ := stack_effect_run (offset := 160) (len := 32)
    (highCopy_execution b hOutside) storage ready code
    (program_text_slice code 0x1e35 52 (by decide +kernel)) hip (by decide)
    (by solve_stack_copy_regs highCopyEffect) (by solve_stack_copy_cover highCopyEffect)
  have hsU := storage.of_agrees hu.agrees hu.rsp
  obtain ⟨t, ht, hagLow, heLow⟩ := stack_effect_run (offset := 128) (len := 32)
    (lowCopy_execution b hOutside) hsU hu.ready hu.code
    (program_text_slice hu.code 0x1e69 52 (by decide +kernel)) heHigh.rip (by decide)
    (by solve_stack_copy_regs lowCopyEffect) (by solve_stack_copy_cover lowCopyEffect)
  have hsT := hsU.of_agrees ht.agrees ht.rsp
  have highWords := heHigh.writes
  have lowWords := heLow.writes
  simp only [highCopyEffect, lowCopyEffect, Write.AllHold] at highWords lowWords
  have high (j : Nat) (hj : j < 4) :
      (Operand.mem (stackPtr s + BitVec.ofNat 64 (160 + 8 * j)) : Operand 64).read u =
        (Operand.mem (stackPtr s + BitVec.ofNat 64 (64 + 8 * j)) : Operand 64).read s := by
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl
    · exact highWords.2.2.2.2
    · exact highWords.2.2.2.1
    · exact highWords.2.2.1
    · exact highWords.2.1
  have low (j : Nat) (hj : j < 4) :
      (Operand.mem (stackPtr u + BitVec.ofNat 64 (128 + 8 * j)) : Operand 64).read t =
        (Operand.mem (stackPtr u + BitVec.ofNat 64 (32 + 8 * j)) : Operand 64).read u := by
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl
    · exact lowWords.2.2.2.2.2
    · exact lowWords.2.2.2.2.1
    · exact lowWords.2.2.2.1
    · exact lowWords.2.2.1
  have hdfU : DirectionFlagClear u.RFLAGS :=
    (hagHigh.directionFlagClear (by simp [stackWrites]) ⟨h.df⟩).df
  refine ⟨t, hu.trans ht, heLow.rip,
    (hagLow.directionFlagClear (by simp [stackWrites]) ⟨hdfU⟩).df,
    keep_position hagLow (keep_position hagHigh h.toPosition),
    keep_state hagLow ht.rsp (by decide) (.inr (by decide))
      (keep_state hagHigh hu.rsp (by decide) (.inr (by decide)) h.state), ?_⟩
  apply Digest.hasBytes_of_bytes_size _ (Digest.size_firstBlock m)
  intro i hi
  have hsp := ht.rsp.trans hu.rsp
  rw [hsp, ← h.padded i hi]
  by_cases half : i < 32
  · have hw := stack_word_bytes hsU hsT ht.rsp
      (src := 32 + 8 * (i / 8)) (dst := 128 + 8 * (i / 8))
      (by simp only [Kind.stackBytes]; omega) (by simp only [Kind.stackBytes]; omega)
      (low (i / 8) (by omega)) (i % 8) (by omega)
    rw [hu.rsp, stack_offset, stack_offset,
      show 128 + 8 * (i / 8) + i % 8 = 128 + i by omega,
      show 32 + 8 * (i / 8) + i % 8 = 32 + i by omega, ← stack_offset, ← stack_offset] at hw
    exact hw.trans (stack_bytes_preserved hagHigh (base := 32) (count := 32)
      (by decide) (by decide) (.inr (by decide)) i half)
  · have hw := stack_word_bytes storage hsU hu.rsp
      (src := 64 + 8 * ((i - 32) / 8)) (dst := 160 + 8 * ((i - 32) / 8))
      (by simp only [Kind.stackBytes]; omega) (by simp only [Kind.stackBytes]; omega)
      (high ((i - 32) / 8) (by omega)) ((i - 32) % 8) (by omega)
    rw [stack_offset, stack_offset, show 160 + 8 * ((i - 32) / 8) + (i - 32) % 8 = 128 + i by omega,
      show 64 + 8 * ((i - 32) / 8) + (i - 32) % 8 = 32 + i by omega,
      ← stack_offset, ← stack_offset] at hw
    have hp := stack_bytes_preserved hagLow (base := 160) (count := 32)
      (by decide) (by decide) (.inl (by decide)) (i - 32) (by omega)
    rw [hu.rsp, stack_offset, show 160 + (i - 32) = 128 + i by omega, ← stack_offset] at hp
    exact hp.trans hw

theorem clear_block [Bindings] {b : ReturnBoundary} {m : ByteArray} {s : RamState}
    (hOutside : ¬ InProgram b.rip) (storage : Storage .updateFinalizeCopy s)
    (ready : ReadyToStep s) (code : CodeIn Extracted.programImage s) (rip : s.RIP = 0x101eb4)
    (df : DirectionFlagClear s.RFLAGS) (position : Position m s)
    (state : StateBytes s (penultimateHash m)) (hlong : 56 ≤ m.size % 64) :
    ∃ t, Run b s t ∧ Last m t := by
  obtain ⟨t, ht, hag, he⟩ := stack_effect_run (offset := 32) (len := 56)
    (clear_execution b hOutside) storage ready code
    (program_text_slice code 0x1eb4 63 (by decide +kernel)) rip (by decide)
    (by solve_stack_copy_regs clearEffect) (by solve_stack_copy_cover clearEffect)
  have hsT := storage.of_agrees ht.agrees ht.rsp
  refine ⟨t, ht, keep_position hag position, he.rip,
    (hag.directionFlagClear (by simp [stackWrites]) ⟨df⟩).df,
    keep_state hag ht.rsp (by decide) (.inr (by decide)) state, ?_⟩
  have writes := he.writes
  simp only [clearEffect, Write.AllHold] at writes
  have zero_word (j : Nat) (hj : j < 7) :
      memLoad t.external (stackPtr s + BitVec.ofNat 64 (32 + 8 * j)) 64 = 0 := by
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 by omega)
      with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact writes.1
    · exact writes.2.1
    · exact writes.2.2.1
    · exact writes.2.2.2.1
    · exact writes.2.2.2.2.1
    · exact writes.2.2.2.2.2.1
    · exact writes.2.2.2.2.2.2
  intro i hi
  have readable := (hsT.stackWritable (32 + 8 * (i / 8)) 8
    (by simp only [Kind.stackBytes]; omega)).mem
  rw [ht.rsp] at readable
  have hb := Bytes.of_memLoad (n := 64) readable (i % 8) (by omega)
  rw [zero_word (i / 8) (by omega), stack_offset, show 32 + 8 * (i / 8) + i % 8 = 32 + i by omega,
    ← stack_offset] at hb
  rw [ht.rsp]
  simp only [show ¬ m.size % 64 < 56 by omega, ite_false]
  simpa [storedByte] using hb

end Sha1.Proofs.Buffered.Finalize.Family.Long
