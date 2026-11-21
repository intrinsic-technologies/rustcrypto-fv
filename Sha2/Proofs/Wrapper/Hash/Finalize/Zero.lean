import Sha2.Proofs.Wrapper.Hash.Finalize.State
import Sha2.Proofs.Wrapper.Memory
import Sha2.Proofs.Wrapper.Hash.Padding.Zero

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper.Hash.Finalize

open Sha2.Spec Sha2.Proofs.Program Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.SHA256 Sha2.Proofs.Common.Machine

theorem zero_frame {v : Variant} {initial s t : RamState} (rsp : stackPtr s = stackPtr initial - 344)
    (effect : (Padding.Zero.effect s v).Holds s t) :
    AgreesExcept [.mem (stackPtr initial - 344) 56, .rip] s t := by
  have cover (offset : Nat) (bound : offset + 8 ≤ 56) (a : BitVec 64)
      (covered : (Component.mem (rspOf s + BitVec.ofNat 64 offset) 8).Covers a) :
      (Component.mem (stackPtr initial - 344) 56).Covers a := by
    obtain ⟨i, hi, rfl⟩ := covered
    refine ⟨offset + i, by omega, ?_⟩
    change stackPtr s + _ + _ = _
    rw [rsp, BitVec.add_assoc, ← BitVec.ofNat_add]
  apply Common.Encoding.Serialize.agrees_of_footprint effect.agrees
  · intro c hc noMem
    simp only [Padding.Zero.effect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    all_goals simp_all [Component.isMem]
  · intro c hc a covered
    simp only [Padding.Zero.effect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    all_goals try exact covered.elim
    all_goals refine ⟨.mem (stackPtr initial - 344) 56, by simp, ?_⟩
    · exact cover 0 (by decide) a covered
    · exact cover 8 (by decide) a covered
    · exact cover 16 (by decide) a covered
    · exact cover 24 (by decide) a covered
    · exact cover 32 (by decide) a covered
    · exact cover 40 (by decide) a covered
    · exact cover 48 (by decide) a covered

theorem zero_words {v : Variant} {s t : RamState} (effect : (Padding.Zero.effect s v).Holds s t) :
    ∀ j < 7, memLoad t.external (rspOf s + BitVec.ofNat 64 (8 * j)) 64 = 0 := by
  have words := effect.writes
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ at words
  intro j bound
  have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact words.1
  · exact words.2.1
  · exact words.2.2.1
  · exact words.2.2.2.1
  · exact words.2.2.2.2.1
  · exact words.2.2.2.2.2.1
  · exact words.2.2.2.2.2.2

theorem zero [Bindings] {v : Variant} {initial s : RamState} {inputs : Array Input} {message : ByteArray}
    {hash : Array UInt32} (ctx : Context initial inputs v)
    (input : Working initial s message hash v) (rip : s.RIP = (v.pc 0x276)) :
    ∃ t, Working initial t message hash v ∧ t.RIP = (v.pc 0x2b4) ∧
      (⟨(stackPtr initial - 344).toNat, 56⟩ : MemoryRegion).HasBytes
        t.external ⟨Array.replicate 56 0⟩ := by
  have pre : Padding.Zero.Pre s v := by
    refine ⟨rip, ?_, ?_⟩
    · intro i member
      rw [stack_address input.rsp]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp only [BitVec.reduceSub]
      all_goals exact stack_writable8 ctx input.toState (by decide) (by decide)
    · intro i member offset len bound
      rw [stack_address input.rsp]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp only [BitVec.reduceSub]
      all_goals exact stack_codeApart ctx (by decide) (by decide) bound
  obtain ⟨_, t, run, ready, _, effect⟩ :=
    Padding.Zero.run (v := v) (returnBoundary initial) (validCall_returnBoundary ctx.machine ctx.call).2.2
      s (supportedMachine_readyToStep input.machine) (Padding.Zero.code (v := v) input.loaded) pre
  have frame := zero_frame input.rsp effect
  have preserved := Wrapper.preserved_of_agrees ctx input.toPreserved run ready frame
    (by
      intro c hc a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact Wrapper.local_memory (by decide) (by decide) (.inl (by decide)) a ha
      · exact ha.elim) (by simp)
  have hash := Wrapper.hashState_of_bytes input.hashWords
    (Wrapper.store_bytes frame (offset := 280) (len := 32)
      (by unfold OffsetsApart; decide +kernel) (by decide))
  refine ⟨t, ⟨⟨preserved, hash, ?_⟩, ?_, ?_⟩, effect.rip, ?_⟩
  · exact (frame.read (n := 64) (r := 14) (by simp)).trans input.hashPointer
  · exact (frame.read (n := 64) (r := 12) (by simp)).trans input.blocks
  · exact (frame.read (n := 64) (r := 15) (by simp)).trans input.tailLength
  · refine ⟨by simp [MemoryRegion.HasLength, ByteArray.size], ?_⟩
    intro i
    have hi : i.val < 56 := by simpa only [ByteArray.size, Array.size_replicate] using i.isLt
    have readable := stack_readable ctx preserved.toState (offset := 344) (len := 56) (by decide) (by decide)
    have words := zero_words effect (i.val / 8) (by omega)
    have bytes : Bytes t.external (rspOf s + BitVec.ofNat 64 (8 * (i.val / 8))) 8
        (storedByte (memLoad t.external (rspOf s + BitVec.ofNat 64 (8 * (i.val / 8))) 64)) := by
      apply Bytes.of_memLoad (n := 64)
      intro k hk
      change (t.external[stackPtr s + _ + _]?).isSome
      rw [input.rsp, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact readable.mem _ (by omega)
    have byte := bytes (i.val % 8) (by omega)
    rw [words] at byte
    change t.external[BitVec.ofNat 64 ((stackPtr initial - 344).toNat + i.val)]? = _
    rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have address : rspOf s + BitVec.ofNat 64 (8 * (i.val / 8)) + BitVec.ofNat 64 (i.val % 8) =
        stackPtr initial - 344 + BitVec.ofNat 64 i.val := by
      change stackPtr s + _ + _ = _
      rw [input.rsp, BitVec.add_assoc, ← BitVec.ofNat_add]
      congr 2
      omega
    rw [address] at byte
    simpa [storedByte, ByteArray.getElem_eq_getElem_data] using byte

end Sha2.Proofs.Wrapper.Hash.Finalize
