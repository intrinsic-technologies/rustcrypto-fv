import P256.Proofs.Verifying.Message.Hash.Finalize.Compress.Blocks.Memory
import P256.Proofs.Verifying.Message.Hash.Finalize.Compress.Blocks.ZeroMachine

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Hash.Finalize.Compress.Blocks

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program SHA256

theorem zero_frame {initial s t : RamState} (rsp : stackPtr s = stackPtr initial - 1176)
    (effect : (ZeroMachine.effect s).Holds s t) :
    AgreesExcept [.mem (stackPtr initial - 1048) 56, .rip] s t := by
  have cover (offset : Nat) (bound : offset + 8 ≤ 56) (a : BitVec 64)
      (covered : (Component.mem (rspOf s + 128 + BitVec.ofNat 64 offset) 8).Covers a) :
      (Component.mem (stackPtr initial - 1048) 56).Covers a := by
    obtain ⟨i, hi, rfl⟩ := covered
    refine ⟨offset + i, by omega, ?_⟩
    change (stackPtr s + 128) + _ + _ = _
    rw [rsp, BitVec.add_assoc, ← BitVec.ofNat_add]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd]
  apply agrees_of_footprint effect.agrees
  · intro c hc noMem
    simp only [ZeroMachine.effect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    all_goals simp_all [Component.isMem]
  · intro c hc a covered
    simp only [ZeroMachine.effect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    all_goals try exact covered.elim
    all_goals refine ⟨.mem (stackPtr initial - 1048) 56, by simp, ?_⟩
    · exact cover 0 (by decide) a (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] using covered)
    · exact cover 8 (by decide) a (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] using covered)
    · exact cover 16 (by decide) a (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] using covered)
    · exact cover 24 (by decide) a (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] using covered)
    · exact cover 32 (by decide) a (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] using covered)
    · exact cover 40 (by decide) a (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] using covered)
    · exact cover 48 (by decide) a (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] using covered)

theorem zero_words {s t : RamState} (effect : (ZeroMachine.effect s).Holds s t) :
    ∀ j < 7, memLoad t.external (rspOf s + BitVec.ofNat 64 (128 + 8 * j)) 64 = 0 := by
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

theorem zero [Bindings] {initial s : RamState} {message : ByteArray} {boundary : ReturnBoundary}
    {hash : Array UInt32} (pre : Message.Pre initial boundary message)
    (input : Working initial s boundary message hash) (rip : s.RIP = 0x10d7f5) (large : 56 ≤ message.size % 64) :
    ∃ t, Working initial t boundary message hash ∧ t.RIP = 0x10d849 ∧
      (⟨(stackPtr initial - 1048).toNat, 56⟩ : MemoryRegion).HasBytes
        t.external (finalPrefix message) := by
  have hp : ZeroMachine.Pre s := by
    refine ⟨rip, ?_, ?_⟩
    · intro i member
      rw [stack_address input.rsp]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp only [BitVec.reduceSub]
      all_goals exact stack_writable8 pre input.toFrameState (by decide) (by decide)
    · intro i member offset len bound
      rw [stack_address input.rsp]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp only [BitVec.reduceSub]
      all_goals exact stack_codeApart pre (by decide) (by decide) bound
  obtain ⟨_, t, run, ready, _, effect⟩ :=
    ZeroMachine.run boundary pre.outerBoundary
      s (readyToStep input.machine input.bindingsSupported) (ZeroMachine.code input.loaded) hp
  have frame := zero_frame input.rsp effect
  have preserved := preserve pre input.toHashAt run ready frame (by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · obtain ⟨i, hi, eq⟩ := ha
      exact Or.inl ⟨i, by omega, eq⟩
    · exact ha.elim) (by simp) (by simp)
  refine ⟨t, ⟨preserved, ?_, ?_⟩, effect.rip, ?_⟩
  · exact (frame.read (n := 64) (r := 12) (by simp)).trans input.blocks
  · exact (frame.read (n := 64) (r := 15) (by simp)).trans input.tailLength
  · simp only [finalPrefix, show ¬ message.size % 64 < 56 by omega, ite_false]
    refine ⟨by simp [MemoryRegion.HasLength, ByteArray.size], ?_⟩
    intro i
    have hi : i.val < 56 := by simpa only [ByteArray.size, Array.size_replicate] using i.isLt
    have readable := stack_readable pre preserved.toFrameState (offset := 1048) (len := 56) (by decide) (by decide)
    have words := zero_words effect (i.val / 8) (by omega)
    have baseAddress (j : Nat) : rspOf s + BitVec.ofNat 64 (128+j) =
        stackPtr initial - 1048 + BitVec.ofNat 64 j := by
      change stackPtr s + _ = _
      rw [input.rsp, BitVec.ofNat_add]
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.ofNat_eq_ofNat]
      rw [← BitVec.add_assoc (-1176#64) (128#64)]
      rfl
    have bytes : Bytes t.external (rspOf s + BitVec.ofNat 64 (128 + 8 * (i.val / 8))) 8
        (storedByte (memLoad t.external (rspOf s + BitVec.ofNat 64 (128 + 8 * (i.val / 8))) 64)) := by
      apply Bytes.of_memLoad (n := 64)
      intro k hk
      rw [baseAddress, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact readable.mem _ (by omega)
    have byte := bytes (i.val % 8) (by omega)
    rw [words] at byte
    change t.external[BitVec.ofNat 64 ((stackPtr initial - 1048).toNat + i.val)]? = _
    rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have address : rspOf s + BitVec.ofNat 64 (128 + 8 * (i.val / 8)) + BitVec.ofNat 64 (i.val % 8) =
        stackPtr initial - 1048 + BitVec.ofNat 64 i.val := by
      rw [baseAddress, BitVec.add_assoc, ← BitVec.ofNat_add]
      congr 2
      omega
    rw [address] at byte
    simpa [storedByte, ByteArray.getElem_eq_getElem_data] using byte

end P256.Proofs.Verifying.Message.Hash.Finalize.Compress.Blocks
