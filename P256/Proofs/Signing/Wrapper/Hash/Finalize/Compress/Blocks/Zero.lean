import P256.Proofs.Signing.Wrapper.Hash.Finalize.Compress.Blocks.Memory
import P256.Proofs.Signing.Wrapper.Hash.Finalize.Compress.Blocks.ZeroMachine

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Hash.Finalize.Compress.Blocks

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program SHA256

theorem zero_frame {initial s t : RamState} (rsp : stackPtr s = stackPtr initial - 520)
    (effect : (ZeroMachine.effect s).Holds s t) :
    AgreesExcept [.mem (stackPtr initial - 456) 56, .rip] s t := by
  have cover (offset : Nat) (bound : offset + 8 ≤ 56) (a : BitVec 64)
      (covered : (Component.mem (rspOf s + BitVec.ofNat 64 (64+offset)) 8).Covers a) :
      (Component.mem (stackPtr initial - 456) 56).Covers a := by
    obtain ⟨i, hi, rfl⟩ := covered
    refine ⟨offset + i, by omega, ?_⟩
    have sp : rspOf s = stackPtr initial - 520 := rsp
    simp only [sp, BitVec.ofNat_add, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.ofNat_eq_ofNat]
    rw [← BitVec.add_assoc (-520#64) (64#64)]
    rfl
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
    all_goals refine ⟨.mem (stackPtr initial - 456) 56, by simp, ?_⟩
    · exact cover 0 (by decide) a covered
    · exact cover 8 (by decide) a covered
    · exact cover 16 (by decide) a covered
    · exact cover 24 (by decide) a covered
    · exact cover 32 (by decide) a covered
    · exact cover 40 (by decide) a covered
    · exact cover 48 (by decide) a covered

theorem zero_words {s t : RamState} (effect : (ZeroMachine.effect s).Holds s t) :
    ∀ j < 7, memLoad t.external (rspOf s + 64 + BitVec.ofNat 64 (8 * j)) 64 = 0 := by
  have words := effect.writes
  simp only [ZeroMachine.effect, Write.AllHold, Operand.read] at words
  intro j bound
  have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [rspOf, Operand.read, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] using words.1
  · simpa only [rspOf, Operand.read, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] using words.2.1
  · simpa only [rspOf, Operand.read, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] using words.2.2.1
  · simpa only [rspOf, Operand.read, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] using words.2.2.2.1
  · simpa only [rspOf, Operand.read, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] using words.2.2.2.2.1
  · simpa only [rspOf, Operand.read, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] using words.2.2.2.2.2.1
  · simpa only [rspOf, Operand.read, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] using words.2.2.2.2.2.2

theorem zero [Bindings] {initial start s : RamState} {secret message : ByteArray}
    {hash : Array UInt32} (pre : HashEntry initial start secret message)
    (input : Working initial start s message hash) (rip : s.RIP = 0x1028fe) (large : 56 ≤ message.size % 64) :
    ∃ t, Working initial start t message hash ∧ t.RIP = 0x10293d ∧
      (⟨(stackPtr initial - 456).toNat, 56⟩ : MemoryRegion).HasBytes
        t.external (finalPrefix message) := by
  have hp : ZeroMachine.Pre s := by
    refine ⟨rip, ?_, ?_⟩
    · intro i member
      rw [stack_address input.rsp]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp only [BitVec.reduceSub]
      all_goals exact stack_writable8 pre input.toFrame (by decide) (by decide)
    · intro i member offset len bound
      rw [stack_address input.rsp]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp only [BitVec.reduceSub]
      all_goals exact stack_codeApart pre (by decide) (by decide) bound
  obtain ⟨_, t, run, ready, _, effect⟩ :=
    ZeroMachine.run (returnBoundary initial) (outside pre.context)
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
  · exact (frame.read (n := 64) (r := 14) (by simp)).trans input.blocks
  · exact (frame.read (n := 64) (r := 3) (by simp)).trans input.tailLength
  · simp only [finalPrefix, show ¬ message.size % 64 < 56 by omega, ite_false]
    refine ⟨by simp [MemoryRegion.HasLength, ByteArray.size], ?_⟩
    intro i
    have hi : i.val < 56 := by simpa only [ByteArray.size, Array.size_replicate] using i.isLt
    have readable := stack_readable pre preserved.toFrame (offset := 456) (len := 56) (by decide) (by decide)
    have words := zero_words effect (i.val / 8) (by omega)
    have bytes : Bytes t.external (rspOf s + 64 + BitVec.ofNat 64 (8 * (i.val / 8))) 8
        (storedByte (memLoad t.external (rspOf s + 64 + BitVec.ofNat 64 (8 * (i.val / 8))) 64)) := by
      apply Bytes.of_memLoad (n := 64)
      intro k hk
      change (t.external[stackPtr s + 64 + _ + _]?).isSome
      rw [input.rsp]
      have norm : stackPtr initial - 520#64 + 64 = stackPtr initial - 456 := by
        simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
        rfl
      rw [norm, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact readable.mem _ (by omega)
    have byte := bytes (i.val % 8) (by omega)
    rw [words] at byte
    change t.external[BitVec.ofNat 64 ((stackPtr initial - 456).toNat + i.val)]? = _
    rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have address : rspOf s + 64 + BitVec.ofNat 64 (8 * (i.val / 8)) + BitVec.ofNat 64 (i.val % 8) =
        stackPtr initial - 456 + BitVec.ofNat 64 i.val := by
      change stackPtr s + 64 + _ + _ = _
      rw [input.rsp]
      have norm : stackPtr initial - 520#64 + 64 = stackPtr initial - 456 := by
        simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
        rfl
      rw [norm, BitVec.add_assoc, ← BitVec.ofNat_add]
      congr 2
      omega
    rw [address] at byte
    simpa [storedByte, ByteArray.getElem_eq_getElem_data] using byte

end P256.Proofs.Signing.Wrapper.Hash.Finalize.Compress.Blocks
