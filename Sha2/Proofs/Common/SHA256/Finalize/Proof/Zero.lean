import Sha2.Proofs.Common.SHA256.Finalize.Proof.Frame

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Finalize

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

theorem zero_frame {p : BitVec 64} {offset : Blocks.Zero.Offset} {s t : RamState}
    (effect : (Blocks.Zero.effect p offset s).Holds s t) :
    AgreesExcept [.mem (rspOf s + BitVec.ofNat 64 offset.value) 56, .rip] s t := by
  have cover (k : Nat) (bound : k + 8 ≤ 56) (a : BitVec 64)
      (covered : (Component.mem (rspOf s + BitVec.ofNat 64 (offset.value + k)) 8).Covers a) :
      (Component.mem (rspOf s + BitVec.ofNat 64 offset.value) 56).Covers a := by
    obtain ⟨i, hi, rfl⟩ := covered
    refine ⟨k + i, by omega, ?_⟩
    simp only [BitVec.ofNat_add, BitVec.add_assoc]
  apply Common.Encoding.Serialize.agrees_of_footprint effect.agrees
  · intro c hc noMem
    simp only [Blocks.Zero.effect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    all_goals simp_all [Component.isMem]
  · intro c hc a covered
    simp only [Blocks.Zero.effect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    all_goals try exact covered.elim
    all_goals refine ⟨.mem (rspOf s + BitVec.ofNat 64 offset.value) 56, by simp, ?_⟩
    · exact cover 0 (by decide) a covered
    · exact cover 8 (by decide) a covered
    · exact cover 16 (by decide) a covered
    · exact cover 24 (by decide) a covered
    · exact cover 32 (by decide) a covered
    · exact cover 40 (by decide) a covered
    · exact cover 48 (by decide) a covered

theorem zero_words {p : BitVec 64} {offset : Blocks.Zero.Offset} {s t : RamState}
    (effect : (Blocks.Zero.effect p offset s).Holds s t) :
    ∀ j < 7, memLoad t.external (rspOf s + BitVec.ofNat 64 offset.value + BitVec.ofNat 64 (8*j)) 64 = 0 := by
  have words := effect.writes
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ at words
  intro j bound
  have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [Nat.mul_zero, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
  · exact words.1
  · simpa only [Write.AllHold, Operand.read, BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using words.2.1
  · simpa only [Write.AllHold, Operand.read, BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using words.2.2.1
  · simpa only [Write.AllHold, Operand.read, BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using words.2.2.2.1
  · simpa only [Write.AllHold, Operand.read, BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using words.2.2.2.2.1
  · simpa only [Write.AllHold, Operand.read, BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using words.2.2.2.2.2.1
  · simpa only [Write.AllHold, Operand.read, BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using words.2.2.2.2.2.2

theorem hasBytes_zero_of_words {t : RamState} {base : BitVec 64}
    (read : MemReadable t base 56)
    (words : ∀ j < 7, memLoad t.external (base + BitVec.ofNat 64 (8*j)) 64 = 0) :
    (⟨base.toNat, 56⟩ : MemoryRegion).HasBytes t.external ⟨Array.replicate 56 0⟩ := by
  refine ⟨by simp [MemoryRegion.HasLength, ByteArray.size], ?_⟩
  intro i
  have hi : i.val < 56 := by simpa only [ByteArray.size, Array.size_replicate] using i.isLt
  have bytes := Bytes.of_memLoad (n := 64) (m := t.external)
    (a := base + BitVec.ofNat 64 (8*(i.val/8))) (by
      intro k hk
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact read.mem _ (by omega))
  rw [words (i.val/8) (by omega)] at bytes
  have byte := bytes (i.val%8) (by omega)
  rw [BitVec.add_assoc, ← BitVec.ofNat_add,
    show 8*(i.val/8)+i.val%8 = i.val by omega] at byte
  simpa [BitVec.ofNat_add, BitVec.ofNat_toNat, storedByte, ByteArray.getElem_eq_getElem_data] using byte

theorem zero [Bindings] {L : Layout} {initial before s : RamState}
    {n reserve : Nat} {regions : Vector MemoryRegion n} {message : ByteArray} {hash : Array UInt32}
    (ctx : Context L initial regions reserve) (input : Working L initial before s regions message hash)
    (rip : s.RIP = L.zero) :
    ∃ t, Working L initial before t regions message hash ∧ t.RIP = L.length ∧
      (⟨(L.buffer (L.sp initial)).toNat, 56⟩ : MemoryRegion).HasBytes
        t.external ⟨Array.replicate 56 0⟩ := by
  have inside : BlockInProgram L.zero L.variant.buffer.length := by
    have h := ctx.code.inside .zero
    have size : ∀ offset, (Blocks.Zero.bytes offset).length = offset.length := by
      intro offset
      cases offset <;> rfl
    change BlockInProgram L.zero (Blocks.Zero.bytes L.variant.buffer).length at h
    rwa [size] at h
  have writable (i : Nat) (hi : i + 8 ≤ 56) :
      MemWritable s (rspOf s + BitVec.ofNat 64 (L.variant.buffer.value+i)) 8 := by
    rw [show rspOf s = L.sp initial from input.rsp]
    exact ctx.writable input.state (by have := ctx.wf.bufferFits; omega) (by decide)
  have apart (i : Nat) (hi : i + 8 ≤ 56) :
      RangeApart (rspOf s + BitVec.ofNat 64 (L.variant.buffer.value+i)) 8 L.zero L.variant.buffer.length := by
    rw [show rspOf s = L.sp initial from input.rsp]
    exact ctx.codeApart (by have := ctx.wf.bufferFits; omega) inside
  have pre : Blocks.Zero.Pre L.zero L.variant.buffer s :=
    ⟨rip, writable 0 (by decide), apart 0 (by decide), writable 8 (by decide), apart 8 (by decide),
      writable 16 (by decide), apart 16 (by decide), writable 24 (by decide), apart 24 (by decide),
      writable 32 (by decide), apart 32 (by decide), writable 40 (by decide), apart 40 (by decide),
      writable 48 (by decide), apart 48 (by decide)⟩
  obtain ⟨_, t, run, ready, _, effect⟩ := Blocks.Zero.run L.zero L.variant.buffer
    (returnBoundary initial) ctx.outside inside s (supportedMachine_readyToStep input.state.machine)
      (ctx.code.loaded .zero s input.state.loaded) pre
  have frame : AgreesExcept [.mem (L.buffer (L.sp initial)) 56, .rip] s t := by
    simpa only [Layout.buffer, show rspOf s = L.sp initial from input.rsp] using zero_frame effect
  have preserved := input.toPreserved.of_agrees ctx run ready frame
    (by
      intro c hc a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · refine ⟨⟨(L.buffer (L.sp initial)).toNat, 64⟩, by simp [footprint], ?_⟩
        exact ctx.local_cover (base := L.variant.buffer.value) (offset := 0)
          (by have := ctx.wf.bufferFits; omega) (by decide) ha
      · exact ha.elim)
    (by intro r _ _; simp) (by simp)
  have hashWords : HashStateAt t (L.hash (L.sp initial)) hash := by
    apply Sha2.Proofs.Wrapper.hashState_of_bytes input.hashWords
    intro i hi
    apply frame.byte
    intro c hc covered
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · obtain ⟨j, hj, he⟩ := covered
      have apart : OffsetsApart (BitVec.ofNat 64 L.variant.buffer.value) 56
          (BitVec.ofNat 64 (L.variant.buffer.value+64)) 32 := by
        cases L.variant <;> unfold OffsetsApart <;> decide +kernel
      apply apart.ne (L.sp initial) hj hi (by decide)
      simpa only [Layout.hash, Layout.buffer, BitVec.ofNat_add, BitVec.add_assoc,
        BitVec.ofNat_eq_ofNat] using he.symm
    · exact covered.elim
  refine ⟨t, ⟨⟨preserved, hashWords, ?_⟩, ?_, ?_⟩, effect.rip.trans ctx.flow.zero, ?_⟩
  · intro h
    exact (frame.read (n := 64) (r := L.variant.hashReg) (by simp)).trans (input.hashPointer h)
  · exact (frame.read (n := 64) (r := L.variant.registers.tail) (by simp)).trans input.tailLength
  · exact (frame.read (n := 64) (r := L.variant.registers.blocks) (by simp)).trans input.blocks
  · apply hasBytes_zero_of_words (ctx.readable preserved.state (by have := ctx.wf.bufferFits; omega))
    simpa only [Layout.buffer, show rspOf s = L.sp initial from input.rsp] using zero_words effect

end Sha2.Proofs.Common.SHA256.Finalize
