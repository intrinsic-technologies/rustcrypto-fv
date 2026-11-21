import P256.Proofs.Nonce.Update.Seeded.Absorb.Prefix.Buffer.Prepare
import P256.Proofs.Nonce.Update.Seeded.Absorb.Memory
import P256.Proofs.Nonce.UpdateValue.Absorb.Mathematics

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Seeded.Absorb.Prefix

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem copy [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {original state : State} (pre : DrbgCalleePre initial boundary 0x109f30 1856 original)
    (input : Entered initial s state) :
    ∃ fuel t, Advances boundary fuel s t ∧ Copied initial t state := by
  obtain ⟨fuel, t, run, ready, _, effect⟩ := Buffer.run boundary pre.outerBoundary s
    (readyToStep input.machine input.bindingsSupported) (Buffer.code input.loaded)
    (Buffer.block_pre pre input)
  have src : Buffer.source s = initial.regValue .rdi + 32 := input.valuePointer
  have dst : Buffer.destination s = scratch initial + 320 := input.bufferPointer
  have agrees : AgreesExcept [.reg 0, .reg 1,
      .mem (scratch initial + 320) 32, .rip] s t := by
    apply effect.agrees.widen
    · simp [Buffer.effect, Effect.components, Component.isMem]
    · intro a c hc cover
      have hc : c = .reg 0 ∨ c = .reg 1 ∨ c = .mem (Buffer.destination s) 8 ∨
          c = .mem (Buffer.destination s + 8) 8 ∨ c = .mem (Buffer.destination s + 16) 8 ∨
          c = .mem (Buffer.destination s + 24) 8 ∨ c = .rip := by
        simpa [Buffer.effect, Effect.components] using hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals try exact cover.elim
      all_goals obtain ⟨i, hi, rfl⟩ := cover
      all_goals refine ⟨.mem (scratch initial + 320) 32, by simp, ?_⟩
      all_goals rw [dst]
      · exact ⟨i, by omega, rfl⟩
      · exact ⟨8+i, by omega, by bv_omega⟩
      · exact ⟨16+i, by omega, by bv_omega⟩
      · exact ⟨24+i, by omega, by bv_omega⟩
  have writes : ∀ (c : Component), c ∈ [.reg 0, .reg 1, .mem (scratch initial + 320) 32, .rip] →
      ∀ (a : BitVec 64), c.Covers a → (ScalarFrame.workRegion initial 1856).Contains a.toNat := by
    intro c hc a cover
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    all_goals try exact cover.elim
    exact Update.Prepare.work_contains_scratch pre (by decide) cover
  have frame := Update.Absorb.frame_after pre input.toFrameState ready agrees (by simp) writes
  have preserved (offset len : Nat) (bound : offset + len < 2^64)
      (apart : offset + len ≤ 320 ∨ 352 ≤ offset) :
      ∀ i < len, t.external[scratch initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
        s.external[scratch initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
    intro i hi
    apply agrees.byte
    intro c hc cover
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    all_goals try exact cover.elim
    obtain ⟨j, hj, eq⟩ := cover
    bv_omega
  have value : (MemoryRegion.mk (scratch initial + 320).toNat 32).HasBytes t.external state.value := by
    apply P256.Proofs.Program.hasBytes_copy input.drbg.2
    apply HMAC.Key.Output.bytes_of_words (count := 4)
    · exact Update.Absorb.Prefix.state_readable pre input.toFrameState (by decide)
    · rw [← show stackPtr t = scratch initial from frame.rsp]
      exact ScalarFrame.stack_readable pre.callee frame (by decide) (by decide)
    · have h := effect.writes
      change _ ∧ _ ∧ memLoad t.external (Buffer.destination s) 64 = _ ∧
        memLoad t.external (Buffer.destination s + 8) 64 = _ ∧
        memLoad t.external (Buffer.destination s + 16) 64 = _ ∧
        memLoad t.external (Buffer.destination s + 24) 64 = _ at h
      rw [src, dst] at h
      intro j hj
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
      · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h.2.2.1
      · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat] using h.2.2.2.1
      · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat] using h.2.2.2.2.1
      · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat] using h.2.2.2.2.2
  have context := input.toContext.after_agrees pre ready agrees (by simp) (by simp) writes
    (preserved 64 24 (by decide) (.inl (by decide)))
  refine ⟨fuel, t, run, context, effect.rip,
    (agrees.read (n := 64) (r := 15) (by simp)).trans input.position,
    (agrees.read (n := 64) (r := 5) (by simp)).trans input.descriptors, ?_, value⟩
  · apply UpdateValue.Absorb.hmacStateAt_absorb_short input.hmac (by decide)
    · exact ⟨rfl, fun i => Fin.elim0 i⟩
    · have position := input.hmac.inner.position
      simp only [ByteArray.size_append, HMAC.keyPad_size, ByteArray.size_empty,
        Nat.add_zero, Nat.reduceMod, BitVec.add_assoc, BitVec.reduceAdd] at position ⊢
      simpa only [BitVec.add_zero] using
        (preserved 383 1 (by decide) (.inr (by decide)) 0 (by decide)).trans
          (by simpa only [BitVec.add_zero] using position)
    · intro i hi apart
      have h := preserved (256+i) 1 (by omega) (by rcases apart with ha | ha <;> omega) 0 (by decide)
      simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.add_zero] using h

end P256.Proofs.Nonce.Update.Seeded.Absorb.Prefix
