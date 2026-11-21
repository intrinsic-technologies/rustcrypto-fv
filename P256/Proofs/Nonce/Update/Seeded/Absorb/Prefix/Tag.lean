import P256.Proofs.Nonce.Update.Seeded.Absorb.Prefix.TagHead
import P256.Proofs.Nonce.Update.Seeded.Absorb.Prefix.TagTail
import P256.Proofs.Nonce.Update.Seeded.Absorb.Memory
import P256.Proofs.Nonce.UpdateValue.Absorb.Mathematics
import P256.Proofs.Nonce.Update.Absorb.Memory

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Seeded.Absorb.Prefix

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open Update.Absorb

def tagComponents (initial : RamState) : List Component :=
  [.reg 0, .reg 13, .reg 14, .reg 15, .flags, .mem (scratch initial + 352) 1,
    .mem (scratch initial + 383) 1, .rip]

theorem tag_writes [Bindings] {initial : RamState} {boundary : ReturnBoundary} {original : State}
    (pre : DrbgCalleePre initial boundary 0x109f30 1856 original) :
    ∀ c ∈ tagComponents initial, ∀ a, c.Covers a →
      (ScalarFrame.workRegion initial 1856).Contains a.toNat := by
  intro c hc a cover
  simp only [tagComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact cover.elim
  all_goals exact Update.Prepare.work_contains_scratch pre (by decide) cover

theorem tag_bytes {initial s t : RamState} (agrees : AgreesExcept (tagComponents initial) s t)
    (offset len : Nat) (bound : offset + len < 2^64)
    (apart : (offset + len ≤ 352 ∨ 353 ≤ offset) ∧ (offset + len ≤ 383 ∨ 384 ≤ offset)) :
    ∀ i < len, t.external[scratch initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      s.external[scratch initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  intro i hi
  apply agrees.byte
  intro c hc cover
  simp only [tagComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact cover.elim
  all_goals obtain ⟨j, hj, eq⟩ := cover
  all_goals bv_omega

set_option maxRecDepth 1024 in
theorem tag [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {original state : State} (pre : DrbgCalleePre initial boundary 0x109f30 1856 original)
    (input : Copied initial s state) :
    ∃ fuel t, Advances boundary fuel s t ∧ Loop initial t state (state.value ++ ⟨#[1]⟩) 0 := by
  have hp : TagHead.Pre s := ⟨input.rip, input.position,
    stack_writable1 pre input.toFrameState (by decide), fun pc len bound =>
      ScalarFrame.stack_code pre.callee input.toFrameState (by decide) (by decide) bound⟩
  obtain ⟨fuel, u, run, ready, _, head⟩ := TagHead.run boundary pre.outerBoundary s
    (readyToStep input.machine input.bindingsSupported) (TagHead.code input.loaded) hp
  have headAgrees : AgreesExcept (tagComponents initial) s u := by
    have h := head.agrees
    simp only [TagHead.effect, Effect.components, List.map, Write.component, Operand.component] at h
    rw [show rspOf s = scratch initial from input.rsp] at h
    exact h.mono (by simp [tagComponents])
  have frameU := frame_after pre input.toFrameState ready headAgrees
    (by simp [tagComponents]) (tag_writes pre)
  obtain ⟨v, stepV, readyV, branch⟩ := jcc_rel32_effect_step 0x10a677 4 0x8b u ready
    (programText_slice (programLoaded_codeIn frameU.loaded) 0xa677 _ (by decide) (by decide +kernel))
    ⟨head.rip, by intro; decide⟩
  have zero : (StatusFlags.ofRFLAGS u.RFLAGS).ZF = false := head.flags.2.2.2.1
  have ripV : v.RIP = 0x10a67d := by
    rw [branch.rip]
    change (if (StatusFlags.ofRFLAGS u.RFLAGS).ZF then 0x10a708 else 0x10a67d) = _
    simp only [zero, Bool.false_eq_true, ↓reduceIte]
  have runV : Advances boundary 1 u v := Advances.of_step stepV (.inl (by
    rw [ripV]
    exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xa67d (by decide))))
  have branchAgrees : AgreesExcept [.rip] u v := branch.agrees
  have beforeTail : AgreesExcept (tagComponents initial) s v :=
    (headAgrees.trans branchAgrees).mono (by simp [tagComponents])
  have frameV := frame_after pre input.toFrameState readyV beforeTail
    (by simp [tagComponents]) (tag_writes pre)
  have headWrites := head.writes
  change u.regValue .r15 = 32 ∧ memLoad u.external (stackPtr s + 383) 8 = 32 ∧
    u.regValue .rax = 32 at headWrites
  have tp : TagTail.Pre v := by
    refine ⟨ripV, (branchAgrees.read (n := 64) (r := 0) (by simp)).trans headWrites.2.2, ?_, ?_⟩
    · intro off member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> exact stack_writable1 pre frameV (by decide)
    · intro off member pc len bound
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;>
        exact ScalarFrame.stack_code pre.callee frameV (by decide) (by decide) bound
  obtain ⟨tailFuel, t, tailRun, readyT, _, tail⟩ := TagTail.run boundary pre.outerBoundary v
    readyV (TagTail.code frameV.loaded) tp
  have tailAgrees : AgreesExcept (tagComponents initial) v t := by
    have h := tail.agrees
    simp only [TagTail.effect, Effect.components, List.map, Write.component, Operand.component] at h
    rw [show rspOf v = scratch initial from frameV.rsp] at h
    exact h.mono (by simp [tagComponents])
  have agrees : AgreesExcept (tagComponents initial) s t :=
    (beforeTail.trans tailAgrees).mono (by simp)
  have frameT := frame_after pre input.toFrameState readyT agrees
    (by simp [tagComponents]) (tag_writes pre)
  have tailWrites := tail.writes
  change memLoad t.external (stackPtr v + 352) 8 = 1 ∧ t.regValue .rax = 33 ∧
    t.regValue .r14 = stackPtr v + 384 ∧ memLoad t.external (stackPtr v + 383) 8 = 33 ∧
    t.regValue .r13 = 0x11c930 at tailWrites
  rw [frameV.rsp] at tailWrites
  have byte (offset : Nat) (bound : offset < 680) (value : BitVec 8)
      (loaded : memLoad t.external (scratch initial + BitVec.ofNat 64 offset) 8 = value) :
      t.external[scratch initial + BitVec.ofNat 64 offset]? = some (UInt8.ofBitVec value) := by
    have readable := ScalarFrame.stack_readable (frameOffset := 680) pre.callee frameT (offset := offset) (len := 1) (by decide) (by omega)
    rw [frameT.rsp] at readable
    have bytes := Bytes.of_memLoad (n := 8) readable.mem
    change Bytes t.external (scratch initial + BitVec.ofNat 64 offset) 1
      (storedByte (memLoad t.external (scratch initial + BitVec.ofNat 64 offset) 8)) at bytes
    rw [loaded] at bytes
    have h := bytes 0 (by decide)
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, storedByte_eq_extract, Nat.mul_zero,
      BitVec.extractLsb'_eq_self] using h
  have value : (MemoryRegion.mk (scratch initial + 320).toNat state.value.size).HasBytes t.external state.value := by
    rw [input.drbg.value_size]
    exact P256.Proofs.Program.hasBytes_copy input.value (tag_bytes agrees 320 32 (by decide) (by omega))
  have tagByte : t.external[scratch initial + 352]? = some 1 := byte 352 (by decide) 1 tailWrites.1
  have position : t.external[scratch initial + 383]? = some 33 := byte 383 (by decide) 33 tailWrites.2.2.2.1
  have context := input.toContext.after_agrees pre readyT agrees
    (by simp [tagComponents]) (by simp [tagComponents]) (tag_writes pre)
    (by simpa only [BitVec.ofNat_eq_ofNat] using tag_bytes agrees 64 24 (by decide) (by omega))
  refine ⟨fuel + 1 + tailFuel, t, (run.trans runV).trans tailRun, context, tail.rip,
    ?_, tailWrites.2.2.1, tailWrites.2.2.2.2, ?_⟩
  · change t.regValue .rbp = initial.regValue .rsi + 0#64
    rw [BitVec.add_zero]
    exact (agrees.read (n := 64) (r := 5) (by simp [tagComponents])).trans input.descriptors
  · apply UpdateValue.Absorb.hmacStateAt_absorb_short input.hmac
    · simp only [ByteArray.size_append, input.drbg.value_size]
      decide
    · have bytes := hasBytes_append value (hasBytes_singleton (by
        simpa only [input.drbg.value_size, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using tagByte))
      simpa only [input.drbg.value_size, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using bytes
    · simp only [ByteArray.size_append, input.drbg.value_size, BitVec.add_assoc, BitVec.reduceAdd]
      exact position
    · intro i hi apart
      have h := tag_bytes agrees (256+i) 1 (by omega) (by rcases apart with ha | ha <;> omega) 0 (by decide)
      simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.add_zero] using h

end P256.Proofs.Nonce.Update.Seeded.Absorb.Prefix
