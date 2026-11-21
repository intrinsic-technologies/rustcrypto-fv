import P256.Proofs.Nonce.Update.Absorb.Prefix.TagHead
import P256.Proofs.Nonce.Update.Absorb.Prefix.TagTail
import P256.Proofs.Nonce.Update.Absorb.Prefix.State
import P256.Proofs.Nonce.UpdateValue.Absorb.Mathematics
import P256.Proofs.Nonce.Update.Absorb.Memory

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Absorb.Prefix

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

def tagComponents (initial : RamState) : List Component :=
  [.reg 0, .reg 3, .reg 15, .flags, .mem (scratch initial + 184) 1,
    .mem (scratch initial + 215) 1, .rip]

theorem tag_writes [Bindings] {initial : RamState} {boundary : ReturnBoundary} {state : State}
    (pre : DrbgCalleePre initial boundary 0x109f30 1856 state) :
    ∀ c ∈ tagComponents initial, ∀ a, c.Covers a →
      (ScalarFrame.workRegion initial 1856).Contains a.toNat := by
  intro c hc a cover
  simp only [tagComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact cover.elim
  all_goals exact Prepare.work_contains_scratch pre (by decide) cover

theorem tag_bytes {initial s t : RamState} (agrees : AgreesExcept (tagComponents initial) s t)
    (offset len : Nat) (bound : offset + len < 2^64)
    (apart : (offset + len ≤ 184 ∨ 185 ≤ offset) ∧ (offset + len ≤ 215 ∨ 216 ≤ offset)) :
    ∀ i < len, t.external[scratch initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      s.external[scratch initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  intro i hi
  apply agrees.byte
  intro c hc cover
  simp only [tagComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact cover.elim
  all_goals obtain ⟨j, hj, eq⟩ := cover
  all_goals bv_omega

set_option maxRecDepth 1024 in
theorem tag [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {state : State} (pre : DrbgCalleePre initial boundary 0x109f30 1856 state)
    (input : Copied initial s state) :
    ∃ fuel t, Advances boundary fuel s t ∧ Tagged initial t state := by
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
  obtain ⟨v, stepV, readyV, branch⟩ := jcc_rel32_effect_step 0x10a190 4 0x91 u ready
    (programText_slice (programLoaded_codeIn frameU.loaded) 0xa190 _ (by decide) (by decide +kernel))
    ⟨head.rip, by intro; decide⟩
  have zero : (StatusFlags.ofRFLAGS u.RFLAGS).ZF = false := head.flags.2.2.2.1
  have ripV : v.RIP = 0x10a196 := by
    rw [branch.rip]
    change (if (StatusFlags.ofRFLAGS u.RFLAGS).ZF then 0x10a227 else 0x10a196) = _
    simp only [zero, Bool.false_eq_true, ↓reduceIte]
  have runV : Advances boundary 1 u v := Advances.of_step stepV (.inl (by
    rw [ripV]
    exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xa196 (by decide))))
  have branchAgrees : AgreesExcept [.rip] u v := branch.agrees
  have beforeTail : AgreesExcept (tagComponents initial) s v :=
    (headAgrees.trans branchAgrees).mono (by simp [tagComponents])
  have frameV := frame_after pre input.toFrameState readyV beforeTail
    (by simp [tagComponents]) (tag_writes pre)
  have headWrites := head.writes
  change u.regValue .r15 = 32 ∧ memLoad u.external (stackPtr s + 215) 8 = 32 ∧
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
  change memLoad t.external (stackPtr v + 184) 8 = 0 ∧ t.regValue .rbx = 33 ∧
    memLoad t.external (stackPtr v + 215) 8 = 33 at tailWrites
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
  have value : (MemoryRegion.mk (scratch initial + 152).toNat state.value.size).HasBytes t.external state.value := by
    rw [input.drbg.value_size]
    exact hasBytes_copy input.value (tag_bytes agrees 152 32 (by decide) (by omega))
  have zeroByte : t.external[scratch initial + 184]? = some 0 := byte 184 (by decide) 0 tailWrites.1
  have position : t.external[scratch initial + 215]? = some 33 := byte 215 (by decide) 33 tailWrites.2.2
  refine ⟨fuel + 1 + tailFuel, t, (run.trans runV).trans tailRun, frameT, tail.rip,
    drbg_after pre input.drbg agrees (tag_writes pre), ?_, ?_, ?_,
    (agrees.read (n := 64) (r := 5) (by simp [tagComponents])).trans input.descriptors,
    (agrees.read (n := 64) (r := 13) (by simp [tagComponents])).trans input.inputCount⟩
  · apply UpdateValue.Absorb.hmacStateAt_absorb_short input.hmac
    · simp only [ByteArray.size_append, input.drbg.value_size]
      decide
    · have bytes := hasBytes_append value (hasBytes_singleton (by
        simpa only [input.drbg.value_size, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using zeroByte))
      simpa only [input.drbg.value_size, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using bytes
    · simp only [ByteArray.size_append, input.drbg.value_size, BitVec.add_assoc, BitVec.reduceAdd]
      exact position
    · intro i hi apart
      have h := tag_bytes agrees (88+i) 1 (by omega) (by rcases apart with ha | ha <;> omega) 0 (by decide)
      simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.add_zero] using h
  · calc
      memLoad t.external (scratch initial + 72) 64 = memLoad s.external (scratch initial + 72) 64 := by
        apply memLoad_congr
        intro i hi
        exact congrArg (fun x : Option UInt8 => x.getD 0) (tag_bytes agrees 72 8 (by decide) (by omega) i hi)
      _ = initial.regValue .rdi := input.savedPointer
  · calc
      memLoad t.external (scratch initial + 64) 64 = memLoad s.external (scratch initial + 64) 64 := by
        apply memLoad_congr
        intro i hi
        exact congrArg (fun x : Option UInt8 => x.getD 0) (tag_bytes agrees 64 8 (by decide) (by omega) i hi)
      _ = initial.regValue .rdi + 32 := input.savedValue

end P256.Proofs.Nonce.Update.Absorb.Prefix
