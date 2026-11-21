import P256.Proofs.Nonce.Update.Absorb.Prefix.Head
import P256.Proofs.Nonce.Update.Absorb.Prefix.State
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Absorb.Prefix

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

set_option maxRecDepth 1024 in
theorem enter [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {state : State} (pre : DrbgCalleePre initial boundary 0x109f30 1856 state)
    (input : Prepared initial s state) :
    ∃ fuel t, Advances boundary fuel s t ∧ Entered initial t state := by
  have headPre : Head.Pre s := by
    refine ⟨input.rip, ScalarFrame.stack_readable pre.callee input.toFrameState (by decide) (by decide), ?_, ?_, ?_⟩
    · have position := input.hmac.inner.position
      simp only [ByteArray.size_append, HMAC.keyPad_size, ByteArray.size_empty,
        Nat.add_zero, Nat.reduceMod, BitVec.add_assoc, BitVec.reduceAdd] at position
      change memLoad s.external (stackPtr s + 215) 8 = 0
      rw [input.rsp, memLoad_8]
      change ((s.external[scratch initial + 215]?).getD 0).toBitVec = 0
      simp only [BitVec.ofNat_eq_ofNat]
      rw [position]
      rfl
    · intro offset member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;>
        exact stack_writable8 pre input.toFrameState (by decide) (by decide)
    · intro offset member pc len bound
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;>
        exact ScalarFrame.stack_code pre.callee input.toFrameState (by decide) (by decide) bound
  obtain ⟨fuel, u, run, ready, _, effect⟩ := Head.run boundary pre.outerBoundary s
    (readyToStep input.machine input.bindingsSupported) (Head.code input.loaded) headPre
  have agrees : AgreesExcept [.reg 6, .reg 14, .reg 12, .reg 15,
      .mem (scratch initial + 72) 8, .mem (scratch initial + 64) 8, .flags, .rip] s u := by
    have h := effect.agrees
    simp only [Head.effect, Effect.components, List.map, Write.component, Operand.component] at h
    rwa [show rspOf s = scratch initial from input.rsp] at h
  have writes : ∀ (c : Component), c ∈ [.reg 6, .reg 14, .reg 12, .reg 15,
      .mem (scratch initial + 72) 8, .mem (scratch initial + 64) 8, .flags, .rip] →
      ∀ (a : BitVec 64), c.Covers a → (ScalarFrame.workRegion initial 1856).Contains a.toNat := by
    intro c hc a cover
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact cover.elim
    all_goals exact Prepare.work_contains_scratch pre (by decide) cover
  have frame := frame_after pre input.toFrameState ready agrees (by simp) writes
  obtain ⟨t, step, readyT, branch⟩ := jcc_rel8_effect_step 0x10a15a 7 0x4a u ready
    (programText_slice (programLoaded_codeIn frame.loaded) 0xa15a _ (by decide) (by decide +kernel))
    ⟨effect.rip, by intro; decide⟩
  have carry : (StatusFlags.ofRFLAGS u.RFLAGS).CF = true := effect.flags.1
  have rip : t.RIP = 0x10a15c := by
    rw [branch.rip]
    change (if !((StatusFlags.ofRFLAGS u.RFLAGS).CF ||
      (StatusFlags.ofRFLAGS u.RFLAGS).ZF) then 0x10a1a6 else 0x10a15c) = _
    simp only [carry, Bool.true_or, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  have runT : Advances boundary 1 u t := Advances.of_step step (.inl (by
    rw [rip]
    exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xa15c (by decide))))
  have last : AgreesExcept [.rip] u t := branch.agrees
  have memory := last.external (by simp [Component.Covers])
  have allAgrees := agrees.trans last
  have finalFrame := frame_after pre frame readyT last (by simp) (by
    intro c hc a cover
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst c
    exact cover.elim)
  have stores := effect.writes
  change u.regValue .rsi = s.regValue .rbx + 32 ∧
    u.regValue .r14 = stackPtr s + 152 ∧ u.regValue .r12 = stackPtr s + 216 ∧
    u.regValue .r15 = 0 ∧ memLoad u.external (stackPtr s + 72) 64 = s.regValue .rbx ∧
    memLoad u.external (stackPtr s + 64) 64 = s.regValue .rbx + 32 at stores
  rw [input.rsp, input.drbgPointer] at stores
  refine ⟨fuel + 1, t, run.trans runT, finalFrame, rip,
    (last.read (n := 64) (r := 6) (by simp)).trans stores.1,
    (last.read (n := 64) (r := 14) (by simp)).trans stores.2.1,
    (last.read (n := 64) (r := 15) (by simp)).trans stores.2.2.2.1, ?_, ?_, ?_, ?_,
    (allAgrees.read (n := 64) (r := 5) (by simp)).trans input.descriptors,
    (allAgrees.read (n := 64) (r := 13) (by simp)).trans input.inputCount⟩
  · exact (drbg_after pre input.drbg agrees writes).copy (fun _ _ => by rw [memory])
  · apply input.hmac.copy
    intro i hi
    rw [memory]
    apply agrees.byte
    intro c hc cover
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact cover.elim
    all_goals obtain ⟨j, hj, eq⟩ := cover
    all_goals bv_omega
  · rw [memory]
    exact stores.2.2.2.2.1
  · rw [memory]
    exact stores.2.2.2.2.2

end P256.Proofs.Nonce.Update.Absorb.Prefix
