import P256.Proofs.Nonce.Update.Seeded.Absorb.Prefix.Head
import P256.Proofs.Nonce.Update.Seeded.Absorb.Memory
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Seeded.Absorb.Prefix

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem enter [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {original state : State} (pre : DrbgCalleePre initial boundary 0x109f30 1856 original)
    (input : Prepared initial s state) :
    ∃ fuel t, Advances boundary fuel s t ∧ Entered initial t state := by
  have headPre : Head.Pre s := by
    refine ⟨input.rip, ScalarFrame.stack_readable pre.callee input.toFrameState (by decide) (by decide), ?_⟩
    have position := input.hmac.inner.position
    simp only [ByteArray.size_append, HMAC.keyPad_size, ByteArray.size_empty,
      Nat.add_zero, Nat.reduceMod, BitVec.add_assoc, BitVec.reduceAdd] at position
    change memLoad s.external (stackPtr s + 383) 8 = 0
    rw [input.rsp, memLoad_8]
    change ((s.external[scratch initial + 383]?).getD 0).toBitVec = 0
    simp only [BitVec.ofNat_eq_ofNat]
    rw [position]
    rfl
  obtain ⟨fuel, u, run, ready, _, effect⟩ := Head.run boundary pre.outerBoundary s
    (readyToStep input.machine input.bindingsSupported) (Head.code input.loaded) headPre
  have agrees : AgreesExcept [.reg 13, .reg 15, .flags, .rip] s u := effect.agrees
  have current : Context initial s state := ⟨input.toFrameState, input.drbg,
    input.bufferPointer, input.savedPointer, input.savedValue, input.savedEnd⟩
  have context := current.after_nomem pre ready agrees (by simp) (by simp) (by
    intro c hc a; simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl <;> simp [Component.Covers])
  obtain ⟨v, step, readyV, branch⟩ := jcc_rel8_effect_step 0x10a63c 7 0x56 u ready
    (programText_slice (programLoaded_codeIn context.loaded) 0xa63c _ (by decide) (by decide +kernel))
    ⟨effect.rip, by intro; decide⟩
  have carry : (StatusFlags.ofRFLAGS u.RFLAGS).CF = true := effect.flags.1
  have ripV : v.RIP = 0x10a63e := by
    rw [branch.rip]
    change (if !((StatusFlags.ofRFLAGS u.RFLAGS).CF ||
      (StatusFlags.ofRFLAGS u.RFLAGS).ZF) then 0x10a694 else 0x10a63e) = _
    simp only [carry, Bool.true_or, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  have runV : Advances boundary 1 u v := Advances.of_step step (.inl (by
    rw [ripV]
    exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xa63e (by decide))))
  have branchAgrees : AgreesExcept [.rip] u v := branch.agrees
  have contextV := context.after_nomem pre readyV branchAgrees (by simp) (by simp) (by
    intro c hc a; simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst c; simp [Component.Covers])
  obtain ⟨t, runT, readyT, load⟩ :=
    (mov_r64_m64_effect_step 0x10a63e 0x48 (by simp [RexWPrefix]) 1
      (.sib 4 none 0 (.d8 64)) (by decide) rfl rfl).advances readyV
      (programText_slice (programLoaded_codeIn contextV.loaded) 0xa63e _ (by decide) (by decide +kernel))
      ⟨ripV, ScalarFrame.stack_readable pre.callee contextV.toFrameState (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xa643 (by decide)))
  have loadAgrees : AgreesExcept [.reg 1,.rip] v t := load.agrees
  have finalContext := contextV.after_nomem pre readyT loadAgrees (by simp) (by simp) (by
    intro c hc a; simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> simp [Component.Covers])
  have allAgrees := (agrees.trans branchAgrees).trans loadAgrees
  refine ⟨fuel+1+1, t, (run.trans runV).trans runT, finalContext, load.rip, ?_, ?_,
    (allAgrees.read (n := 64) (r := 5) (by simp)).trans input.descriptors, ?_⟩
  · have value : t.regValue .rcx = memLoad v.external (stackPtr v + 64) 64 := load.writes
    rw [contextV.rsp] at value
    exact value.trans contextV.savedValue
  · exact (loadAgrees.read (n := 64) (r := 15) (by simp)).trans
      ((branchAgrees.read (n := 64) (r := 15) (by simp)).trans effect.writes.2)
  · exact input.hmac.copy (fun _ _ => by rw [allAgrees.external (by simp [Component.Covers])])

end P256.Proofs.Nonce.Update.Seeded.Absorb.Prefix
