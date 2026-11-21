import P256.Proofs.Nonce.Update.Absorb.Setup
import P256.Proofs.Nonce.Update.Absorb.Seeded.Context
import P256.Proofs.Nonce.Update.Absorb.Seeded.EnterTail
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Absorb.Seeded

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem enter [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {state : State} {secret reduced : ByteArray} (pre : UpdateSeededPre initial boundary state secret reduced)
    (input : Tagged initial s state) :
    ∃ fuel t, Advances boundary fuel s t ∧ Loop initial t state (state.value ++ ⟨#[0]⟩) 0 := by
  have hp : Setup.Pre s := by
    refine ⟨input.rip, ?_, ?_⟩
    · intro off member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;>
        exact stack_writable8 pre.toDrbgCalleePre input.toFrameState (by decide) (by decide)
    · intro off member pc len bound
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;>
        exact ScalarFrame.stack_code pre.callee input.toFrameState (by decide) (by decide) bound
  obtain ⟨fuel, u, run, ready, _, effect⟩ := Setup.run boundary pre.outerBoundary s
    (readyToStep input.machine input.bindingsSupported) (Setup.code input.loaded) hp
  have agrees : AgreesExcept [.reg 0, .mem (scratch initial + 80) 8,
      .mem (scratch initial + 424) 8, .flags, .rip] s u := by
    have h := effect.agrees
    simp only [Setup.effect, Effect.components, List.map, Write.component, Operand.component] at h
    rwa [show rspOf s = scratch initial from input.rsp] at h
  have writes : ∀ (c : Component), c ∈ [.reg 0, .mem (scratch initial + 80) 8,
      .mem (scratch initial + 424) 8, .flags, .rip] →
      ∀ (a : BitVec 64), c.Covers a → (ScalarFrame.workRegion initial 1856).Contains a.toNat := by
    intro c hc a cover
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact cover.elim
    all_goals exact Prepare.work_contains_scratch pre.toDrbgCalleePre (by decide) cover
  have frame := frame_after pre.toDrbgCalleePre input.toFrameState ready agrees (by simp) writes
  have count : s.regValue .r13 = 3 := input.inputCount.trans pre.inputCount
  obtain ⟨t, step, readyT, branch⟩ := jcc_rel32_effect_step 0x10a27b 4 0x11b u ready
    (programText_slice (programLoaded_codeIn frame.loaded) 0xa27b _ (by decide) (by decide +kernel))
    ⟨effect.rip, by intro; decide⟩
  have flag : (StatusFlags.ofRFLAGS u.RFLAGS).ZF = false := by
    have h := effect.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS u.RFLAGS).ZF = (s.regValue .r13 == 0) at h
    simpa only [count, show ((3 : BitVec 64) == 0) = false from by decide +kernel] using h
  have rip : t.RIP = 0x10a281 := by
    rw [branch.rip]
    change (if (StatusFlags.ofRFLAGS u.RFLAGS).ZF then 0x10a39c else 0x10a281) = _
    simp only [flag, Bool.false_eq_true, ↓reduceIte]
  have lastRun : Advances boundary 1 u t := Advances.of_step step (.inl (by
    rw [rip]
    exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xa281 (by decide))))
  have last : AgreesExcept [.rip] u t := branch.agrees
  have memory := last.external (by simp [Component.Covers])
  have frameT := frame_after pre.toDrbgCalleePre frame readyT last (by simp) (by
    intro c hc a cover
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst c
    exact cover.elim)
  have preserved (offset len : Nat) (bound : offset + len < 2^64)
      (apart : (offset + len ≤ 80 ∨ 88 ≤ offset) ∧ (offset + len ≤ 424 ∨ 432 ≤ offset)) :
      ∀ i < len, u.external[scratch initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
        s.external[scratch initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
    intro i hi
    apply agrees.byte
    intro c hc cover
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact cover.elim
    all_goals obtain ⟨j, hj, eq⟩ := cover
    all_goals bv_omega
  have stores := effect.writes
  change u.regValue .rax = (s.regValue .r13 <<< 4) + s.regValue .rbp ∧
    memLoad u.external (stackPtr s + 80) 64 = (s.regValue .r13 <<< 4) + s.regValue .rbp ∧
    memLoad u.external (stackPtr s + 424) 64 = s.regValue .r13 at stores
  rw [count, input.descriptors, input.rsp] at stores
  have ctx : Context initial t state := by
    refine ⟨frameT, ?_, ?_, ?_, ?_,
      ((agrees.trans last).read (n := 64) (r := 5) (by simp)).trans input.descriptors, ?_⟩
    · exact (drbg_after pre.toDrbgCalleePre input.drbg agrees writes).copy (fun _ _ => by rw [memory])
    · rw [memory]
      calc
        memLoad u.external (scratch initial + 72) 64 = memLoad s.external (scratch initial + 72) 64 := by
          apply memLoad_congr
          intro i hi
          exact congrArg (fun x : Option UInt8 => x.getD 0) (preserved 72 8 (by decide) (by omega) i hi)
        _ = initial.regValue .rdi := input.savedPointer
    · rw [memory]
      calc
        memLoad u.external (scratch initial + 64) 64 = memLoad s.external (scratch initial + 64) 64 := by
          apply memLoad_congr
          intro i hi
          exact congrArg (fun x : Option UInt8 => x.getD 0) (preserved 64 8 (by decide) (by omega) i hi)
        _ = initial.regValue .rdi + 32 := input.savedValue
    · rw [memory, pre.inputCount]
      exact stores.2.2
    · rw [memory, pre.inputCount]
      simpa only [scratch, BitVec.ofNat_eq_ofNat, show ((3#64) <<< 4) = 48#64 from by decide +kernel, BitVec.reduceMul, BitVec.add_comm] using stores.2.1
  have hmac : HMAC.HmacStateAt t (scratch initial + 88) state.key (state.value ++ ⟨#[0]⟩) :=
    input.hmac.copy (fun i hi => by
      rw [memory]
      exact preserved 88 168 (by decide) (by omega) i hi)
  obtain ⟨tailFuel, v, tailRun, readyV, _, tail⟩ := EnterTail.run boundary pre.outerBoundary t
    (readyToStep ctx.machine ctx.bindingsSupported) (EnterTail.code ctx.loaded) rip
  have tailAgrees : AgreesExcept [.reg 14, .rip] t v := tail.agrees
  have ctxV := ctx.after_nomem pre.toDrbgCalleePre readyV tailAgrees (by simp) (by simp)
    (by simp [Component.Covers])
  refine ⟨fuel + 1 + tailFuel, v, (run.trans lastRun).trans tailRun, ctxV, tail.rip, ?_, ?_⟩
  · change v.regValue .r14 = initial.regValue .rsi + 0#64
    rw [BitVec.add_zero]
    exact tail.writes.trans ctx.descriptors
  · exact hmac.copy (fun _ _ => by rw [tailAgrees.external (by simp [Component.Covers])])

end P256.Proofs.Nonce.Update.Absorb.Seeded
