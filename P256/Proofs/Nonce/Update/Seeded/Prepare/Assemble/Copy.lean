import P256.Proofs.Nonce.Update.Seeded.Prepare.Assemble.State
import P256.Proofs.Nonce.Update.Seeded.Prepare.Assemble.CopySetup
import P256.Proofs.Nonce.Update.Zero.CopyCall

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Seeded.Prepare.Assemble

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

private def copyLayout : StackCallLayout 1856 168 168 0 :=
  ⟨688, 248, 424, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩

theorem copy_hmac [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {original state : State} (pre : DrbgCalleePre initial boundary 0x109f30 1856 original)
    (current : CopyReady initial s state) :
    ∃ fuel t, Advances boundary fuel s t ∧ Prepared initial t state := by
  obtain ⟨n, u, setupRun, ready, _, effect⟩ := CopySetup.run boundary pre.outerBoundary s
    (readyToStep current.machine current.bindingsSupported) (CopySetup.code current.loaded) current.rip
  have agrees : AgreesExcept [.reg 7, .reg 6, .reg 2, .rip] s u := effect.agrees
  have context : Context initial u state := current.toContext.after_agrees pre ready agrees
    (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> simp)
    (by intro c hc a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at hc; rcases hc with rfl | rfl | rfl | rfl <;> exact ha.elim)
    (by intro i hi; rw [agrees.external (by simp [Component.Covers])])
  have memory := agrees.external (by simp [Component.Covers])
  have hmac : HMAC.HmacStateAt u (scratch initial + 432) state.key ByteArray.empty :=
    current.hmac.copy (by intro i hi; rw [memory])
  have rsp : rspOf s = scratch initial := current.rsp
  have sourceAddr : scratch initial + 432#64 = stackPtr initial - 248#64 := by
    simp only [scratch, BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have targetAddr : scratch initial + 256#64 = stackPtr initial - 424#64 := by
    simp only [scratch, BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have source : u.regValue .rsi = stackPtr initial - 248#64 := by
    have h : u.regValue .rsi = rspOf s + 432 := effect.writes.2.1
    simpa only [rsp, BitVec.ofNat_eq_ofNat, sourceAddr] using h
  have destination : u.regValue .rdi = stackPtr initial - 424#64 := by
    have h : u.regValue .rdi = rspOf s + 256 := effect.writes.1
    simpa only [rsp, BitVec.ofNat_eq_ofNat, targetAddr] using h
  obtain ⟨t, result⟩ := Zero.memcpy_call pre context.toFrameState copyLayout rfl
    (by decide) (by decide) 0xa621 0xf9ed1 (by decide)
    (by decide +kernel) (by decide +kernel) effect.rip source destination effect.writes.2.2
  have drbg : DrbgAt t (initial.regValue .rdi) state := by
    apply context.drbg.copy
    intro i hi
    apply result.writes
    intro region member inside
    have eq : region = ScalarFrame.workRegion initial 1856 := by simpa using member
    subst region
    exact pre.separation _
      (memoryRegion_contains_add pre.stateBounded (Nat.le_refl _) (Nat.le_refl _) hi)
      ((Update.Prepare.work_substack pre) inside)
  have finalContext := context.of_copied result.toFrameState drbg
    ((result.calleeSaved .rbx (by simp)).trans context.drbgPointer)
    ((result.calleeSaved .rbp (by simp)).trans context.descriptors) (by
      have address : scratch initial + 64#64 = stackPtr initial - 616#64 := by
        simp only [scratch, BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
      intro i hi
      simp only [BitVec.ofNat_eq_ofNat, address]
      exact result.preserved 616 24 (by decide) (by decide) (.inl (by decide)) i hi)
  obtain ⟨fuel, run⟩ := result.execution
  refine ⟨n+fuel, t, setupRun.trans run, result.toFrameState, result.rip, drbg, ?_,
    (result.calleeSaved .r12 (by simp)).trans
      ((agrees.read (n := 64) (r := 12) (by simp)).trans current.bufferPointer),
    finalContext.savedPointer, finalContext.savedValue, finalContext.descriptors, finalContext.savedEnd⟩
  apply hmac.copy
  simpa only [BitVec.ofNat_eq_ofNat, sourceAddr, targetAddr, copyLayout] using result.copied

end P256.Proofs.Nonce.Update.Seeded.Prepare.Assemble
