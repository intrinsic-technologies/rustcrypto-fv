import P256.Proofs.Nonce.Update.Absorb.Seeded.RemainderCopy
import P256.Proofs.Nonce.Update.Absorb.Seeded.CrossTail

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Absorb.Seeded

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem finish_cross [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {state : State} {secret reduced input : ByteArray}
    (pre : UpdateSeededPre initial boundary state secret reduced)
    (done : CrossDone initial s state input) :
    ∃ fuel t, Advances boundary fuel s t ∧ Loop initial t state input 1 := by
  obtain ⟨fuel,u,run,ready,_,effect⟩ := CrossTail.run boundary pre.outerBoundary s
    (readyToStep done.machine done.bindingsSupported) (CrossTail.code done.loaded)
    ⟨done.rip,ScalarFrame.stack_readable pre.callee done.toFrameState (by decide) (by decide)⟩
  have agrees : AgreesExcept [.reg 14,.flags,.rip] s u := effect.agrees
  have ctx := done.toContext.after_nomem pre.toDrbgCalleePre ready agrees (by simp) (by simp)
    (by simp [Component.Covers])
  have current : u.regValue .r14 = initial.regValue .rsi + 16 := by
    have h : u.regValue .r14 = s.regValue .r14 + 16 := effect.writes
    rwa [done.current] at h
  have zero : (StatusFlags.ofRFLAGS u.RFLAGS).ZF = false := by
    have h := effect.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS u.RFLAGS).ZF =
      (((s.regValue .r14 + 16) - memLoad s.external (stackPtr s + 80) 64) == 0) at h
    rw [done.current,show stackPtr s = scratch initial from done.rsp,done.savedEnd,pre.inputCount] at h
    rw [h]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq,Bool.false_eq_true,iff_false]
    bv_omega
  obtain ⟨t,step,readyT,branch⟩ := jcc_rel32_effect_step 0x10a386 5 0xffffff37 u ready
    (programText_slice (programLoaded_codeIn ctx.loaded) 0xa386 _ (by decide) (by decide +kernel))
    ⟨effect.rip,by intro; decide⟩
  have rip : t.RIP = 0x10a2c3 := by
    rw [branch.rip]
    change (if !(StatusFlags.ofRFLAGS u.RFLAGS).ZF then 0x10a2c3 else 0x10a38c) = _
    simp only [zero,Bool.not_false,↓reduceIte]
  have lastRun : Advances boundary 1 u t := Advances.of_step step (.inl (by
    rw [rip]; exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xa2c3 (by decide))))
  have a : AgreesExcept [.rip] u t := branch.agrees
  have ctxT := ctx.after_nomem pre.toDrbgCalleePre readyT a (by simp) (by simp) (by simp [Component.Covers])
  exact ⟨fuel+1,t,run.trans lastRun,ctxT,rip,
    (a.read (n:=64) (r:=14) (by simp)).trans current,
    done.hmac.copy (fun _ _ => by rw [(agrees.trans a).external (by simp [Component.Covers])])⟩

end P256.Proofs.Nonce.Update.Absorb.Seeded
