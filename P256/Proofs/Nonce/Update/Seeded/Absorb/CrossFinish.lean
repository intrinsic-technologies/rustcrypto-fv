import P256.Proofs.Nonce.Update.Seeded.Absorb.RemainderCopy
import P256.Proofs.Nonce.Update.Seeded.Absorb.ShortTail

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Seeded.Absorb

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem finish_cross [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {original state : State} {secret reduced input : ByteArray}
    (pre : UpdateSeededPre initial boundary original secret reduced)
    (done : CrossDone initial s state input) :
    ∃ fuel t, Advances boundary fuel s t ∧ Loop initial t state input 1 := by
  obtain ⟨fuel,t,run,ready,_,effect⟩ := CrossTail.run boundary pre.outerBoundary s
    (readyToStep done.machine done.bindingsSupported) (CrossTail.code done.loaded)
    ⟨done.rip,ScalarFrame.stack_readable pre.toDrbgCalleePre.callee done.toFrameState (by decide) (by decide)⟩
  have agrees : AgreesExcept [.reg 5,.flags,.rip] s t := effect.agrees
  have ctx := done.toContext.after_nomem pre.toDrbgCalleePre ready agrees (by simp) (by simp)
    (by simp [Component.Covers])
  have current : t.regValue .rbp = initial.regValue .rsi + 16 := by
    have h : t.regValue .rbp = s.regValue .rbp + 16 := effect.writes
    rwa [done.current] at h
  have atEnd : ShortTail.atEnd s = false := by
    change ((s.regValue .rbp + 16) == memLoad s.external (stackPtr s + 80) 64) = _
    rw [done.current,show stackPtr s = scratch initial from done.rsp,done.savedEnd,pre.inputCount]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq,Bool.false_eq_true,iff_false]
    bv_omega
  have rip : t.RIP = 0x10a78d := by
    rw [effect.rip]
    simp only [CrossTail.effect,ShortTail.target,atEnd,Bool.false_eq_true,↓reduceIte]
  exact ⟨fuel,t,run,ctx,rip,current,
    (agrees.read (n:=64) (r:=14) (by simp)).trans done.hashPointer,
    (agrees.read (n:=64) (r:=13) (by simp)).trans done.copyPointer,
    done.hmac.copy (fun _ _ => by rw [agrees.external (by simp [Component.Covers])])⟩

end P256.Proofs.Nonce.Update.Seeded.Absorb
