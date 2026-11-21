import P256.Proofs.Signing.Core.Iteration.Point.Normalize.Inverse
import P256.Proofs.Signing.Core.Iteration.Point.Normalize.SelectFacts
import P256.Proofs.Signing.Core.Iteration.Point.Normalize.Memory
import P256.Proofs.Signing.Core.Iteration.Point.Normalize.Sites

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Point.Normalize

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open Standards.SECG.ECC P256.Spec.Operations
open NextNonce (scalarFrame coreFrame base_add)

structure Selected [Bindings] (s t : RamState) (point : Projective) : Prop where
  frame : Frame s t
  projective : ProjectiveAt t (frameBase s+176) point
  inverse : Field.MontgomeryAt t (frameBase s+2128) (Curve.inverse domain.p point.z)
  flag : (t.regValue .r12).setWidth 8 = if point.z = 0 then 0 else 1
  rbp : t.regValue .rbp = frameBase s+2128
  r13 : t.regValue .r13 = frameBase s+432
  r15 : t.regValue .r15 = frameBase s+1328
  rbx : t.regValue .rbx = frameBase s+240

theorem select_inverse [Bindings] {s t : RamState} {boundary : ReturnBoundary} {point : Projective}
    (pre : SignPre s boundary) (state : Inverted s t point) (rip : t.RIP = 0x10cf82) :
    ∃ fuel u, Advances boundary fuel t u ∧ u.RIP = 0x10cfd8 ∧
      Selected s u point ∧ Preserved s t u := by
  obtain ⟨n,v,run,ready,_,ef⟩ := SelectSetup.correct boundary pre.outerBoundary t
    (readyToStep state.frame.machine state.frame.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.frame.loaded) 0xcf82 SelectSetup.bytes
      (by decide) (by decide +kernel)) (SelectSetup.prepared pre state.frame rip)
  have frame := SelectSetup.after pre state.frame ready ef
  have zero := SelectSetup.zero pre state.frame frame ef
  have values := ef.writes
  simp only [SelectSetup.effect,Write.AllHold] at values
  have original : ProjectiveAt v (frameBase s+176) point := by
    apply state.projective.of_bytes_eq
    intro i hi
    simpa only [BitVec.ofNat_add,BitVec.add_assoc,BitVec.ofNat_eq_ofNat] using
      SelectSetup.byte state.frame ef (offset := 176+i) (by omega) (.inl (by omega))
  have inverse : Field.MontgomeryAt v (frameBase s+432) (Curve.inverse domain.p point.z) := by
    apply state.inverse.of_bytes_eq
    intro i hi
    simpa only [BitVec.ofNat_add,BitVec.add_assoc,BitVec.ofNat_eq_ofNat] using
      SelectSetup.byte state.frame ef (offset := 432+i) (by omega) (.inr (by omega))
  have flags := SelectSetup.choice ef (show t.external[stackPtr t+464]? =
      some (if point.z = 0 then 0 else 1) by rw [state.frame.rsp]; exact state.flag)
  have choice : (v.regValue .rcx).setWidth 8 = if decide (point.z ≠ 0) then 1 else 0 := by
    by_cases hz : point.z = 0 <;> simpa [hz] using flags.2
  have savedFlag : (v.regValue .r12).setWidth 8 = if point.z = 0 then 0 else 1 := by
    by_cases hz : point.z = 0 <;> simpa [hz] using flags.1
  have si : v.regValue .rsi = frameBase s+368 :=
    values.2.2.2.2.2.2.2.1.trans (congrArg (·+368) state.frame.rsp)
  have di : v.regValue .rdi = frameBase s+2128 :=
    values.2.2.2.2.2.2.1.trans (congrArg (·+2128) state.frame.rsp)
  have dx : v.regValue .rdx = frameBase s+432 := values.2.2.2.2.2.2.2.2.1.trans state.r13
  obtain ⟨m,u,called,finished,ripU,value,saved,bytes,_⟩ := PublicPoint.Normalize.select_binary_call
    (op := fun x y => if decide (point.z ≠ 0) then y else x)
    pre.toCalleePre (scalarFrame frame) inverseSelectSite
    (fun w hp hc hx hy => Projective.Multiply.Machine.Lookup.Select.field_select_low8_correct hp hx hy
      ((congrArg (BitVec.setWidth 8) hc).trans choice)) ef.rip
    (si.trans (base_add s (by decide))) (dx.trans (base_add s (by decide)))
    (di.trans (base_add s (by decide)))
    (by
      change Field.MontgomeryAt v (stackPtr s-1912) 0
      rw [← (show frameBase s+368 = stackPtr s-1912 from base_add s (by decide))]
      exact zero)
    (by
      change Field.MontgomeryAt v (stackPtr s-1848) (Curve.inverse domain.p point.z)
      rw [← (show frameBase s+432 = stackPtr s-1848 from base_add s (by decide))]
      exact inverse)
  have kept := bytes_from_stack (s := s) (output := 2128) (lenOut := 32) (by decide) bytes
  have invValue : Field.MontgomeryAt u (frameBase s+2128) (Curve.inverse domain.p point.z) := by
    have address : frameBase s+2128 = stackPtr s-152 := base_add s (by decide)
    have same : (if decide (point.z ≠ 0) then Curve.inverse domain.p point.z else 0) =
        Curve.inverse domain.p point.z := by
      by_cases hz : point.z = 0
      · simp [hz,Projective.Algebra.inverse_zero]
      · simp [hz]
    rw [address,← same]
    exact value
  refine ⟨n+m,u,run.trans called,ripU,⟨coreFrame finished,?_,invValue,?_,?_,?_,?_,?_⟩,?_⟩
  · apply original.of_bytes_eq
    exact kept 176 96 (by decide) (.inl (by decide))
  · exact (congrArg (BitVec.setWidth 8) (saved .r12 (by simp))).trans savedFlag
  · exact (saved .rbp (by simp)).trans (values.2.2.2.2.2.1.trans
      (congrArg (·+2128) state.frame.rsp))
  · exact (saved .r13 (by simp)).trans ((ef.agrees.read (n := 64) (r := 13)
      (by simp [SelectSetup.effect,Effect.components])).trans state.r13)
  · exact (saved .r15 (by simp)).trans ((ef.agrees.read (n := 64) (r := 15)
      (by simp [SelectSetup.effect,Effect.components])).trans state.r15)
  · exact (saved .rbx (by simp)).trans ((ef.agrees.read (n := 64) (r := 3)
      (by simp [SelectSetup.effect,Effect.components])).trans state.rbx)
  · intro i hi
    have h := kept i 1 (by rcases hi with h|h|h|h <;> omega)
      (by rcases hi with h|h|h|h <;> omega) 0 (by decide)
    simp only [BitVec.add_zero] at h
    exact h.trans (SelectSetup.byte state.frame ef (by rcases hi with h|h|h|h <;> omega)
      (by rcases hi with h|h|h|h <;> omega))

end P256.Proofs.Signing.Core.Iteration.Point.Normalize
