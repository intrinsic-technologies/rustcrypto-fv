import P256.Proofs.Signing.Core.Iteration.Point.Normalize.Coordinates.Y
import P256.Proofs.Signing.Core.Iteration.Point.Normalize.Copy.PackedCorrect
import P256.Proofs.Signing.Core.Iteration.Point.Normalize.Finish.Store

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Point.Normalize.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open Standards.SECG.ECC P256.Spec.Operations

structure Registers (s t : RamState) : Prop where
  rbp : t.regValue .rbp = frameBase s+528
  r13 : t.regValue .r13 = frameBase s+432
  r14 : t.regValue .r14 = frameBase s+8
  r15 : t.regValue .r15 = frameBase s+1328
  flag : (t.regValue .r12).setWidth 8 = 1

theorem Registers.preserve {s t u : RamState} {cs : List Component}
    (regs : Registers s t) (agrees : AgreesExcept cs t u)
    (unchanged : ∀ r ∈ [5,12,13,14,15], Component.reg r ∉ cs) : Registers s u := by
  exact ⟨(agrees.read (n := 64) (r := 5) (unchanged _ (by simp))).trans regs.rbp,
    (agrees.read (n := 64) (r := 13) (unchanged _ (by simp))).trans regs.r13,
    (agrees.read (n := 64) (r := 14) (unchanged _ (by simp))).trans regs.r14,
    (agrees.read (n := 64) (r := 15) (unchanged _ (by simp))).trans regs.r15,
    (congrArg (BitVec.setWidth 8) (agrees.read (n := 64) (r := 12) (unchanged _ (by simp)))).trans regs.flag⟩

structure Payload [Bindings] (s t : RamState) (x y : Nat) (offset : Nat) : Prop where
  frame : Frame s t
  registers : Registers s t
  point : Sec1.AffineAt t (frameBase s+BitVec.ofNat 64 offset) (.affine x y)

theorem packed [Bindings] {s t : RamState} {boundary : ReturnBoundary} {point : Projective}
    (pre : SignPre s boundary) (state : Coordinates s t point) (nonzero : point.z ≠ 0)
    (rip : t.RIP = 0x10d05e) :
    ∃ fuel u, Advances boundary fuel t u ∧ u.RIP = 0x10d09d ∧
      Payload s u (point.x*Curve.inverse domain.p point.z % domain.p)
        (point.y*Curve.inverse domain.p point.z % domain.p) 1328 ∧ Preserved s t u := by
  obtain ⟨n,v,run,frame,ip,value,ef⟩ := Copy.Packed.correct pre state.frame rip state.y
  obtain ⟨u,run1,ip1,st⟩ := zero pre frame ip
  have unchanged (offset : Nat) (small : offset < 2^64) (apart : offset < 1360 ∨ 1393 ≤ offset) :
      u.external[frameBase s+BitVec.ofNat 64 offset]? = t.external[frameBase s+BitVec.ofNat 64 offset]? :=
    (st.unchanged (by decide) small (by omega)).trans
      (Copy.Packed.byte state.frame ef small (by omega))
  have regs : Registers s t := ⟨state.rbp,state.r13,state.r14,state.r15,by simpa [nonzero] using state.flag⟩
  have ru := regs.preserve (ef.agrees.trans st.agrees) (by
    intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl <;>
      simp [Copy.Packed.effect,ScalarFrame.Copy32.effect,Effect.components])
  refine ⟨n+1,u,run.trans run1,ip1,⟨st.frame,ru,?_,?_,?_⟩,?_⟩
  · apply state.x.of_bytes_eq
    intro i hi
    simpa only [BitVec.ofNat_add,BitVec.add_assoc,BitVec.ofNat_eq_ofNat] using unchanged (1328+i) (by omega) (.inl (by omega))
  · have h : Field.MontgomeryAt u (frameBase s+1360) (point.y*Curve.inverse domain.p point.z % domain.p) := by
      apply value.of_bytes_eq
      intro i hi
      simpa only [BitVec.ofNat_add,BitVec.add_assoc,BitVec.ofNat_eq_ofNat] using
        st.unchanged (by decide) (i := 1360+i) (by omega) (.inl (by omega))
    simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd] using h
  · change u.external[frameBase s+1328+64]? = some 0
    rw [show frameBase s+1328+64 = frameBase s+1392 by rw [BitVec.add_assoc]; rfl]
    exact st.byte
  · intro i hi
    exact unchanged i (by rcases hi with h|h|h|h <;> omega) (by rcases hi with h|h|h|h <;> omega)

end P256.Proofs.Signing.Core.Iteration.Point.Normalize.Finish
