import P256.Proofs.PublicPoint.Normalize.Finish.CopyPayload
import P256.Proofs.PublicPoint.Normalize.Finish.Prepared
import P256.Proofs.Common.Memory.Readable

set_option autoImplicit false

namespace P256.Proofs.PublicPoint.Normalize.Finish

open P256.Spec.Operations Standards.SECG.ECC
open Prelude X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame Field

theorem copy_coordinates [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {point : Projective} (pre : CalleePre s boundary 0x10e6f0 32 65 3352)
    (state : Coordinates s t boundary point) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 65 3352 1944 ∧
      u.RIP = 0x10ea81 ∧
      MontgomeryAt u (frameBase s + 1032) (point.x * Curve.inverse domain.p point.z % domain.p) ∧
      MontgomeryAt u (frameBase s + 1064) (point.y * Curve.inverse domain.p point.z % domain.p) ∧
      u.external[frameBase s + 1096]? = some 0 ∧
      AgreesExcept [.reg 0, .reg 1, .mem (frameBase s + 1064) 33, .rip] t u := by
  obtain ⟨fuel,u,run,frame,effect⟩ := copy_y_correct pre state.toFrameState state.rip
  have g := copy_y_agrees effect
  change AgreesExcept [.reg 0, .reg 1, .mem (stackPtr t + 1064) 33, .rip] t u at g
  rw [state.rsp] at g
  have rsp : stackPtr t = frameBase s := state.rsp
  have rspU : stackPtr u = frameBase s := frame.rsp
  have hx : MontgomeryAt t (frameBase s + 1032)
      (point.x * Curve.inverse domain.p point.z % domain.p) := by
    simpa only [frameBase,BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd] using state.x
  have hy : MontgomeryAt t (stackPtr t + 32)
      (point.y * Curve.inverse domain.p point.z % domain.p) := by
    rw [rsp]
    simpa only [frameBase,BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd] using state.y
  have my := copy_y_payload effect hy (by
    rw [rsp, ← rspU]
    exact stack_readable (frameOffset := 1944) pre frame (by decide) (by decide))
  have tag := copy_y_tag effect (by
    rw [rsp, ← rspU]
    exact stack_readable (frameOffset := 1944) pre frame (by decide) (by decide))
  rw [rsp] at my tag
  refine ⟨fuel,u,run,frame,effect.rip,?_,my,tag,g⟩
  apply hx.of_bytes_eq
  intro i hi
  apply g.byte
  intro c hc ha
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl <;> try exact ha.elim
  obtain ⟨j,hj,he⟩ := ha
  exact RangeApart.offsets (frameBase s) (a := 1064) (b := 1032)
    (by decide) (by decide) (.inr (by decide)) j hj i hi he.symm

end P256.Proofs.PublicPoint.Normalize.Finish
