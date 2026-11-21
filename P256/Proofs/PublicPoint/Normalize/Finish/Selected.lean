import P256.Proofs.PublicPoint.Normalize.Finish.Prepared
import P256.Proofs.PublicPoint.Normalize.Finish.TagStore

set_option autoImplicit false

namespace P256.Proofs.PublicPoint.Normalize.Finish

open P256.Spec.Operations Standards.SECG.ECC
open Prelude X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

structure Selected [Bindings] (s t : RamState) (boundary : ReturnBoundary)
    (point : Projective) : Prop extends FrameState s t 65 3352 1944 where
  execution : ∃ fuel, Advances boundary fuel s t
  rip : t.RIP = 0x10eae1
  output : t.regValue .rbx = s.regValue .rdi
  x : Field.MontgomeryAt t (s.regValue .rdi)
    (if point.z = 0 then 0 else point.x * Curve.inverse domain.p point.z % domain.p)
  y : Field.MontgomeryAt t (s.regValue .rdi + 32)
    (if point.z = 0 then 0 else point.y * Curve.inverse domain.p point.z % domain.p)
  tag : t.external[frameBase s + 328]? = some 0
  choice : (t.regValue .rbp).setWidth 8 = if point.z = 0 then 0 else 1

theorem finish_selected [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {point : Projective} (pre : CalleePre s boundary 0x10e6f0 32 65 3352)
    (state : Selected s t boundary point) :
    ∃ u, CalleeResult s u boundary 65 3352 ∧ Sec1.AffineAt u (s.regValue .rdi) point.toAffine := by
  have choice : (t.regValue .rbp).setWidth 8 = if decide (point.z ≠ 0) then 1 else 0 := by
    rw [state.choice]
    by_cases hz : point.z=0 <;> simp [hz]
  have tag : t.external[stackPtr s-1616]? = some 0 := by
    simpa only [frameBase,BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd] using state.tag
  obtain ⟨v,runV,frameV,ripV,xV,yV,tagV⟩ := tag_output pre state.toFrameState state.rip
    state.output tag choice state.x state.y
  obtain ⟨u,result,memory⟩ := return_correct pre frameV ripV (by
    obtain ⟨fuel,run⟩ := state.execution
    exact ⟨fuel+6,run.trans runV⟩)
  refine ⟨u,result,?_⟩
  have hx := xV.of_bytes_eq (t := u) (fun _ _ => congrArg (fun m => m[_]?) memory)
  have hy := yV.of_bytes_eq (t := u) (fun _ _ => congrArg (fun m => m[_]?) memory)
  have ht : u.external[s.regValue .rdi+64]? = some (if decide (point.z ≠ 0) then 0 else 1) := by
    rw [memory]; exact tagV
  by_cases hz : point.z=0
  · simp only [Projective.toAffine,hz,ite_true,Sec1.AffineAt] at hx hy ⊢
    exact ⟨hx,hy,by simpa [hz] using ht⟩
  · simp only [Projective.toAffine,hz,ite_false,Sec1.AffineAt] at hx hy ⊢
    exact ⟨hx,hy,by simpa [hz] using ht⟩

end P256.Proofs.PublicPoint.Normalize.Finish
