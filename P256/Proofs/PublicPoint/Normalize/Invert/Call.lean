import P256.Proofs.PublicPoint.Normalize.Invert.Setup
import P256.Proofs.Program.FieldCall.Unary
import P256.Proofs.Field.Inverse

set_option autoImplicit false
namespace P256.Proofs.PublicPoint.Normalize
open P256.Spec P256.Spec.Program P256.Spec.Operations Standards.SECG.ECC Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame Program.FieldCall

structure Inverted [Bindings] (s t : RamState) (boundary : ReturnBoundary)
    (point : Projective) : Prop extends FrameState s t 65 3352 1944 where
  execution : ∃ fuel, Advances boundary fuel s t
  rip : t.RIP = 0x10e96b
  output : t.regValue .rbx = s.regValue .rdi
  projective : ProjectiveAt t (stackPtr s - 1880) point
  inverse : Field.MontgomeryAt t (stackPtr s - 1784) (Curve.inverse domain.p point.z)
  choice : t.external[stackPtr s - 1752]? = some (if point.z = 0 then 0 else 1)
  r15 : t.regValue .r15 = stackPtr s - 1784

def inverseLayout : StackCallLayout 3352 32 40 880 :=
  ⟨1952, 1816, 1784, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem invert [Bindings] {s t : RamState} {boundary : ReturnBoundary} {d : Nat}
    (pre : CalleePre s boundary 0x10e6f0 32 65 3352)
    (state : Multiplied s t boundary d) :
    ∃ u, Inverted s u boundary (Projective.Multiply.model
      Projective.Multiply.Machine.Basepoint.basePoint d) := by
  let point := Projective.Multiply.model Projective.Multiply.Machine.Basepoint.basePoint d
  obtain ⟨n,v,run,frame,effect,memory⟩ := inverse_setup pre state.toFrameState state.rip
  have args := effect.writes
  simp only [inverseSetupEffect, Write.AllHold] at args
  have src : v.regValue .rsi = stackPtr s - 1816 := by
    exact args.1.trans (scalar_stack_address state.rsp (by decide) (by decide))
  have dst : v.regValue .rdi = stackPtr s - 1784 := by
    exact args.2.2.trans (scalar_stack_address state.rsp (by decide) (by decide))
  have hx : Field.MontgomeryAt v (stackPtr s - 1816) point.z := by
    have hz := state.value.2.2
    rw [show stackPtr s - 1880 + 64 = stackPtr s - 1816 by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl] at hz
    exact hz.of_bytes_eq (by intro i hi; rw [memory])
  obtain ⟨m,u,called,finished,rip,value,saved,bytes,_⟩ := unary_call
    (resultAt := fun u address => Field.MontgomeryAt u address (Curve.inverse domain.p point.z) ∧
      u.external[address + 32]? = some (if point.z = 0 then 0 else 1))
    pre frame inverseLayout rfl (by decide) 0xe966 0x5725 (by decide)
    (by decide +kernel) (by decide) (by decide)
    (inProgram_of_textOffset 0x14090 (by decide))
    (fun v cp hv => Field.Inverse.inverse_correct cp hv)
    effect.rip src dst hx
  refine ⟨u,finished,?_,rip,?_,?_,value.1,?_,?_⟩
  · obtain ⟨fuel,previous⟩ := state.execution
    exact ⟨fuel+n+m,(previous.trans run).trans called⟩
  · exact (saved .rbx (by simp)).trans
      ((effect.agrees.read (n := 64) (r := 3) (by simp [inverseSetupEffect, Effect.components])).trans state.output)
  · apply state.value.of_bytes_eq
    intro i hi
    exact (bytes 1880 96 (by decide) (by decide) (Or.inr (by decide)) i hi).trans
      (by rw [memory]; rfl)
  · have hflag : u.external[stackPtr s - 1784 + 32]? = some (if point.z = 0 then 0 else 1) := value.2
    rw [show stackPtr s - 1784 + 32 = stackPtr s - 1752 by
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl] at hflag
    exact hflag
  · exact (saved .r15 (by simp)).trans
      (args.2.1.trans (scalar_stack_address state.rsp (by decide) (by decide)))

end P256.Proofs.PublicPoint.Normalize
