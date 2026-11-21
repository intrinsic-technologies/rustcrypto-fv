import P256.Proofs.Ecdh.Normalize.Invert.Setup
import P256.Proofs.Program.FieldCall.Unary
import P256.Proofs.Field.Inverse

set_option autoImplicit false
namespace P256.Proofs.Ecdh.Normalize
open P256.Spec P256.Spec.Program P256.Spec.Operations Standards.SECG.ECC Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame Program.FieldCall

structure Inverted [Bindings] (s t : RamState) (boundary : ReturnBoundary)
    (point : Projective) : Prop extends FrameState s t 32 3464 2056 where
  execution : ∃ fuel, Advances boundary fuel s t
  rip : t.RIP = 0x100355
  output : t.regValue .rbx = s.regValue .rdi
  projective : ProjectiveAt t (stackPtr s - 1904) point
  inverse : Field.MontgomeryAt t (stackPtr s - 1976) (Curve.inverse domain.p point.z)
  choice : t.external[stackPtr s - 1944]? = some (if point.z = 0 then 0 else 1)
  r15 : t.regValue .r15 = stackPtr s - 1976

def inverseLayout : StackCallLayout 3464 32 40 880 :=
  ⟨2064, 1840, 1976, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem invert [Bindings] {s t : RamState} {boundary : ReturnBoundary} {point : Projective}
    (pre : CalleePre s boundary 0x100000 32 32 3464)
    (state : Multiplied s t point) (execution : ∃ fuel, Advances boundary fuel s t) :
    ∃ u, Inverted s u boundary point := by
  obtain ⟨n,v,run,frame,effect,memory⟩ := inverse_setup pre state.toFrameState state.rip
  have args := effect.writes
  simp only [inverseSetupEffect, Write.AllHold] at args
  have src : v.regValue .rsi = stackPtr s - 1840 := by
    exact args.1.trans (scalar_stack_address state.rsp (by decide) (by decide))
  have dst : v.regValue .rdi = stackPtr s - 1976 := by
    exact args.2.2.trans (scalar_stack_address state.rsp (by decide) (by decide))
  have original : ProjectiveAt t (stackPtr s - 1904) point := by
    simpa only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg,
      BitVec.reduceAdd] using state.value
  have hx : Field.MontgomeryAt v (stackPtr s - 1840) point.z := by
    have hz := original.2.2
    rw [show stackPtr s - 1904 + 64 = stackPtr s - 1840 by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl] at hz
    exact hz.of_bytes_eq (by intro i hi; rw [memory])
  obtain ⟨m,u,called,finished,rip,value,saved,bytes,_⟩ := unary_call
    (resultAt := fun u address => Field.MontgomeryAt u address (Curve.inverse domain.p point.z) ∧
      u.external[address + 32]? = some (if point.z = 0 then 0 else 1))
    pre frame inverseLayout rfl (by decide) 0x350 0x13d3b (by decide)
    (by decide +kernel) (by decide) (by decide)
    (inProgram_of_textOffset 0x14090 (by decide))
    (fun v cp hv => Field.Inverse.inverse_correct cp hv)
    effect.rip src dst hx
  refine ⟨u,finished,?_,rip,?_,?_,value.1,?_,?_⟩
  · obtain ⟨fuel,previous⟩ := execution
    exact ⟨fuel+n+m,(previous.trans run).trans called⟩
  · exact (saved .rbx (by simp)).trans
      ((effect.agrees.read (n := 64) (r := 3) (by simp [inverseSetupEffect, Effect.components])).trans state.output)
  · apply original.of_bytes_eq
    intro i hi
    exact (bytes 1904 96 (by decide) (by decide) (Or.inl (by decide)) i hi).trans
      (by rw [memory]; rfl)
  · have hflag : u.external[stackPtr s - 1976 + 32]? = some (if point.z = 0 then 0 else 1) := value.2
    rw [show stackPtr s - 1976 + 32 = stackPtr s - 1944 by
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl] at hflag
    exact hflag
  · exact (saved .r15 (by simp)).trans
      (args.2.1.trans (scalar_stack_address state.rsp (by decide) (by decide)))

end P256.Proofs.Ecdh.Normalize
