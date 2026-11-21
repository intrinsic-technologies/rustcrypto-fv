import P256.Proofs.Verifying.Core.Finish.Prepare
import P256.Proofs.Verifying.Core.Finish.Canonical

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program
open SecretKeyFromBytes.Scalar (Nat256At)

theorem normalize [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {x y r : Nat} {nonzero : Bool} (pre : Core.Pre s boundary)
    (frame : Frame s t) (rip : t.RIP = 0x10df44)
    (hx : Field.MontgomeryAt t (stackPtr s-600) x)
    (hy : Field.MontgomeryAt t (stackPtr s-784) y)
    (r15 : t.regValue .r15 = stackPtr s-600)
    (choice : (t.regValue .rbx).setWidth 8 = if nonzero then 1 else 0)
    (scalar : Nat256At t (stackPtr s-472) r)
    (output : memLoad t.external (frameBase s+384) 64 = s.regValue .rdi) :
    ∃ n u, Advances boundary n t u ∧ Frame s u ∧ u.RIP = 0x10e098 ∧
      ((if nonzero then x else 0) < 2^256 ∧
        (⟨(frameBase s+392).toNat,32⟩ : MemoryRegion).HasBytes u.external
          (Standards.SECG.ECC.Encoding.natToOctets 32 (if nonzero then x else 0))) ∧
      Nat256At u (frameBase s+704) r ∧ memLoad u.external (frameBase s+384) 64 = s.regValue .rdi := by
  have state : Coordinates s t x y r nonzero := by
    refine ⟨frame,rip,output,?_,?_,choice,?_,?_⟩
    · simpa only [frameBase,BitVec.sub_eq_add_neg,BitVec.add_assoc,
        BitVec.reduceNeg,BitVec.reduceAdd] using hx
    · simpa only [frameBase,BitVec.sub_eq_add_neg,BitVec.add_assoc,
        BitVec.reduceNeg,BitVec.reduceAdd] using hy
    · simpa only [frameBase,BitVec.sub_eq_add_neg,BitVec.add_assoc,
        BitVec.reduceNeg,BitVec.reduceAdd] using r15
    · simpa only [frameBase,BitVec.sub_eq_add_neg,BitVec.add_assoc,
        BitVec.reduceNeg,BitVec.reduceAdd] using scalar
  obtain ⟨n,a,runA,stateA⟩ := save_coordinates pre.toCalleePre state
  obtain ⟨m,b,runB,stateB⟩ := prepare pre.toCalleePre stateA
  obtain ⟨k,c,runC,stateC⟩ := select pre.toCalleePre stateB
  obtain ⟨l,u,runU,frameU,ripU,xU,rU,outU⟩ := canonical pre stateC
  exact ⟨n+m+k+l,u,((runA.trans runB).trans runC).trans runU,frameU,ripU,xU,rU,outU⟩

end P256.Proofs.Verifying.Core.Finish
