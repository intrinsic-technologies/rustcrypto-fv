import P256.Proofs.Verifying.Core.Reduce.Body
import P256.Proofs.Verifying.Core.Reduce.Selected
import P256.Proofs.Verifying.Core.Reduce.Output
import P256.Proofs.Verifying.Core.Reduce.Epilogue

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Reduce

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program SecretKeyFromBytes.Scalar

theorem reduce_correct : Correct := by
  intro bindings s boundary a pre input
  obtain ⟨n0,t0,h0,state0⟩ := subtract_body pre
  obtain ⟨n1,t1,h1,state1,rip1,ptr1,val1⟩ := select_body pre state0
  obtain ⟨n2,t2,h2,state2,rip2,val2⟩ := store_output pre state1 rip1 ptr1 val1
  obtain ⟨t,result,memory⟩ := epilogue pre state2 rip2 ⟨n0+(n1+n2),h0.trans (h1.trans h2)⟩
  refine ⟨t,result,?_⟩
  have value := reduceOrder_toNat (Field.readLimbs s (s.regValue .rsi))
  rw [Field.readLimbs_toNat input] at value
  rw [value] at val2
  exact ⟨val2.1,fun i hi => by rw [memory]; exact val2.2 i hi⟩

end P256.Proofs.Verifying.Core.Reduce
