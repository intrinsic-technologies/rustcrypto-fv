import P256.Proofs.Verifying.Combination.Loop.MultiNegative.Index
import P256.Proofs.Verifying.Combination.Loop.MultiNegative.Scale
import P256.Proofs.Verifying.Combination.Loop.MultiNegative.Copy
import P256.Proofs.Verifying.Combination.Loop.MultiNegative.YInput
import P256.Proofs.Verifying.Combination.Loop.MultiNegative.CallSetup
import P256.Proofs.Verifying.Combination.PointNegate
import P256.Proofs.Verifying.Combination.PointNegativeFinish

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Loop.Multi

open P256.Spec P256.Spec.Program P256.Proofs.Projective P256.Proofs.Program
open P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

set_option maxRecDepth 4096 in
theorem negative_correct : NegativeCorrect := by
  intro _ s t boundary tables digits p q point u v k left digit pre state rip rdi rax hd neg
  let i : Fin 8 := ⟨digit.natAbs/2, digit_index_lt hd⟩
  let selected := Table.oddTable (if left then p else q) i
  obtain ⟨a, runA, stateA, ripA, indexA⟩ :=
    select_negative_index left pre state rip digit hd neg rdi rax
  obtain ⟨b, runB, stateB, ripB, strideB⟩ := select_negative_scale left pre stateA ripA i indexA
  obtain ⟨nc,c,runC,stateC,ripC,strideC,valueC⟩ := Negative.copy_selected pre stateB i ripB strideB
  obtain ⟨nd,d,runD,stateD,ripD,yD,bytesD⟩ := Negative.copy_y pre stateC i ripC strideC
  have valueD : ProjectiveAt d (stackPtr s-240) selected := valueC.of_bytes_eq bytesD
  obtain ⟨ne,e,runE,stateE,ripE,dstE,srcE,r14E,extE⟩ := Negative.setup_negate pre stateD ripD
  have valueE : ProjectiveAt e (stackPtr s-240) selected :=
    valueD.of_bytes_eq (fun _ _ => congrArg (fun m : Ram => m[_]?) extE)
  have yE : MontgomeryAt e (stackPtr s-368) selected.y :=
    yD.of_bytes_eq (fun _ _ => congrArg (fun m : Ram => m[_]?) extE)
  obtain ⟨nf,f,runF,frameF,ripF,yF,regsF,bytesF⟩ := negate_y pre.toCalleePre stateE.toFrameState
    ripE dstE srcE yE
  have dataF := Negative.data_of_frame pre stateE frameF
    (by
      intro r hr
      apply regsF r
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl|rfl|rfl|rfl|rfl <;> simp)
    (by
      intro off len h j hj
      rcases h with ⟨rfl,rfl⟩ | ⟨h,rfl⟩
      · exact bytesF 336 96 (by decide) (by decide) (by decide) j hj
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl|rfl|rfl|rfl <;>
          exact bytesF _ 8 (by decide) (by decide) (by decide) j hj)
  have valueF : ProjectiveAt f (stackPtr s-240) selected :=
    valueE.of_bytes_eq (bytesF 240 96 (by decide) (by decide) (by decide))
  obtain ⟨ng,w,runG,stateG⟩ := negative_finish pre dataF ripF
    ((regsF .r14 (by simp)).trans r14E) valueF yF
  have lookup : Algebra.signedLookup (Table.oddTable (if left then p else q)) digit = selected.negate := by
    rw [signedLookup_nonzero _ hd (by omega), ite_eq_left neg]
  refine ⟨7+2+nc+nd+ne+nf+ng,w,
    (((((runA.trans runB).trans runC).trans runD).trans runE).trans runF).trans runG, ?_⟩
  rw [lookup]
  exact stateG

end P256.Proofs.Verifying.Combination.Loop.Multi
