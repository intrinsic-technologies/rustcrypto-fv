import P256.Proofs.Signing.Core.Iteration.Components.Finish

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Components

open X86 X86.Machine X86.UserProcess X86Proofs Prelude

theorem correct_of_callees (add : AddContract) (constructor : ConstructorContract) :
    ComponentsContract := by
  intro inst s t boundary state secret nonce x y digest pre original input rip
  obtain ⟨na,a,runA,ripA,stateA⟩ := reduce_x pre input rip
  obtain ⟨nb,b,runB,ripB,stateB⟩ := first_product pre original stateA ripA
  obtain ⟨nc,c,runC,ripC,stateC⟩ := second_product add pre stateB ripB
  obtain ⟨nd,d,runD,ripD,stateD⟩ := finish constructor pre original input.positive input.canonical
    input.affine stateC ripC
  exact ⟨na+nb+nc+nd,d,((runA.trans runB).trans runC).trans runD,ripD,stateD⟩

end P256.Proofs.Signing.Core.Iteration.Components
