import K256.Proofs.Verify.Core.Scalars.Products.Transfer

namespace K256.Proofs.Signing.Scalar

open X86.Machine X86.UserProcess X86Proofs CFG Lift Verify.LIR

theorem multiply_of_product {code : CodeMap} {a : Values Value Reg.count} {m : Ram}
    {out : Output Value Ram Reg.count}
    (run : program.Exec (dialect code) ⟨⟨.l109f60,a,m⟩,[]⟩ out) :
    program.Exec (dialect code) ⟨⟨.l109f70,a,m⟩,[]⟩ out := by
  have eq : program.step (dialect code) ⟨⟨.l109f70,a,m⟩,[]⟩ =
      program.step (dialect code) ⟨⟨.l109f60,a,m⟩,[]⟩ := by rfl
  cases run with
  | done step => exact .done (eq.trans step)
  | next step tail => exact .next (eq.trans step) tail

end K256.Proofs.Signing.Scalar
