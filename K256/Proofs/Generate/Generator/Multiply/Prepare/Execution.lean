import K256.Proofs.Generate.Generator.Multiply.Prepare.Bases
import K256.Proofs.Generate.Generator.Multiply.Prepare.Tables
import K256.Proofs.Generate.Generator.Multiply.Prepare.Digits
import K256.Proofs.Generate.Generator.Multiply.Prepare.Accumulator
import K256.Proofs.Generate.Generator.Multiply.Split.Execution

namespace K256.Proofs.Generate.Generator.Multiply

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
  Standards.SECG.DomainParameters.Secp256k1

theorem prepare (recode : type_of% @Radix.execute) (select : type_of% @lookup)
    (add : type_of% @addCall) {fr : Activation} {initial a : Registers} {m : Ram} {d : Nat}
    (entry : CoreEntry fr initial d) (pos : 0 < d) (bound : d < domain.n)
    (split : SplitState fr a m d) :
    ∃ b n, Reaches .l11c9e7 a m .l11d748 b n ∧ Prepared fr b n d := by
  obtain ⟨b, n, bases, h₁⟩ := Prepare.prepareBases entry pos bound split
  obtain ⟨c, o, tables, h₂⟩ := Prepare.prepareTables add entry pos bound h₁
  obtain ⟨e, p, digits, h₃⟩ := Prepare.prepareDigits recode entry pos bound h₂
  obtain ⟨f, q, acc, ready⟩ := Prepare.prepareAccumulator select add entry pos bound h₃
  exact ⟨f, q, ((bases.trans tables).trans digits).trans acc, ready⟩

end K256.Proofs.Generate.Generator.Multiply
