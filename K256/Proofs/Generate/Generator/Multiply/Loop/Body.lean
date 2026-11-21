import K256.Proofs.Generate.Generator.Multiply.Loop.Body.Doubles
import K256.Proofs.Generate.Generator.Multiply.Loop.Body.Tables
import K256.Proofs.Generate.Generator.Multiply.Loop.Body.Additions
import K256.Proofs.Generate.Generator.Multiply.Loop.Body.Exit

namespace K256.Proofs.Generate.Generator.Multiply

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
  Standards.SECG.DomainParameters.Secp256k1

theorem windowRound (doubles : type_of% @fourDoubles) (select : type_of% @lookup)
    (add : type_of% @addCall) {fr : Activation} {initial a : Registers} {m : Ram} {d k : Nat}
    (entry : CoreEntry fr initial d) (bound : k < 32) (s : WindowHead fr a m d (k+1)) :
    ∃ b n, Reaches .l11d7ef a m .l11d7d0 b n ∧
      Atom.All Extracted.programImage b n (Fn11c880.frameAt .l11d7d0 fr) ∧
      ParseSignature.ArgumentWidths b ∧ SavedWidths b ∧ WindowMemory fr n d ∧
      (∃ p : Projective, p.valid ∧ p.Stored n (fr.rsp - 0xb90) ∧ p.value = windowValue d k) ∧
      memLoad n (fr.rsp - 0xa68) 64 = BitVec.ofNat 64 k + 1 ∧
      memLoad n (fr.rsp - 0xbc8) 64 = (fr.r9 + BitVec.ofNat 64 (32+k)) + 1 ∧
      b[12].get 64 = fr.rsp - 0xcb8 + 0x490 := by
  obtain ⟨p, pv, acc, value⟩ := s.acc
  obtain ⟨a₁,m₁,p₁,s₁,acc₁⟩ := windowDoubles doubles entry bound s acc
  obtain ⟨a₂,m₂,p₂,s₂,acc₂,t₁,t₂,temp,zero⟩ := windowCopyTables entry s₁ acc₁
  obtain ⟨a₃,m₃,l,r,p₃,s₃,acc₃,lv,rv,left,right,temp,zero⟩ :=
    windowAdditions select add entry bound s₂ acc₂ t₁ t₂ temp zero
  obtain ⟨b,path,done,keep⟩ := windowRoundExit s₃ zero
  obtain ⟨v,w⟩ := windowRoundValue bound pv lv rv value left right
  exact ⟨b,m₃,((p₁.trans p₂).trans p₃).trans path,done.atoms,done.widths,done.saved,
    done.memory,⟨p.round l r,v,acc₃,w⟩,done.count,done.pointer,keep ▸ temp⟩

end K256.Proofs.Generate.Generator.Multiply
