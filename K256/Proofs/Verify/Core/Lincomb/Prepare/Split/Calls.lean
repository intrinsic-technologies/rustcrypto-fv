import K256.Proofs.Verify.Core.Lincomb.Prepare.Split.Calls.FirstRound
import K256.Proofs.Verify.Core.Lincomb.Prepare.Split.Calls.Advance

namespace K256.Proofs.Verify.Core.Lincomb.Prepare

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Multiply (scalarWords)
open Generate.Curve

open SplitCalls

theorem splitResidues {a : Registers} {m : Ram} {sp src scalar tables digits : BitVec 64}
    {k : Nat} (entry : RoutineEntry a m sp 0x558)
    (di : a[7] = ⟨64, src⟩) (si : a[6] = ⟨64, scalar⟩) (dx : a[2] = ⟨64, tables⟩)
    (cx : a[1] = ⟨64, digits⟩) (bound : k < domain.n)
    (words : WordsAt m scalar 64 (Generate.Generator.Multiply.scalarWords k))
    (scalarRead : Readable m scalar 32)
    (scalarApart : Outside [scratch sp 0x558] scalar 32) :
    ∃ b n, Reaches .l10f150 a m .l10f221 b n ∧ Residues a m sp src tables digits k b n := by
  obtain ⟨b₁,n₁,h₁,s₁,w₁⟩ := firstRound entry di si dx cx bound words scalarRead scalarApart
  have v₁ : Stored sp n₁ (results .roundFirst k) := by
    intro kv h
    obtain rfl := List.mem_singleton.mp h
    exact w₁
  obtain ⟨b₂,n₂,h₂,s₂,v₂⟩ := advance .mulFirst (by decide) entry bound words scalarRead scalarApart s₁ v₁
  obtain ⟨b₃,n₃,h₃,s₃,v₃⟩ := advance .roundSecond (by decide) entry bound words scalarRead scalarApart s₂ v₂
  obtain ⟨b₄,n₄,h₄,s₄,v₄⟩ := advance .mulSecond (by decide) entry bound words scalarRead scalarApart s₃ v₃
  obtain ⟨b₅,n₅,h₅,s₅,v₅⟩ := advance .addSecond (by decide) entry bound words scalarRead scalarApart s₄ v₄
  obtain ⟨b₆,n₆,h₆,s₆,v₆⟩ := advance .mulLambda (by decide) entry bound words scalarRead scalarApart s₅ v₅
  obtain ⟨b₇,n₇,h₇,s₇,v₇⟩ := advance .addFirst (by decide) entry bound words scalarRead scalarApart s₆ v₆
  exact ⟨b₇,n₇,h₁.trans (h₂.trans (h₃.trans (h₄.trans (h₅.trans (h₆.trans h₇))))),
    s₇.toSplitFrame,v₇ (56,splitFirst k) (.head _),v₇ (176,splitSecond k) (.tail _ (.head _))⟩

end K256.Proofs.Verify.Core.Lincomb.Prepare
