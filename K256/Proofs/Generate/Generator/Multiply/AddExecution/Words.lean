import K256.Proofs.Generate.Generator.Multiply.AddExecution.Safety
import K256.Proofs.Generate.Generator.Multiply.AddExecution.Certificate
namespace K256.Proofs.Generate.Generator.Multiply

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine
open K256.Proofs.Generate.LIR

open K256.Proofs.Common.Point

theorem addWordsCall {code : CodeMap} (included : ∀ a ∈ fnCode, a ∈ code)
    (fr : Activation) (args : Values Value Reg.count) (mem : Ram) (p q : PointWords)
    (atoms : Atom.All code args mem (Fn10a410.frameAt .l10a410 fr))
    (src : Readable mem fr.rsi 120) (dst : Writable code mem fr.rdi 120)
    (srcAbove : fr.rsp.toNat + 8 ≤ fr.rsi.toNat) (dstAbove : fr.rsp.toNat + 8 ≤ fr.rdi.toNat)
    (apart : fr.rdi.toNat + 120 ≤ fr.rsi.toNat ∨ fr.rsi.toNat + 120 ≤ fr.rdi.toNat)
    (pBound : ∀ w ∈ [p.x, p.y, p.z], ∃ x, K256.Proofs.Common.Field.FieldRepr w x 1)
    (qBound : ∀ w ∈ [q.x, q.y, q.z], ∃ x, K256.Proofs.Common.Field.FieldRepr w x 1)
    (left : PointWordsAt mem fr.rdi p) (right : PointWordsAt mem fr.rsi q) :
    ∃ out, program.Exec (dialect code) ⟨⟨.l10a410, args, mem⟩, []⟩ out ∧
      out.tag = some ⟨64, fr.ret⟩ ∧ Atom.All code out.values out.store (Fn10a410.doneAt fr) ∧
      ParseSignature.ArgumentWidths out.values ∧ PointWordsAt out.store fr.rdi (AddWords.add p q) ∧
      RamWriteFrame mem out.store [⟨(fr.rsp - 0x218).toNat, 0x218⟩, ⟨fr.rdi.toNat, 120⟩] := by
  obtain ⟨out, run, tag, done_, widths, frame⟩ := addReturns included fr args mem atoms
    src dst srcAbove dstAbove apart
  exact ⟨out, .done (by simp only [Program.step, run, Transfer.next]), tag, done_, widths,
    addStoredWords included fr args mem p q atoms src dst srcAbove dstAbove apart
      pBound qBound left right run, frame⟩

end K256.Proofs.Generate.Generator.Multiply
