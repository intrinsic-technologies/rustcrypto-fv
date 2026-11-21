import K256.Proofs.Generate.Generator.Multiply.AddExecution.Arithmetic.Formula
import K256.Proofs.Generate.Generator.Multiply.AddExecution.Replay.Return
import K256.Proofs.Generate.Generator.Multiply.AddExecution.Replay.Compose.Endpoints
import K256.Proofs.Generate.Generator.Multiply.AddExecution.Segments.A
import K256.Proofs.Generate.Generator.Multiply.AddExecution.Segments.B
import K256.Proofs.Generate.Generator.Multiply.AddExecution.Segments.C
import K256.Proofs.Generate.Generator.Multiply.AddExecution.Segments.D

namespace K256.Proofs.Generate.Generator.Multiply

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine
open K256.Proofs.Generate.LIR

open K256.Proofs.Common.Point

theorem addStoredWords {code : CodeMap} (included : ∀ a ∈ fnCode, a ∈ code)
    (fr : Activation) (args : Values Value Reg.count) (mem : Ram) (p q : PointWords)
    (atoms : Atom.All code args mem (Fn10a410.frameAt .l10a410 fr))
    (src : Readable mem fr.rsi 120) (dst : Writable code mem fr.rdi 120)
    (srcAbove : fr.rsp.toNat + 8 ≤ fr.rsi.toNat) (dstAbove : fr.rsp.toNat + 8 ≤ fr.rdi.toNat)
    (apart : fr.rdi.toNat + 120 ≤ fr.rsi.toNat ∨ fr.rsi.toNat + 120 ≤ fr.rdi.toNat)
    (pBound : ∀ w ∈ [p.x, p.y, p.z], ∃ x, K256.Proofs.Common.Field.FieldRepr w x 1)
    (qBound : ∀ w ∈ [q.x, q.y, q.z], ∃ x, K256.Proofs.Common.Field.FieldRepr w x 1)
    (left : PointWordsAt mem fr.rdi p) (right : PointWordsAt mem fr.rsi q)
    {out : Output Value Ram Reg.count}
    (run : program.runBlock (dialect code) ⟨.l10a410, args, mem⟩ = .returned out) :
    PointWordsAt out.store fr.rdi (AddWords.add p q) := by
  let s : AddReplay.Inputs := ⟨fr, mem, args, p, q⟩
  obtain ⟨ready, values, memory⟩ :=
    AddReplay.entry s atoms src dst srcAbove dstAbove apart left right
  obtain ⟨last, final, evaluated, _, state, _⟩ :=
    (BodySegment.trans
      (BodySegment.trans (AddReplay.segmentsA included s ready) (AddReplay.segmentsB included s ready))
      (BodySegment.trans (AddReplay.segmentsC included s ready) (AddReplay.segmentsD included s ready)))
      values memory
  change b_l10a410.eval (dialect code) args mem = .returned out at run
  have store := AddReplay.returnedStore (a := last) (evaluated.symm.trans run)
  rw [store, ← AddGraph.output_eq_add p q pBound qBound]
  exact AddReplay.storedOutput s state

end K256.Proofs.Generate.Generator.Multiply
