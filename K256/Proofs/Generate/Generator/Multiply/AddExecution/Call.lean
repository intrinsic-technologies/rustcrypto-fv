import K256.Proofs.Generate.Generator.Multiply.AddExecution.Words
import K256.Proofs.Generate.Generator.Multiply.AddExecution.Repr
import K256.Proofs.Common.Tactic
import K256.Proofs.Generate.Generator.Multiply.Coordinates
import K256.Proofs.Generate.LIR.Fn10a410.Frame
import K256.Proofs.ParseSignature.Contract

namespace K256.Proofs.Generate.Generator.Multiply

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine
open K256.Proofs.Generate.LIR

open K256.Proofs.Common.Point K256.Proofs.Common.Field

private theorem storedWords {p : Projective} {m : Ram} {base : BitVec 64} (h : p.Stored m base) :
    ∃ w : PointWords, PointWordsAt m base w ∧ Projective.WordsRepr w p := by
  obtain ⟨x, y, z, wx, wy, wz, rx, ry, rz⟩ := h.coordinates
  exact ⟨⟨x, y, z⟩, ⟨wx, wy, wz⟩, ⟨rx, ry, rz⟩⟩

private theorem coordBounds {w : PointWords} {p : Projective} (h : Projective.WordsRepr w p) :
    ∀ c ∈ [w.x, w.y, w.z], ∃ x, FieldRepr c x 1 := by
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact ⟨_, h.x⟩
  · exact ⟨_, h.y⟩
  · exact ⟨_, h.z⟩

theorem addCall {code : CodeMap} (included : ∀ a ∈ fnCode, a ∈ code)
    (fr : Activation) (args : Values Value Reg.count) (mem : Ram) (p q : Projective)
    (atoms : Atom.All code args mem (Fn10a410.frameAt .l10a410 fr))
    (src : Readable mem fr.rsi 120) (dst : Writable code mem fr.rdi 120)
    (srcAbove : fr.rsp.toNat + 8 ≤ fr.rsi.toNat) (dstAbove : fr.rsp.toNat + 8 ≤ fr.rdi.toNat)
    (apart : fr.rdi.toNat + 120 ≤ fr.rsi.toNat ∨ fr.rsi.toNat + 120 ≤ fr.rdi.toNat)
    (left : p.Stored mem fr.rdi) (right : q.Stored mem fr.rsi) :
    ∃ out, program.Exec (dialect code) ⟨⟨.l10a410, args, mem⟩, []⟩ out ∧
      out.tag = some ⟨64, fr.ret⟩ ∧ Atom.All code out.values out.store (Fn10a410.doneAt fr) ∧
      ParseSignature.ArgumentWidths out.values ∧ (p.add q).Stored out.store fr.rdi ∧
      RamWriteFrame mem out.store [⟨(fr.rsp - 0x218).toNat, 0x218⟩, ⟨fr.rdi.toNat, 120⟩] := by
  obtain ⟨a, aw, ha⟩ := storedWords left
  obtain ⟨b, bw, hb⟩ := storedWords right
  obtain ⟨out, run, tag, post, widths, vals, frame⟩ := addWordsCall included fr args mem a b
    atoms src dst srcAbove dstAbove apart (coordBounds ha) (coordBounds hb) aw bw
  have rep := ha.add hb
  exact ⟨out, run, tag, post, widths,
    ⟨_, _, _, vals.1, vals.2.1, vals.2.2, rep.x, rep.y, rep.z⟩, frame⟩

end K256.Proofs.Generate.Generator.Multiply
