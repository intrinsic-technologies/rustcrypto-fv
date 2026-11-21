import K256.Proofs.Generate.Generator.Multiply.AddExecution.Frame.Body
import K256.Proofs.Generate.Generator.Multiply.AddExecution.Frame.Entry
import K256.Proofs.Generate.Generator.Multiply.AddExecution.Frame.Finish
import K256.Proofs.Generate.Generator.Multiply.AddExecution.Frame.Preservation

namespace K256.Proofs.Generate.Generator.Multiply

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine
open K256.Proofs.Generate.LIR

theorem addReturns {code : CodeMap} (included : ∀ a ∈ fnCode, a ∈ code)
    (fr : Activation) (args : Values Value Reg.count) (mem : Ram)
    (atoms : Atom.All code args mem (Fn10a410.frameAt .l10a410 fr))
    (src : Readable mem fr.rsi 120) (dst : Writable code mem fr.rdi 120)
    (srcAbove : fr.rsp.toNat + 8 ≤ fr.rsi.toNat) (dstAbove : fr.rsp.toNat + 8 ≤ fr.rdi.toNat)
    (apart : fr.rdi.toNat + 120 ≤ fr.rsi.toNat ∨ fr.rsi.toNat + 120 ≤ fr.rdi.toNat)
    :
    ∃ out, program.runBlock (dialect code) ⟨.l10a410, args, mem⟩ = .returned out ∧
      out.tag = some ⟨64, fr.ret⟩ ∧ Atom.All code out.values out.store (Fn10a410.doneAt fr) ∧
      ParseSignature.ArgumentWidths out.values ∧
      RamWriteFrame mem out.store [⟨(fr.rsp - 0x218).toNat, 0x218⟩, ⟨fr.rdi.toNat, 120⟩] := by
  obtain ⟨b, m, entry, frame, s⟩ := AddFrame.enterBody included atoms src dst srcAbove dstAbove apart
  have initial := atoms
  simp only [Fn10a410.frameAt, Fn10a410.frameAtG0, Atom.All, Atom.Holds] at initial
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rd, _, _, stack, depth, _⟩ := initial
  obtain ⟨c, t, middle, p, scratch⟩ := AddFrame.body included s.size s.sp (stack.of_frame frame)
  have room : 0x218 ≤ fr.rsp.toNat := by omega
  have state := s.preserve p scratch room rd.low
  have total := frame.trans scratch (AddFrame.spillsWithin fr room)
  obtain ⟨out, finish, tag, done_, widths, frame'⟩ :=
    AddFrame.finishBody included atoms src dst srcAbove dstAbove apart total state
  exact ⟨out, entry.trans (middle.trans finish), tag, done_, widths, frame'⟩

end K256.Proofs.Generate.Generator.Multiply
