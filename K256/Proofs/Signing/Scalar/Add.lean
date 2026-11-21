import K256.Proofs.Verify.Core.Lincomb.Transfer
import K256.Proofs.Generate.Generator.Multiply.Split.Addition.Execution
import K256.Proofs.Verify.LIR.Fn10a2e0.Frame
import K256.Proofs.Common.Lift.Generated.Values.Register2

namespace K256.Proofs.Signing.Scalar

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  CFG Lift Refine Verify.LIR Generate.Generator.Multiply
  Standards.SECG.DomainParameters.Secp256k1

private theorem addEntry {fr : Activation} {a : Values Value Reg.count} {m : Ram}
    (entry : Atom.All Extracted.programImage a m (Fn10a2e0.frameAt .l10a2e0 fr)) :
    ∃ b, program.runBlock (dialect Extracted.programImage) ⟨.l10a2e0,a,m⟩ =
      .jump ⟨.l1109b0,b,m⟩ ∧ Atom.All Extracted.programImage b m
      (Generate.LIR.Fn1109b0.frameAt .l1109b0 {fr with rcx := 0x2021a0}) := by
  refine ⟨?args, ?step, ?post⟩
  case step =>
    cfg_eval
    rfl
  case post =>
    simp only [Fn10a2e0.frameAt, Fn10a2e0.frameAtG12, Atom.All, Atom.Holds] at entry
    exact ⟨entry.1, entry.2.1, rfl, entry.2.2.2⟩

theorem add {fr : Activation} {a : Values Value Reg.count} {m : Ram} {x y : Nat}
    (entry : Atom.All Extracted.programImage a m (Fn10a2e0.frameAt .l10a2e0 fr))
    (image : ∀ b ∈ Extracted.programImage, m[b.1]? = some b.2) (hx : x < domain.n) (hy : y < domain.n)
    (rx : Readable m fr.rsi 32) (ry : Readable m fr.rdx 32) (dst : Writable Extracted.programImage m fr.rdi 32)
    (above : fr.rsp.toNat + 8 ≤ fr.rdi.toNat)
    (apart : ∀ src ∈ [fr.rsi, fr.rdx],
      (src.toNat + 32 ≤ fr.rsp.toNat - 64 ∨ fr.rsp.toNat + 8 ≤ src.toNat) ∧
      (src.toNat + 32 ≤ fr.rdi.toNat ∨ fr.rdi.toNat + 32 ≤ src.toNat))
    (wx : WordsAt m fr.rsi 64 (scalarWords x)) (wy : WordsAt m fr.rdx 64 (scalarWords y)) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l10a2e0,a,m⟩,[]⟩ out ∧
      out.tag = some ⟨64,fr.ret⟩ ∧ Atom.All Extracted.programImage out.values out.store (Fn10a2e0.doneAt fr) ∧
      ParseSignature.ArgumentWidths out.values ∧ WordsAt out.store fr.rdi 64 (scalarWords ((x+y)%domain.n)) ∧
      RamWriteFrame m out.store [⟨fr.rsp.toNat-64,64⟩, ⟨fr.rdi.toNat,32⟩] := by
  obtain ⟨b, step, atoms⟩ := addEntry entry
  obtain ⟨out, run, tag, frame, widths, words, written⟩ :=
    Split.add atoms image (fun _ => rfl) hx hy rx ry dst above apart wx wy
  have path := Verify.Core.Lincomb.transfer (dst := .l1109b0) (by simp [Verify.Core.Lincomb.sharedEntry]) run
  exact ⟨out, .next (by simp only [Program.step, step, Transfer.next_jump]) path,
    tag, frame, widths, words, written⟩

end K256.Proofs.Signing.Scalar
