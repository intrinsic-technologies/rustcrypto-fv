import K256.Proofs.Verify.Transfer.Compare
import K256.Proofs.Verify.Core.State
import K256.Proofs.Generate.Generator.Sample.Decide.Nonzero.Compare
import K256.Proofs.Generate.Generator.Multiply.Split.WideProduct

namespace K256.Proofs.Verify.Core

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Generate.Generator.Multiply

theorem compareNonzero {fr : Activation} {a : Registers} {k : Nat}
    (pre : Atom.All Extracted.programImage a fr.original (Generate.LIR.Fn10a280.frameInfo.entryAtoms fr))
    (left : Readable fr.original fr.rdi 32) (right : Readable fr.original fr.rsi 32)
    (leftApart : Outside [fr.region] fr.rdi 32) (rightApart : Outside [fr.region] fr.rsi 32)
    (x : WordsAt fr.original fr.rdi 64 (scalarWords k))
    (zero : WordsAt fr.original fr.rsi 64 (Vector.replicate 4 0))
    (pos : 0 < k) (bound : k < 2^256) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l10a280, a, fr.original⟩, []⟩ out ∧
      out.tag = some ⟨64, fr.ret⟩ ∧
      Atom.All Extracted.programImage out.values out.store (Generate.LIR.Fn10a280.frameInfo.doneAtoms fr) ∧
      RamWriteFrame fr.original out.store [fr.region] ∧ ParseSignature.ArgumentWidths out.values ∧
      out.values[0].get 8 = 0 := by
  obtain ⟨out, run, tag, done_, writes, widths, one, binary⟩ :=
    Generate.Generator.Sample.compareFour fr left right leftApart rightApart a pre
  refine ⟨out, Transfer.compareExec (src := .l10a280) rfl run, tag, done_, writes, widths, ?_⟩
  rcases binary with h | h
  · exact h
  · have eq : scalarWords k = Vector.replicate 4 0 := by
      apply Vector.ext
      intro i hi
      exact (x i hi).symm.trans (((one.mp h) i hi).trans (zero i hi))
    have value := Split.scalarWords_value k bound
    rw [eq] at value
    change 0 = k at value
    omega

end K256.Proofs.Verify.Core
