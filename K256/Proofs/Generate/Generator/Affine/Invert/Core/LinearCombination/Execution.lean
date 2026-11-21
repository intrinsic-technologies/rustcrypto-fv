import K256.Proofs.Generate.Generator.Affine.Invert.Core.LinearCombination.Products
import K256.Proofs.Generate.Generator.Affine.Invert.Core.LinearCombination.Signs
import K256.Proofs.Generate.Generator.Affine.Invert.Core.LinearCombination.Difference
import K256.Proofs.Generate.Generator.Affine.Invert.Core.LinearCombination.Output

namespace K256.Proofs.Generate.Generator.Affine.Invert.Core.LinearCombination
open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
open K256.Proofs.Common.Invert.LinearCombination
open K256.Proofs.Sec1.Affine.Uncompressed

theorem machine (a : Registers) (m : Ram) (sp dst ret left right : BitVec 64) (p : Inputs)
    {x y : Int} (fr : CalleeFrame a m sp dst ret 112 41)
    (lsrc : SignedSource m sp dst left 112 41 x) (rsrc : SignedSource m sp dst right 112 41 y)
    (h : At1084e0 a sp dst ret left right p a m) :
    ∃ out, CalleeExec .l1084e0 a m out ∧
      RamWriteFrame m out.store [⟨(sp - 112).toNat, 112⟩, ⟨dst.toNat, 41⟩] ∧
      Returned a sp dst ret p out := by
  obtain ⟨b1, m1, e0, fr1, h1⟩ := eval1084e0 fr lsrc rsrc (RamWriteFrame.refl _ _) h
  obtain ⟨b2, m2, e1, fr2, h2⟩ := eval108519 fr lsrc rsrc fr1 h1
  obtain ⟨b3, m3, e2, fr3, h3⟩ := eval10855c fr lsrc rsrc fr2 h2
  obtain ⟨b4, m4, e3, fr4, h4⟩ := eval1085a1 fr lsrc rsrc fr3 h3
  obtain ⟨b5, m5, e4, fr5, h5⟩ := eval1085f2 fr lsrc rsrc fr4 h4
  obtain ⟨b6, m6, e5, fr6, h6⟩ := eval108640 fr lsrc rsrc fr5 h5
  obtain ⟨b7, m7, e6, fr7, h7⟩ := eval108684 fr lsrc rsrc fr6 h6
  obtain ⟨b8, m8, e7, fr8, h8⟩ := eval1086c8 fr lsrc rsrc fr7 h7
  obtain ⟨b9, m9, e8, fr9, h9⟩ := eval108709 fr lsrc rsrc fr8 h8
  obtain ⟨b10, m10, e9, fr10, h10⟩ := eval10874b fr lsrc rsrc fr9 h9
  obtain ⟨b11, m11, e10, fr11, h11⟩ := eval10878d fr lsrc rsrc fr10 h10
  obtain ⟨b12, m12, e11, fr12, h12⟩ := eval1087d9 fr lsrc rsrc fr11 h11
  obtain ⟨b13, m13, e12, fr13, h13⟩ := eval10881b fr lsrc rsrc fr12 h12
  obtain ⟨b14, m14, e13, fr14, h14⟩ := eval10885c fr lsrc rsrc fr13 h13
  obtain ⟨out, e14, outMem, done_⟩ := emit a sp dst ret left right p b14 m14 h14
  rw [← outMem] at fr14
  refine ⟨out, Program.Exec.done ?_, fr14, done_⟩
  change (b_l1084e0.eval (dialect Extracted.programImage) a m).next _ _ = _
  rw [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14]
  rfl

end K256.Proofs.Generate.Generator.Affine.Invert.Core.LinearCombination
