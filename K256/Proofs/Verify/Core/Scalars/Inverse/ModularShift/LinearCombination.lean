import K256.Proofs.Generate.Generator.Affine.Invert.Core.LinearCombination
import K256.Proofs.Generate.Serialize.Transfer.Relabel
import K256.Proofs.Verify.Core.State

namespace K256.Proofs.Verify.Core.Scalars.Inverse

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Common.Field
open Generate.Generator.Affine.Invert.Core (CalleeFrame CalleeResult LinearArgs wideSignedAt)
open Generate.Serialize

private def linearTarget : Generate.LIR.Label → Option LIR.Label
  | .l1084e0 => some .l1084e0
  | _ => none

set_option maxRecDepth 8192 in
private theorem linearBlocks (a : Generate.LIR.Label) (b : LIR.Label) (h : linearTarget a = some b) :
    Relabel.block linearTarget (Generate.LIR.program.blocks a) =
      Relabel.block some (LIR.program.blocks b) := by
  unfold linearTarget at h
  split at h <;> cases h <;> rfl

noncomputable abbrev CalleeExec (l : LIR.Label) (a : Registers) (m : Ram) (out : Output Value Ram Reg.count) :=
  LIR.program.Exec (dialect Extracted.programImage) ⟨⟨l, a, m⟩, []⟩ out

theorem linearCombination {a : Registers} {m : Ram} {sp dst ret : Word} {x y : Int} {u v : Word}
    (fr : CalleeFrame a m sp dst ret 112 41)
    (args : LinearArgs a m sp dst 112 41 x y u v) :
    ∃ out, CalleeExec .l1084e0 a m out ∧ CalleeResult a m sp dst ret 112 41 out ∧
      wideSignedAt out.store dst (x * u.toInt + y * v.toInt) := by
  obtain ⟨out, run, frame, value⟩ := Generate.Generator.Affine.Invert.Core.linearCombination fr args
  exact ⟨out, Relabel.exec linearBlocks run rfl, frame, value⟩

end K256.Proofs.Verify.Core.Scalars.Inverse
