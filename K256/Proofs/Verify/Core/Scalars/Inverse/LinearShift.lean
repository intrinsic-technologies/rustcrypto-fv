import K256.Proofs.Verify.Core.Affine.Transfer
import K256.Proofs.Generate.Generator.Affine.Invert.Core.LinearShift
import K256.Proofs.Verify.Core.State

namespace K256.Proofs.Verify.Core.Scalars.Inverse

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Common.Field
open Generate.Generator.Affine.Invert.Core (CalleeFrame CalleeResult LinearArgs signedAt)

theorem linearShift {a : Registers} {m : Ram} {sp dst ret : Word} {x y q : Int} {u v : Word}
    {shift : Nat} (fr : CalleeFrame a m sp dst ret 208 33)
    (args : LinearArgs a m sp dst 208 33 x y u v)
    (hs : a[9].get 32 = BitVec.ofNat 32 shift) (pos : 0 < shift) (bound : shift ≤ 62)
    (row : (2 : Int)^shift * q = x * u.toInt + y * v.toInt) (fits : q.natAbs < 2^256) :
    ∃ out, LIR.program.Exec (dialect Extracted.programImage) ⟨⟨.l108890, a, m⟩, []⟩ out ∧
      CalleeResult a m sp dst ret 208 33 out ∧ signedAt out.store dst q := by
  obtain ⟨out, run, result⟩ := Generate.Generator.Affine.Invert.Core.linearShift fr args hs pos bound row fits
  exact ⟨out, Core.Affine.transferAt (src := .l108890) (dst := .l108890) rfl run, result⟩

end K256.Proofs.Verify.Core.Scalars.Inverse
