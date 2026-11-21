import K256.Proofs.Signing.Hash.State
import K256.Proofs.Generate.Generator.Affine.Invert.Core.Callee

namespace K256.Proofs.Signing.Hash

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
open K256.Proofs.Verify.Hash

theorem imageAfter {sp : BitVec 64} {m t : Ram} (depth : 512 ≤ sp.toNat)
    (stack : Writable Extracted.programImage m (sp - 512) 1672)
    (writes : RamWriteFrame m t (regions sp))
    (image : ∀ b ∈ Extracted.programImage, m[b.1]? = some b.2) :
    ∀ b ∈ Extracted.programImage, t[b.1]? = some b.2 := by
  apply Generate.Generator.Affine.Invert.Core.stackImage stack _ image
  apply (RamWriteFrame.refl _ _).trans writes
  have low : (sp - 512).toNat = sp.toNat - 512 :=
    BitVec.toNat_sub_of_le (show (512 : BitVec 64) ≤ sp from depth)
  intro r hr
  refine ⟨_, List.mem_cons_self, ?_⟩
  simp only [regions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> dsimp <;> omega

end K256.Proofs.Signing.Hash
