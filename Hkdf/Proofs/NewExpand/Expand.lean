import Hkdf.Proofs.NewExpand.Expand.Entry
import Hkdf.Proofs.NewExpand.Expand.Return
import Hkdf.Proofs.NewExpand.Expand.Positive

namespace Hkdf.Proofs.NewExpand

open Hkdf.Spec.Program X86.UserProcess

theorem expand_correct [X86.Machine.Bindings] : ExpandContract := by
  intro entry boundary key info ptr length pre
  obtain ⟨s, state⟩ := Expand.dispatch pre
  by_cases early : length = 0 ∨ 8160 < length
  · apply Expand.finish pre state.toSavedFrame (state.pc.trans (ite_eq_left early))
    intro enough
    have zero : length = 0 := by omega
    subst length
    exact ⟨ByteArray.empty, Common.expandFromPrk_sha256_zero _ _ (Nat.le_of_eq pre.keySize.symm),
      rfl, fun i => Fin.elim0 i⟩
  · obtain ⟨t, saved, pc, bytes⟩ := Expand.positive pre state (by omega) (by omega)
    exact Expand.finish pre saved pc (fun _ => bytes)

end Hkdf.Proofs.NewExpand
