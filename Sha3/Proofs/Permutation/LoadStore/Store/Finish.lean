import Sha3.Proofs.Permutation.LoadStore.Store.Result
import Sha3.Proofs.Permutation.LoadStore.Store.Image

namespace Sha3.Proofs.Permutation.Store

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program Keccak

theorem effect_avoids_program {copy : Copy} {sp pointer : BitVec 64} {s : RamState}
    (hprogram : ∀ i, i < 200 → ¬ InProgram (pointer + BitVec.ofNat 64 i)) :
    (effect copy sp pointer s).Avoids Extracted.programImage := by
  intro x hx c hc hcover
  obtain ⟨i, hi, haddr⟩ := effect_covers hc hcover
  exact hprogram i hi (haddr ▸ ⟨x.2, hx⟩)

theorem advance_of_moves [Bindings] (copy : Copy) (boundary : ReturnBoundary) (initial : RamState)
    (a : Lanes) (hboundary : ¬ InProgram boundary.rip)
    (htarget : (stackTop initial).toNat < 2^32)
    (hreturn : stackTop initial ≠ boundary.rip ∨ initial.regValue .rsp + 8 ≠ boundary.rsp)
    (hprogram : ∀ i, i < 200 → ¬ InProgram (initial.regValue .rdi + BitVec.ofNat 64 i))
    (hmoves : AdvanceTriple boundary 41 (Pre copy (frameBase initial) (initial.regValue .rdi))
      (codeRange (storeAddress copy) bytes)
      (Effect.post (effect copy (frameBase initial) (initial.regValue .rdi)))) :
    AdvanceTriple boundary 49
      (fun s ↦ Pre copy (frameBase initial) (initial.regValue .rdi) s ∧
        RoundInvariant copy initial 24 a s)
      Extracted.programImage (fun _ t ↦ CallResult initial t a) := by
  intro s hready hcode ⟨hpre, hinv⟩
  obtain ⟨t, hrun, ht, _, he⟩ :=
    hmoves s hready (hcode.mono (storeCode_subset_programImage copy)) hpre
  have hcode' := he.codeIn (effect_avoids_program hprogram) hcode
  have hrestore := restorePre_of_effect hpre hinv he htarget
  obtain ⟨u, hrun', hu, hcode'', hresult, _⟩ :=
    restore_advance copy boundary Extracted.programImage initial a
      (restoreCode_subset_programImage copy) (restore_boundary copy hboundary)
      hreturn t ht hcode' hrestore
  exact ⟨u, hrun.trans hrun', hu, hcode'', hresult⟩

end Sha3.Proofs.Permutation.Store
