import Sha1.Proofs.Buffered.DigestPrepare.Geometry

namespace Sha1.Proofs.Buffered.DigestPrepare.Long

open Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [bindings : Bindings] {initial s t : RamState} {boundary : ReturnBoundary}

set_option maxRecDepth 4096 in
theorem Frame.preserve_wide (h : Frame initial boundary s)
    (hs : Stack.Valid initial Digest.minStackBytes) {changes : List Component}
    (ha : AgreesExcept changes s t) (ht : ReadyToStep t)
    (hc : CodeIn Extracted.programImage t)
    (hreg : ∀ c ∈ changes, c.isMem = false →
      c ∈ digestPreparationChanges initial ∨ c.Agrees s t)
    (hmem : ∀ c ∈ changes, ∀ address, c.Covers address →
      (stackPtr s).toNat - 344 ≤ address.toNat ∧ address.toNat < (stackPtr s).toNat + 280)
    (hrsp : stackPtr t = stackPtr s) (hrbx : t.regValue .rbx = s.regValue .rbx)
    (hr14 : (Operand.reg 14 : Operand 64).read t = (Operand.reg 14 : Operand 64).read s) :
    Frame initial boundary t := by
  have hb := stack_bounds hs
  have hn := h.stackNat hs
  have hsave (offset : Nat) (hl : 280 ≤ offset) (hh : offset + 8 ≤ 320) :
      (Operand.mem (stackPtr t + BitVec.ofNat 64 offset) : Operand 64).read t =
        (Operand.mem (stackPtr s + BitVec.ofNat 64 offset) : Operand 64).read s := by
    rw [hrsp]
    apply memLoad_congr
    intro i hi
    apply congrArg (fun v : Option UInt8 ↦ v.getD 0)
    apply ha.byte
    intro c hc hcov
    have hx := hmem c hc _ hcov
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, toNat_add_ofNat _ _ (by omega)] at hx
    omega
  have hag : AgreesExcept (digestPreparationChanges initial) s t := by
    refine ⟨?_, ?_, ha.rest, ha.grow⟩
    · intro c hc hmem
      by_cases hcm : c ∈ changes
      · rcases hreg c hcm hmem with htarget | hagree
        · exact False.elim (hc htarget)
        · exact hagree
      · exact ha.agree c hcm hmem
    · intro address hx
      apply ha.memory address
      intro c hc hcov
      have hx' := hmem c hc address hcov
      have hstack := stack_region_contains hs (address := address.toNat)
        (by omega) (by omega)
      apply hx (.mem (BitVec.ofNat 64 (Stack.region initial Digest.minStackBytes).start)
        (Stack.region initial Digest.minStackBytes).size) (by simp [digestPreparationChanges])
      refine ⟨address.toNat - (Stack.region initial Digest.minStackBytes).start,
        Nat.sub_lt_left_of_lt_add hstack.1 hstack.2, ?_⟩
      rw [← BitVec.ofNat_add, Nat.add_sub_of_le hstack.1,
        BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine ⟨ht, hc, hag.directionFlagClear (by simp [digestPreparationChanges]) h.df,
    h.boundaryOutside, hrsp.trans h.stack, ?_, hrbx.trans h.output,
    (hsave 280 (by decide) (by decide)).trans h.savedRbx,
    (hsave 288 (by decide) (by decide)).trans h.savedR12,
    (hsave 296 (by decide) (by decide)).trans h.savedR14,
    (hsave 304 (by decide) (by decide)).trans h.savedR15,
    (hsave 312 (by decide) (by decide)).trans h.returnSlot,
    (h.agrees.trans hag).mono (by simp)⟩
  rw [hr14, h.statePointer, hrsp]

end Sha1.Proofs.Buffered.DigestPrepare.Long
