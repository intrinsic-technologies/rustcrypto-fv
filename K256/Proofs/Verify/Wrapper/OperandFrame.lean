import K256.Proofs.Verify.Wrapper.State

namespace K256.Proofs.Verify.Wrapper

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  CFG Lift Refine Verify.LIR Standards.SECG.ECC

theorem AffineInputs.afterHashWrites {initial : RamState} {m t : Ram} {p : Curve.Point} {r s : Nat}
    {key msg sig : ByteArray} (input : AffineInputs initial m p r s 352)
    (call : ValidCall verifyingKeyVerify initial [key,msg,sig]) {regions : List MemoryRegion}
    (writes : RamWriteFrame m t regions)
    (below : ∀ reg ∈ regions, reg.start + reg.size ≤ (localSp initial).toNat + 352) :
    AffineInputs initial t p r s 352 := by
  let sp := localSp initial
  obtain ⟨depth, room⟩ := Hash.Update.stackBounds call
  have base : sp.toNat = (stackPtr initial).toNat - 536 := Common.stackOffset call.stackAvailable (by decide)
  have apart (off n : Nat) (lo : 352 ≤ off) (hi : off + n ≤ 504) :
      Outside regions (sp + BitVec.ofNat 64 off) n := by
    have addr : (sp + BitVec.ofNat 64 off).toNat = sp.toNat + off := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := off) (by omega),
        Nat.mod_eq_of_lt (by omega)]
    refine ⟨by omega, fun reg member => Or.inr ?_⟩
    exact Nat.le_trans (below reg member) (by change sp.toNat + 352 ≤ _; omega)
  refine ⟨input.point.of_copy ?_, input.rAt.of_frame writes (by decide) (apart 352 32 (by decide) (by decide)),
    input.sAt.of_frame writes (by decide) (apart 384 32 (by decide) (by decide))⟩
  intro off width fit
  apply writes.memLoad_eq
  change Outside regions (sp + 416 + BitVec.ofNat 64 off) _
  rw [show sp + 416 + BitVec.ofNat 64 off = sp + BitVec.ofNat 64 (416 + off) by
    rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl]
  exact apart (416+off) _ (by omega) (by omega)

end K256.Proofs.Verify.Wrapper
