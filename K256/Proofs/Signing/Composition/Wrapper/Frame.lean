import K256.Proofs.Signing.Composition.Wrapper.State

namespace K256.Proofs.Signing.Composition.Wrapper

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs CFG Lift Refine

theorem localSp_eq (s : RamState) : localSp s = stackPtr s - 472 := by
  unfold localSp sp
  bv_omega

theorem preserveSlots {s : RamState} {secret msg : ByteArray} {m n : Ram}
    (call : ValidCall signingKeyTrySign s [secret,msg]) (mem : Memory s m)
    {regions : List MemoryRegion} (writes : RamWriteFrame m n regions)
    (bounds : ∀ r ∈ regions, (stackPtr s).toNat - 11192 ≤ r.start ∧
      r.start + r.size ≤ (stackPtr s).toNat - 32) : Memory s n := by
  obtain ⟨room,high,_⟩ := stackBounds call
  have keep (off : Nat) (h : off ≤ 32) :
      memLoad n (stackPtr s - BitVec.ofNat 64 off) 64 =
        memLoad m (stackPtr s - BitVec.ofNat 64 off) 64 := by
    apply writes.memLoad_eq
    rw [show 64 / 8 = 8 by decide]
    have addr := Common.stackOffset call.stackAvailable (off := off) (show off ≤ 11192 by omega)
    refine ⟨by rw [addr]; omega, fun r hr => Or.inr ?_⟩
    rw [addr]
    have := (bounds r hr).2
    omega
  refine ⟨mem.written.trans writes ?_, ?_,
    (keep 32 (by decide)).trans mem.savedWrapperRBX, (keep 24 (by decide)).trans mem.savedWrapperR12,
    (keep 16 (by decide)).trans mem.savedWrapperR14, (keep 8 (by decide)).trans mem.savedWrapperR15⟩
  · intro r hr
    obtain ⟨lo,hi⟩ := bounds r hr
    exact ⟨_, List.mem_singleton_self _, lo, by
      change _ ≤ (stackPtr s).toNat - 11192 + ((stackPtr s).toNat+8-((stackPtr s).toNat-11192))
      omega⟩
  · rw [← mem.ret]
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.sub_zero] using keep 0 (by decide)

end K256.Proofs.Signing.Composition.Wrapper
