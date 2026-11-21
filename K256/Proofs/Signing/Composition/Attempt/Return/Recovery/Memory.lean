import K256.Proofs.Signing.Composition.Attempt.Memory

namespace K256.Proofs.Signing.Composition.Attempt.Return.Recovery

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine

theorem preserveCore {s : RamState} {secret msg : ByteArray} {d : Nat} {m n : Ram}
    (call : ValidCall signingKeyTrySign s [secret,msg]) (memory : CoreMemory s d m)
    {regions : List MemoryRegion} (writes : RamWriteFrame m n regions)
    (bounds : ∀ t ∈ regions, (sp s).toNat - 9904 ≤ t.start ∧ t.start + t.size ≤ (sp s).toNat + 344) :
    CoreMemory s d n := by
  obtain ⟨room,high,base⟩ := stackBounds call
  have floor := Common.stackOffset (off := 11192) call.stackAvailable (by decide)
  apply memory.preserve writes
  · intro t member
    obtain ⟨lo,hi⟩ := bounds t member
    refine ⟨_,List.mem_singleton_self _,?_⟩
    rw [stackRegion call]
    change (stackPtr s - 11192).toNat ≤ t.start ∧ t.start + t.size ≤ (stackPtr s - 11192).toNat + 11200
    change (stackPtr s - 11192).toNat = (stackPtr s).toNat - 11192 at floor
    omega
  · intro i member
    have bi : 344 ≤ i ∧ i ≤ 1288 := by
      simp only [protectedOffsets,List.mem_cons,List.not_mem_nil,or_false] at member
      omega
    have addr := offsetNat (offset := i) call (by omega)
    refine ⟨by omega,fun t ht => Or.inr ?_⟩
    have := (bounds t ht).2
    omega

end K256.Proofs.Signing.Composition.Attempt.Return.Recovery
