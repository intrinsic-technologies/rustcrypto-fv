import K256.Proofs.Signing.Composition.Attempt.Memory

namespace K256.Proofs.Signing.Composition.Attempt.Inverse

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine

def digestRegions (p : BitVec 64) : List MemoryRegion :=
  [⟨(p-216).toNat,504⟩, ⟨(p+624).toNat,64⟩]

theorem preserveDigestMemory {s : RamState} {d : Nat} {msg secret : ByteArray} {st : State}
    {m n : Ram} (call : ValidCall signingKeyTrySign s [secret,msg]) (memory : LoopMemory s d msg st m)
    (writes : RamWriteFrame m n (digestRegions (sp s))) : LoopMemory s d msg st n := by
  obtain ⟨room,limit,base⟩ := stackBounds call
  have bottom : (stackPtr s-11192).toNat = (stackPtr s).toNat-11192 := Common.stackOffset (off := 11192) call.stackAvailable (by decide)
  have low : (sp s-216).toNat = (sp s).toNat-216 :=
    BitVec.toNat_sub_of_le (by change 216 ≤ (sp s).toNat; omega)
  have upper : (sp s+624).toNat = (sp s).toNat+624 := offsetNat call (by decide : 624 ≤ 1296)
  have inside : RegionsWithin (digestRegions (sp s)) [Stack.region s signingKeyTrySign.minStackBytes] := by
    rw [stackRegion call]
    intro r hr
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    simp only [digestRegions,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl <;> simp only [low,upper,bottom] <;> omega
  have apart {i len : Nat} (fits : i+len ≤ 1296) (above : 288 ≤ i)
      (disj : i+len ≤ 624 ∨ 688 ≤ i) : Outside (digestRegions (sp s)) (sp s+BitVec.ofNat 64 i) len := by
    have addr := offsetNat call (show i ≤ 1296 by omega)
    refine ⟨by rw [addr]; omega,fun r hr => ?_⟩
    simp only [digestRegions,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl <;> simp only [low,upper,addr] <;> omega
  refine memory.preserve call writes inside ?_ (apart (i := 352) (by decide) (by decide) (by decide))
    (apart (i := 592) (by decide) (by decide) (by decide)) (apart (i := 688) (by decide) (by decide) (by decide))
  intro i hi
  simp only [protectedOffsets,List.mem_cons,List.not_mem_nil,or_false] at hi
  exact apart (by omega) (by omega) (by omega)

end K256.Proofs.Signing.Composition.Attempt.Inverse
