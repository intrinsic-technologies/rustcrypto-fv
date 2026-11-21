import K256.Proofs.Signing.Composition.Attempt.Call

namespace K256.Proofs.Signing.Composition.Attempt

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine

structure StackBounds (s : RamState) : Prop where
  room : 9904 ≤ (sp s).toNat
  high : (sp s).toNat + 1296 < 2^32
  alignment : (sp s).toNat % 16 = 0

theorem StackBounds.ofCall {s : RamState} {secret msg : ByteArray}
    (call : ValidCall signingKeyTrySign s [secret,msg]) : StackBounds s := by
  obtain ⟨room, high, spNat⟩ := stackBounds call
  have aligned : (stackPtr s).toNat % 16 = 8 := call.stackAvailable.2.2.2
  exact ⟨by omega, by omega, by omega⟩

theorem StackBounds.above {s : RamState} (g : StackBounds s) (off : BitVec 64)
    (h : off.toNat ≤ 1296) : (sp s + off).toNat = (sp s).toNat + off.toNat := by
  have := g.high
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]

theorem StackBounds.below {s : RamState} (g : StackBounds s) (off : BitVec 64)
    (h : off.toNat ≤ 9904) : (sp s - off).toNat = (sp s).toNat - off.toNat :=
  BitVec.toNat_sub_of_le (BitVec.le_def.mpr (Nat.le_trans h g.room))

theorem StackBounds.window {s : RamState} {secret msg : ByteArray} {m : Ram}
    (_g : StackBounds s) (call : ValidCall signingKeyTrySign s [secret,msg]) (memory : Memory s m) :
    Writable Extracted.programImage m (sp s - 9904) 11200 := by
  rw [show sp s - 9904 = stackPtr s - 11192 by unfold sp; bv_omega]
  exact memory.window call

theorem StackBounds.slot {s : RamState} {secret msg : ByteArray} {m : Ram}
    (g : StackBounds s) (call : ValidCall signingKeyTrySign s [secret,msg]) (memory : Memory s m)
    {p : BitVec 64} {n : Nat}
    (lower : (sp s).toNat - 9904 ≤ p.toNat) (upper : p.toNat + n ≤ (sp s).toNat + 1296) :
    Writable Extracted.programImage m p n := by
  have room := g.room
  have base : (sp s - 9904).toNat = (sp s).toNat - 9904 := g.below 9904 (by decide)
  exact (g.window call memory).sub (by rw [base]; exact lower) (by rw [base]; omega)

theorem StackBounds.pushFrame {s : RamState} {m : Ram} (g : StackBounds s) (tag : BitVec 64) :
    RamWriteFrame m (memStore m (sp s - 8) tag) [⟨(sp s - 8).toNat,8⟩] := by
  have limit := g.high
  have addr : (sp s - 8).toNat = (sp s).toNat - 8 := g.below 8 (by decide)
  refine (RamWriteFrame.refl _ _).memStore _ ⟨_, List.mem_cons_self, ?_⟩
  change (sp s - 8).toNat ≤ (sp s - 8).toNat ∧
    (sp s - 8).toNat + 8 ≤ (sp s - 8).toNat + 8 ∧ (sp s - 8).toNat + 8 ≤ 2^64
  exact ⟨Nat.le_refl _,Nat.le_refl _,by omega⟩

theorem StackBounds.inside {s : RamState} {secret msg : ByteArray}
    (g : StackBounds s) (call : ValidCall signingKeyTrySign s [secret,msg])
    {regions : List MemoryRegion}
    (lower : ∀ r ∈ regions, (sp s).toNat - 9904 ≤ r.start)
    (upper : ∀ r ∈ regions, r.start + r.size ≤ (sp s).toNat + 1296) :
    RegionsWithin regions [Stack.region s signingKeyTrySign.minStackBytes] := by
  intro r hr
  rw [stackRegion call, show stackPtr s - 11192 = sp s - 9904 by unfold sp; bv_omega]
  refine ⟨_,List.mem_cons_self,?_⟩
  have room := g.room
  have bot : (sp s - 9904).toNat = (sp s).toNat - 9904 := g.below 9904 (by decide)
  change (sp s - 9904).toNat ≤ _ ∧ _ ≤ (sp s - 9904).toNat + 11200
  rw [bot]
  exact ⟨lower r hr, by have := upper r hr; omega⟩

theorem StackBounds.outside {s : RamState} (g : StackBounds s) {rs : List MemoryRegion}
    (off : BitVec 64) (n : Nat) (fit : off.toNat + n ≤ 1296)
    (apart : ∀ r ∈ rs, (sp s).toNat + off.toNat + n ≤ r.start ∨ r.start+r.size ≤ (sp s).toNat + off.toNat) :
    Outside rs (sp s+off) n := by
  have top := g.high
  simp only [Outside, g.above off (by omega)]
  exact ⟨by omega, apart⟩

theorem LoopMemory.preserveCoordinates {s : RamState} {secret msg : ByteArray} {d : Nat} {st : State}
    {m t : Ram} {rs : List MemoryRegion}
    (g : StackBounds s) (call : ValidCall signingKeyTrySign s [secret,msg])
    (h : LoopMemory s d msg st m) (writes : RamWriteFrame m t rs)
    (lower : ∀ r ∈ rs, (sp s).toNat - 9904 ≤ r.start)
    (apart : ∀ r ∈ rs, r.start + r.size ≤ (sp s).toNat + 344 ∨
      (sp s).toNat + 424 ≤ r.start ∧ r.start + r.size ≤ (sp s).toNat + 592) :
    LoopMemory s d msg st t := by
  have outside (off : BitVec 64) (n : Nat) (fit : off.toNat + n ≤ 1296)
      (hole : 344 ≤ off.toNat ∧ off.toNat + n ≤ 424 ∨ 592 ≤ off.toNat) :
      Outside rs (sp s+off) n := by
    apply g.outside off n fit
    intro r hr
    rcases apart r hr with h | h <;> rcases hole with w | w <;> omega
  apply h.preserve call writes (g.inside call lower (by
    intro r hr; rcases apart r hr with h | h <;> omega))
  · intro i hi
    simp only [protectedOffsets, List.mem_cons, List.not_mem_nil, or_false] at hi
    apply outside
    all_goals simp only [BitVec.toNat_ofNat]
    all_goals rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl <;> decide
  · exact outside 352 32 (by decide) (by decide)
  · exact outside 592 32 (by decide) (by decide)
  · exact outside 688 72 (by decide) (by decide)

end K256.Proofs.Signing.Composition.Attempt
