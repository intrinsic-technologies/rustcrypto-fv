import K256.Proofs.Signing.Composition.Attempt.State
import K256.Proofs.Signing.Composition.Memory

namespace K256.Proofs.Signing.Composition.Attempt

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine

theorem stackWindow {s : RamState} {secret msg : ByteArray} {m : Ram}
    (call : ValidCall signingKeyTrySign s [secret,msg]) (memory : Memory s m)
    {offset : BitVec 64} {size : Nat} (within : (offset + 9904).toNat + size ≤ 11200) :
    Writable Extracted.programImage m (sp s + offset) size := by
  have lower : stackPtr s - 11192 = sp s + (0 - 9904) := by
    unfold sp
    bv_omega
  exact (memory.window call).of_offsets rfl lower (by
    rw [show offset - (0 - 9904) = offset + 9904 by bv_omega]
    exact within)

theorem offsetNat {s : RamState} {secret msg : ByteArray}
    (call : ValidCall signingKeyTrySign s [secret,msg]) {offset : Nat} (within : offset ≤ 1296) :
    (sp s + BitVec.ofNat 64 offset).toNat = (sp s).toNat + offset := by
  obtain ⟨room, high, base⟩ := stackBounds call
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := offset) (by omega)]
  exact Nat.mod_eq_of_lt (by omega)

theorem belowNat {s : RamState} {secret msg : ByteArray}
    (call : ValidCall signingKeyTrySign s [secret,msg]) {depth : Nat} (within : depth ≤ 9904) :
    (sp s - BitVec.ofNat 64 depth).toNat = (sp s).toNat - depth := by
  obtain ⟨room, _, base⟩ := stackBounds call
  have n : (BitVec.ofNat 64 depth).toNat = depth := Nat.mod_eq_of_lt (by omega)
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def,n]; omega),n]

def workRegions (s : RamState) : List MemoryRegion :=
  [⟨(sp s-9904).toNat,10248⟩,⟨(sp s+384).toNat,32⟩,
    ⟨(sp s+424).toNat,168⟩,⟨(sp s+624).toNat,64⟩]

theorem hasBytes_of_frame {m n : Ram} {regions : List MemoryRegion} {a : BitVec 64}
    {size : Nat} {bytes : ByteArray} (writes : RamWriteFrame m n regions) (outside : Outside regions a size)
    (atBytes : (⟨a.toNat,size⟩ : MemoryRegion).HasBytes m bytes) :
    (⟨a.toNat,size⟩ : MemoryRegion).HasBytes n bytes := by
  refine ⟨atBytes.1, fun i => ?_⟩
  have len : bytes.size = size := atBytes.1
  have addr : (BitVec.ofNat 64 (a.toNat+i.val)).toNat = a.toNat+i.val := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by have := outside.1; omega)
  rw [writes.outside _ ⟨by rw [addr]; have := outside.1; omega, fun r hr => by
    rw [addr]
    rcases outside.2 r hr with lower | upper <;> omega⟩]
  exact atBytes.2 i

theorem loopMemory_of_outer {s : RamState} {d : Nat} {msg : ByteArray} {st : State}
    {a : Verify.Core.Registers} {m : Ram} (outer : Outer s d msg st a m) :
    LoopMemory s d msg st m :=
  ⟨outer.toCoreMemory,outer.hash,outer.order,outer.orderPtr,outer.state⟩

theorem LoopMemory.preserve {s : RamState} {secret msg : ByteArray} {d : Nat} {st : State}
    {m n : Ram} {regions : List MemoryRegion} (call : ValidCall signingKeyTrySign s [secret,msg])
    (before : LoopMemory s d msg st m) (writes : RamWriteFrame m n regions)
    (inside : RegionsWithin regions [Stack.region s signingKeyTrySign.minStackBytes])
    (apart : ∀ i ∈ protectedOffsets, Outside regions (sp s + BitVec.ofNat 64 i) 8)
    (hash : Outside regions (sp s+352) 32) (order : Outside regions (sp s+592) 32)
    (drbg : Outside regions (sp s+688) 72) : LoopMemory s d msg st n := by
  have base (i : Nat) (hi : i ≤ 1296) := offsetNat call hi
  have drbgNat : (sp s+688).toNat = (sp s).toNat+688 := base 688 (by decide)
  have keyNat : (sp s+696).toNat = (sp s).toNat+696 := base 696 (by decide)
  have valueNat : (sp s+728).toNat = (sp s).toNat+728 := base 728 (by decide)
  have pointer : Outside regions (sp s+688) 8 :=
    ⟨by have := drbg.1; omega, fun r hr => by rcases drbg.2 r hr with h | h <;> omega⟩
  have key : Outside regions (sp s+696) 32 := by
    refine ⟨?_,fun r hr => ?_⟩
    · rw [keyNat]; have h := drbg.1; rw [drbgNat] at h; omega
    · rw [keyNat]; have h := drbg.2 r hr; rw [drbgNat] at h
      rcases h with lower | upper <;> omega
  have value : Outside regions (sp s+728) 32 := by
    refine ⟨?_,fun r hr => ?_⟩
    · rw [valueNat]; have h := drbg.1; rw [drbgNat] at h; omega
    · rw [valueNat]; have h := drbg.2 r hr; rw [drbgNat] at h
      rcases h with lower | upper <;> omega
  refine ⟨before.toCoreMemory.preserve writes inside apart, hasBytes_of_frame writes hash before.hash,
    WordsAt.of_frame before.order writes (by decide) order, (writes.memLoad_eq pointer).trans before.orderPtr,
    hasBytes_of_frame writes key before.state.key, ?_⟩
  have addr : (sp s+728).toNat = (sp s+696).toNat + 32 := by rw [valueNat,keyNat]
  have previous := before.state.value
  rw [← addr] at previous ⊢
  exact hasBytes_of_frame writes value previous

theorem LoopMemory.preserve_work {s : RamState} {secret msg : ByteArray} {d : Nat} {st : State}
    {m n : Ram} (call : ValidCall signingKeyTrySign s [secret,msg])
    (before : LoopMemory s d msg st m) (writes : RamWriteFrame m n (workRegions s)) :
    LoopMemory s d msg st n := by
  obtain ⟨room,high,base⟩ := stackBounds call
  have lower : (sp s-9904).toNat = (sp s).toNat-9904 := belowNat call (by decide)
  have atOffset (i : Nat) (ok : i ≤ 1296) := offsetNat call ok
  have span : Stack.region s signingKeyTrySign.minStackBytes = ⟨(sp s-9904).toNat,11200⟩ := by
    rw [stackRegion call]
    have addr : sp s-9904 = stackPtr s-11192 := by unfold sp; bv_omega
    rw [addr]
  have a384 : (sp s+384).toNat = (sp s).toNat+384 := atOffset 384 (by decide)
  have a424 : (sp s+424).toNat = (sp s).toNat+424 := atOffset 424 (by decide)
  have a624 : (sp s+624).toNat = (sp s).toNat+624 := atOffset 624 (by decide)
  have apart {offset length : Nat} (inside : offset+length ≤ 1296)
      (a : 344 ≤ offset) (b : offset+length ≤ 384 ∨ 416 ≤ offset)
      (c : offset+length ≤ 424 ∨ 592 ≤ offset) (d : offset+length ≤ 624 ∨ 688 ≤ offset) :
      Outside (workRegions s) (sp s+BitVec.ofNat 64 offset) length := by
    simp only [Outside,workRegions,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,
      lower,a384,a424,a624,atOffset offset (by omega)]
    refine ⟨by omega,Or.inr (by omega),?_,?_,?_⟩
    · rcases b with h | h <;> omega
    · rcases c with h | h <;> omega
    · rcases d with h | h <;> omega
  apply before.preserve call writes
  · rw [span]
    intro r member
    refine ⟨_,List.mem_singleton_self _,?_⟩
    simp only [workRegions,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl <;>
      simp only [lower,a384,a424,a624] <;> constructor <;> omega
  · intro i member
    apply apart <;> simp only [protectedOffsets,List.mem_cons,List.not_mem_nil,or_false] at member <;> omega
  · exact apart (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact apart (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact apart (by decide) (by decide) (by decide) (by decide) (by decide)

end K256.Proofs.Signing.Composition.Attempt
