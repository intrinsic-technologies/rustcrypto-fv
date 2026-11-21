import K256.Proofs.Signing.Composition.State
import K256.Proofs.Common.CallMemory
import K256.Proofs.Generate.Generator.Affine.Invert.Core.Callee

namespace K256.Proofs.Signing.Composition

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs CFG Lift Refine

theorem stackBounds {s : RamState} {secret msg : ByteArray}
    (call : ValidCall signingKeyTrySign s [secret,msg]) :
    11192 ≤ (stackPtr s).toNat ∧ (stackPtr s).toNat + 8 < 2^32 ∧
    (sp s).toNat = (stackPtr s).toNat - 1288 := by
  have room : 11192 ≤ (stackPtr s).toNat := call.stackAvailable.2.2.1
  have bound := call.stackAvailable.1
  change (stackPtr s).toNat - 11192 + ((stackPtr s).toNat+8 - ((stackPtr s).toNat-11192)) < 2^32 at bound
  exact ⟨room,by omega,Common.stackOffset (off := 1288) call.stackAvailable (by decide)⟩

theorem stackRegion {s : RamState} {secret msg : ByteArray}
    (call : ValidCall signingKeyTrySign s [secret,msg]) :
    Stack.region s signingKeyTrySign.minStackBytes = ⟨(stackPtr s-11192).toNat,11200⟩ := by
  have room := (stackBounds call).1
  have addr := Common.stackOffset (off := 11192) call.stackAvailable (by decide)
  change (⟨(stackPtr s).toNat-11192, (stackPtr s).toNat+8-((stackPtr s).toNat-11192)⟩ : MemoryRegion) = _
  change (stackPtr s - 11192).toNat = (stackPtr s).toNat - 11192 at addr
  rw [addr, show (stackPtr s).toNat+8-((stackPtr s).toNat-11192) = 11200 by omega]

theorem Memory.window {s : RamState} {secret msg : ByteArray} {m : Ram}
    (memory : Memory s m) (call : ValidCall signingKeyTrySign s [secret,msg]) :
    Writable Extracted.programImage m (stackPtr s - 11192) 11200 :=
  (Common.stackWritable (off := 11192) call (by decide) (by decide) (by decide)).of_frame memory.written

theorem Memory.image {s : RamState} {secret msg : ByteArray} {m : Ram}
    (memory : Memory s m) (call : ValidCall signingKeyTrySign s [secret,msg]) :
    ∀ b ∈ Extracted.programImage, m[b.1]? = some b.2 := by
  have saved := memory.written
  rw [stackRegion call] at saved
  exact Generate.Generator.Affine.Invert.Core.stackImage
    (Common.stackWritable (off := 11192) call (by decide) (by decide) (by decide)) saved
    (fun b hb => call.programLoaded _ _ (Common.programSections_fetchByte_of_mem hb))

def protectedOffsets : List Nat :=
  [344,416,760,776,800,808,1016,1024,1032,1040,1256,1264,1272,1280,1288]

theorem CoreMemory.preserve {s : RamState} {d : Nat} {m n : Ram} {regions : List MemoryRegion}
    (before : CoreMemory s d m) (writes : RamWriteFrame m n regions)
    (inside : RegionsWithin regions [Stack.region s signingKeyTrySign.minStackBytes])
    (apart : ∀ i ∈ protectedOffsets, Outside regions (sp s + BitVec.ofNat 64 i) 8) :
    CoreMemory s d n := by
  have keep (i : Nat) (hi : i ∈ protectedOffsets) :
      memLoad n (sp s + BitVec.ofNat 64 i) 64 = memLoad m (sp s + BitVec.ofNat 64 i) 64 :=
    writes.memLoad_eq (apart i hi)
  have top (off i : Nat) (eq : off+i=1288) (hi : i ∈ protectedOffsets) :
      memLoad n (stackPtr s - BitVec.ofNat 64 off) 64 =
      memLoad m (stackPtr s - BitVec.ofNat 64 off) 64 := by
    have addr : stackPtr s - BitVec.ofNat 64 off = sp s + BitVec.ofNat 64 i := by
      unfold sp
      rw [show (1288 : BitVec 64) = BitVec.ofNat 64 (off+i) by rw [eq]; rfl]
      change stackPtr s - BitVec.ofNat 64 off =
        stackPtr s - BitVec.ofNat 64 (off+i) + BitVec.ofNat 64 i
      rw [BitVec.ofNat_add]
      bv_omega
    rw [addr]
    exact keep i hi
  refine ⟨⟨⟨before.written.trans writes inside,?_,?_,?_,?_,?_⟩,?_,?_⟩,?_,?_,?_,?_,?_⟩
  · exact (by simpa only [BitVec.ofNat_eq_ofNat,BitVec.sub_zero] using top 0 1288 rfl (by decide) :
      memLoad n (stackPtr s) 64 = memLoad m (stackPtr s) 64).trans before.ret
  · exact (top 32 1256 rfl (by decide)).trans before.savedWrapperRBX
  · exact (top 24 1264 rfl (by decide)).trans before.savedWrapperR12
  · exact (top 16 1272 rfl (by decide)).trans before.savedWrapperR14
  · exact (top 8 1280 rfl (by decide)).trans before.savedWrapperR15
  · intro i hi
    refine Eq.trans ?_ (before.key i hi)
    obtain rfl | rfl | rfl | rfl := show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega
    all_goals simp only [wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.ofNat_eq_ofNat,
      BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero]
    · exact keep 1016 (by decide)
    · exact keep 1024 (by decide)
    · exact keep 1032 (by decide)
    · exact keep 1040 (by decide)
  · exact (keep 808 (by decide)).trans before.coreReturn
  · exact (keep 344 (by decide)).trans before.keyPtr
  · exact (keep 416 (by decide)).trans before.resultPtr
  · exact (keep 760 (by decide)).trans before.savedOutput
  · exact (keep 776 (by decide)).trans before.savedR13
  · exact (keep 800 (by decide)).trans before.savedRbp

end K256.Proofs.Signing.Composition
