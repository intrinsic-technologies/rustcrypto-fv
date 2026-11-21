import K256.Proofs.Signing.UpdateV.Finalize.Padding.State
import K256.Proofs.Signing.UpdateV.Copy

namespace K256.Proofs.Signing.UpdateV.Finalize

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  K256.Proofs.Verify.Hash

abbrev copyInput (outer : Bool) (m : Ram) (sp : BitVec 64) :=
  if outer then m else memStore m (sp+271) (0 : BitVec 8)

abbrev copyMemory (outer : Bool) (m : Ram) (sp src : BitVec 64) :=
  memCopy (copyInput outer m sp) (sp+8) src 104

private theorem Buffered.copy {m : Ram} {src dst : BitVec 64} {msg : ByteArray}
    (state : Buffered m src msg) : Buffered (memCopy m dst src 104) dst msg := by
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [BitVec.add_zero] using hasBytes_memCopy_offset (src := src) (dst := dst)
      (off := 0) (by decide : 104 ≤ 2^64) (by have := Nat.mod_lt msg.size (by decide : 0 < 64); omega)
      (by simpa only [BitVec.add_zero] using state.bytes)
  · exact (Sec1.Parser.Result.memLoad_memCopy (off := 63) m dst src (by decide : 104 ≤ 2^64)
      (by decide : 63 + 8/8 ≤ 104)).trans state.used
  · exact stateAt_memCopy_offset (off := 64) (by decide) (by decide) state.hash
  · exact (Sec1.Parser.Result.memLoad_memCopy (off := 96) m dst src (by decide : 104 ≤ 2^64)
      (by decide : 96 + 64/8 ≤ 104)).trans state.count

theorem copyBuffered (outer : Bool) {m : Ram} {sp src : BitVec 64} {msg : ByteArray}
    (depth : 344 ≤ sp.toNat) (limit : sp.toNat + 312 < 2^32)
    (read : Readable m src 104) (above : sp.toNat + (if outer then 208 else 312) ≤ src.toNat)
    (state : Buffered m src msg) :
    Buffered (copyMemory outer m sp src) (sp+8) msg ∧
    RamWriteFrame m (copyMemory outer m sp src) [paddingRegion sp,⟨(sp+271).toNat,1⟩] ∧
    (outer = false → memLoad (copyMemory outer m sp src) (sp+271) 8 = 0) := by
  have flagPos : (sp+271).toNat = sp.toNat+271 := toNat_add_ofNat sp 271 (by omega)
  have dstPos : (sp+8).toNat = sp.toNat+8 := toNat_add_ofNat sp 8 (by omega)
  let flag : MemoryRegion := ⟨(sp+271).toNat,1⟩
  have reset : RamWriteFrame m (copyInput outer m sp) [flag] := by
    cases outer
    · exact (RamWriteFrame.refl _ _).memStore _ ⟨_, List.mem_cons_self, Nat.le_refl _, Nat.le_refl _, by omega⟩
    · exact .refl _ _
  have input : Buffered (copyInput outer m sp) src msg := by
    cases outer
    case true => exact state
    case false =>
      have low := read.low
      have bound : sp.toNat+312 ≤ src.toNat := above
      have outside (p : BitVec 64) (k : Nat) (lo : src.toNat ≤ p.toNat)
          (hi : p.toNat + k ≤ src.toNat + 104) : Outside [flag] p k := by
        refine ⟨by omega, fun r hr => Or.inr ?_⟩
        obtain rfl := List.mem_singleton.mp hr
        change (sp+271).toNat + 1 ≤ _
        omega
      have pos (i : Nat) (hi : i ≤ 104) : (src+BitVec.ofNat 64 i).toNat = src.toNat+i :=
        toNat_add_ofNat src i (by omega)
      refine ⟨⟨state.bytes.1,fun i => ?_⟩, (reset.memLoad_eq ?_).trans state.used,
        ⟨state.hash.1,fun i hi => (reset.memLoad_eq ?_).trans (state.hash.2 i hi)⟩,
        (reset.memLoad_eq ?_).trans state.count⟩
      · apply Eq.trans (reset.outside _ ?_) (state.bytes.2 i)
        change Outside [flag] (BitVec.ofNat 64 (src.toNat+i.val)) 1
        rw [ofNat_toNat_add]
        have hi := i.isLt
        have := remainderBytes_size msg
        have h := pos i.val (by omega)
        exact outside _ _ (by omega) (by omega)
      · have h : (src+63).toNat = src.toNat+63 := pos 63 (by decide)
        exact outside _ _ (by omega) (by omega)
      · have h := pos (64+4*i) (by omega)
        change Outside [flag] ((src+64)+BitVec.ofNat 64 (4*i)) 4
        rw [BitVec.ofNat_add, ← BitVec.add_assoc] at h
        change ((src+64)+BitVec.ofNat 64 (4*i)).toNat = src.toNat + (64+4*i) at h
        exact outside _ _ (by omega) (by omega)
      · have h : (src+96).toNat = src.toNat+96 := pos 96 (by decide)
        exact outside _ _ (by omega) (by omega)
  have writes : RamWriteFrame (copyInput outer m sp) (copyMemory outer m sp src) [paddingRegion sp] :=
    Sec1.Wrapper.Copy.memCopy_frame (.refl _ _) ⟨_,List.mem_cons_self,
      by change sp.toNat-344 ≤ _; omega, by change _ ≤ sp.toNat-344+520; omega, by omega⟩
  have resetWide : RamWriteFrame m (copyInput outer m sp) [paddingRegion sp,flag] :=
    (RamWriteFrame.refl _ _).trans reset (by
      intro r hr; obtain rfl := List.mem_singleton.mp hr
      exact ⟨_,List.mem_cons_of_mem _ List.mem_cons_self,Nat.le_refl _,Nat.le_refl _⟩)
  refine ⟨input.copy, resetWide.trans writes ?_, ?_⟩
  · intro r hr; obtain rfl := List.mem_singleton.mp hr
    exact ⟨_,List.mem_cons_self,Nat.le_refl _,Nat.le_refl _⟩
  · rintro rfl
    apply Eq.trans (writes.memLoad_eq ?_) (memLoad_memStore_same _ _ _ (by decide) (by decide))
    refine ⟨by omega,fun r hr => Or.inr ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    change sp.toNat-344+520 ≤ _
    omega

end K256.Proofs.Signing.UpdateV.Finalize
