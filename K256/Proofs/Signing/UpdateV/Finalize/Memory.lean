import K256.Proofs.Signing.UpdateV.Finalize.State
import K256.Proofs.Sec1.Tactic.Lemma.Refine
import K256.Proofs.Generate.Generator.Affine.Invert.Core.Callee

namespace K256.Proofs.Signing.UpdateV.Finalize

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.Hash

theorem outsideOffset {rs : List MemoryRegion} {p : BitVec 64} {len : Nat}
    (out : Outside rs p len) (off : BitVec 64) (n : Nat) (pos : n > 0)
    (fits : off.toNat + n ≤ len) : Outside rs (p + off) n := by
  have bound := out.1
  have addr : (p + off).toNat = p.toNat + off.toNat := by
    rw [BitVec.toNat_add,Nat.mod_eq_of_lt (by omega)]
  exact ⟨by omega,fun r hr => by rcases out.2 r hr with _|_ <;> omega⟩

theorem bytesAfter {m t : Ram} {rs : List MemoryRegion} {p : BitVec 64} {n : Nat} {bs : ByteArray}
    (writes : RamWriteFrame m t rs) (out : Outside rs p n)
    (bytes : (⟨p.toNat,n⟩ : MemoryRegion).HasBytes m bs) :
    (⟨p.toNat,n⟩ : MemoryRegion).HasBytes t bs := by
  refine ⟨bytes.1,fun i => ?_⟩
  have fits : i.val < n := by have h : bs.size = n := bytes.1; omega
  have h := writes.outside _ (outsideOffset out (BitVec.ofNat 64 i.val) 1 (by decide)
    (by have := Nat.mod_le i.val (2^64); simpa only [BitVec.toNat_ofNat] using
          (show i.val % 2^64 + 1 ≤ n by omega)))
  simpa only [BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq] using
    h.trans (by simpa only [BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq] using bytes.2 i)

theorem stateAfter {m t : Ram} {rs : List MemoryRegion} {p : BitVec 64} {hash : Array UInt32}
    (writes : RamWriteFrame m t rs) (out : Outside rs p 32) (state : Compression.StateAt m p hash) :
    Compression.StateAt t p hash := ⟨state.1,state.2.of_frame writes (by decide) out⟩

theorem hmacAfter {m t : Ram} {rs : List MemoryRegion} {p : BitVec 64} {key input : ByteArray}
    (writes : RamWriteFrame m t rs) (out : Outside rs p 168) (state : HmacStateAt m p key input) :
    HmacStateAt t p key input := by
  have prefixOutside (n : Nat) (hn : n ≤ 168) : Outside rs p n :=
    ⟨by have := out.1; omega, fun r hr => by rcases out.2 r hr with _|_ <;> omega⟩
  have buf : Outside rs (p+64) (input.size % 64) := by
    have h := outsideOffset out 64 64 (by decide) (by decide)
    exact ⟨by have := h.1; omega, fun r hr => by rcases h.2 r hr with _|_ <;> omega⟩
  exact ⟨bytesAfter writes (prefixOutside 64 (by decide)) state.outer,bytesAfter writes buf state.buffer,
    (writes.memLoad_eq (outsideOffset out 127 1 (by decide) (by decide))).trans state.used,
    stateAfter writes (outsideOffset out 128 32 (by decide) (by decide)) state.hash,
    (writes.memLoad_eq (outsideOffset out 160 8 (by decide) (by decide))).trans state.count⟩

theorem innerBuffered {m : Ram} {src : BitVec 64} {key input : ByteArray}
    (state : HmacStateAt m src key input) :
    Buffered m (src + 64) (keyPad key 0x36 ++ input) := by
  have remEq : (keyPad key 0x36 ++ input).size % 64 = input.size % 64 := by
    rw [ByteArray.size_append,keyPad_size]; omega
  have countEq : (keyPad key 0x36 ++ input).size / 64 = 1 + input.size / 64 := by
    rw [ByteArray.size_append,keyPad_size]; omega
  constructor
  · simpa only [remEq] using state.buffer
  · simpa only [BitVec.add_assoc,BitVec.ofNat_eq_ofNat,BitVec.reduceAdd,remEq] using state.used
  · simpa only [BitVec.add_assoc,BitVec.ofNat_eq_ofNat,BitVec.reduceAdd] using state.hash
  · simpa only [BitVec.add_assoc,BitVec.ofNat_eq_ofNat,BitVec.reduceAdd,countEq] using state.count

end K256.Proofs.Signing.UpdateV.Finalize
