import K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.Prefix.Safety

namespace K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.Prefix

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

def WordAccess (m : Ram) (src dst used : BitVec 64) : Prop :=
  let m₁ := memStore m (dst+24) (memLoad m (src+24) 64)
  let m₂ := memStore m₁ (dst+16) (memLoad m (src+16) 64)
  let m₃ := memStore m₂ (dst+8) (memLoad m (src+8) 64)
  LoadOk m (src+24) 8 ∧ Writable Extracted.programImage m (dst+24) 8 ∧
  LoadOk m₁ (src+16) 8 ∧ memLoad m₁ (src+16) 64 = memLoad m (src+16) 64 ∧
  Writable Extracted.programImage m₁ (dst+16) 8 ∧ LoadOk m₂ src 8 ∧ LoadOk m₂ (src+8) 8 ∧
  memLoad m₂ src 64 = memLoad m src 64 ∧ memLoad m₂ (src+8) 64 = memLoad m (src+8) 64 ∧
  Writable Extracted.programImage m₂ (dst+8) 8 ∧ Writable Extracted.programImage m₃ dst 8 ∧
  Writable Extracted.programImage (UpdateV.Append.stored m dst src) used 1

theorem wordAccess {fr : Activation} {input : Input} {state : State} {l : Label}
    {a : Verify.Core.Registers} {m n : Ram} {rs : List MemoryRegion}
    (env : Environment fr input) (live : Live l fr a m state) (baseFrame : RamWriteFrame m n rs)
    (off : Nat) (bound : off+64 ≤ 664) :
    WordAccess n (fr.rdi+32) (sp fr+BitVec.ofNat 64 off) (sp fr+BitVec.ofNat 64 (off+63)) := by
  let src := fr.rdi + 32
  let dst := sp fr + BitVec.ofNat 64 off
  let footprint := area fr off (off+32)
  let m₁ := memStore n (dst+24) (memLoad n (src+24) 64)
  let m₂ := memStore m₁ (dst+16) (memLoad n (src+16) 64)
  let m₃ := memStore m₂ (dst+8) (memLoad n (src+8) 64)
  let read := valueReadable env live baseFrame
  have plus (i : Nat) : dst+BitVec.ofNat 64 i = sp fr + BitVec.ofNat 64 (off+i) := by
    rw [BitVec.ofNat_add, ← BitVec.add_assoc]
  have extend {t : Ram} (w : RamWriteFrame n t footprint) (i : Nat) (v : BitVec 64) (hi : i+8 ≤ 32) :
      RamWriteFrame n (memStore t (dst+BitVec.ofNat 64 i) v) footprint := by
    rw [plus]
    exact stackStore env w v (by omega) (by change off+i+8 ≤ off+32; omega) (by omega)
  have w₀ := RamWriteFrame.refl n footprint
  have w₁ : RamWriteFrame n m₁ footprint := extend w₀ 24 _ (by decide)
  have w₂ : RamWriteFrame n m₂ footprint := extend w₁ 16 _ (by decide)
  have w₃ : RamWriteFrame n m₃ footprint := extend w₂ 8 _ (by decide)
  have w₄ := storedFrame (off := off) env w₀ src (by omega) (by omega) (by omega)
  have write {t : Ram} (w : RamWriteFrame n t footprint) (i : Nat) (h : i+8 ≤ 32) :
      Writable Extracted.programImage t (dst+BitVec.ofNat 64 i) 8 := by
    rw [plus]
    exact (stackWritable env live baseFrame (off+i) 8 (by omega)).of_frame w
  have load {t : Ram} (w : RamWriteFrame n t footprint) (i : Nat) (h : i+8 ≤ 32) :
      LoadOk t (src + BitVec.ofNat 64 i) 8 := by
    have addr := Ecdh.Output.outputOffset read.low (i := i) (by omega)
    apply LoadOk.of_region (read.of_frame w)
    all_goals change _ ≤ _; dsimp only [src] at *; omega
  have eq {t : Ram} (w : RamWriteFrame n t footprint) (i : Nat) (h : i+8 ≤ 32) :
      memLoad t (src + BitVec.ofNat 64 i) 64 = memLoad n (src + BitVec.ofNat 64 i) 64 :=
    w.memLoad_eq (valueOutside env h (by omega) (by omega))
  exact ⟨load w₀ 24 (by decide),write w₀ 24 (by decide),load w₁ 16 (by decide),eq w₁ 16 (by decide),
    write w₁ 16 (by decide),by simpa only [BitVec.add_zero] using load w₂ 0 (by decide),
    load w₂ 8 (by decide),by simpa only [BitVec.add_zero] using eq w₂ 0 (by decide),
    eq w₂ 8 (by decide),write w₂ 8 (by decide),by simpa only [BitVec.add_zero] using write w₃ 0 (by decide),
    (stackWritable env live baseFrame (off+63) 1 (by omega)).of_frame w₄⟩

end K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.Prefix
