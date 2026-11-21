import K256.Proofs.Ecdh.LIR.Program
import K256.Proofs.ParseSignature.Memory

namespace K256.Proofs.Ecdh.Decode.Packing

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.Refine K256.Proofs.Lift

def window (sp : BitVec 64) : MemoryRegion := ⟨(sp - 8).toNat, 272⟩

theorem stackLoad {code : CodeMap} {mem : Ram} {sp off : BitVec 64} {n : Nat}
    (win : Writable code mem (sp - 8) 272) (h : (off - (0 - 8)).toNat + n ≤ 272) :
    LoadOk mem (sp + off) n :=
  LoadOk.of_offsets win.readable rfl (addr_sub _ _) h

theorem inputLoad {mem : Ram} {src off : BitVec 64} {n : Nat}
    (read : Readable mem src 33) (h : off.toNat + n ≤ 33) :
    LoadOk mem (src + off) n := by
  apply LoadOk.of_offsets (d := 0) read rfl (addr_self _)
  have eq : off - (0 : BitVec 64) = off := by bv_omega
  exact eq.symm ▸ h

theorem inputLoadBase {mem : Ram} {src : BitVec 64} {n : Nat}
    (read : Readable mem src 33) (h : n ≤ 33) : LoadOk mem src n :=
  LoadOk.of_region read (Nat.le_refl _) (by omega)

theorem stackStore {code : CodeMap} {mem : Ram} {sp off addr pc base : BitVec 64}
    {n len : Nat} {bytes : List UInt8}
    (win : Writable code mem (sp - 8) 272) (ha : addr = sp + off)
    (h : (off - (0 - 8)).toNat + n ≤ 272)
    (cover : ∀ x ∈ codeRange base bytes, x ∈ code)
    (inside : (pc - base).toNat + len ≤ bytes.length) :
    StoreOk code mem addr n pc len := by
  have hw := win.of_offsets ha (addr_sub _ _) h
  have hg := ParseSignature.storeOk_of_codeRange hw cover inside
  have e : base + BitVec.ofNat 64 (pc - base).toNat = pc := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    bv_omega
  rwa [e] at hg

theorem stackRange {code : CodeMap} {mem : Ram} {sp off addr : BitVec 64} {n : Nat}
    (win : Writable code mem (sp - 8) 272) (ha : addr = sp + off)
    (h : (off - (0 - 8)).toNat + n ≤ 272) :
    InRegions [window sp] addr n := by
  have low := win.readable.low
  have e := toNat_of_offsets ha (addr_sub sp 8) low h
  refine ⟨_, List.mem_singleton_self _, ?_⟩
  simp only [InRegion, window, e]
  omega

end K256.Proofs.Ecdh.Decode.Packing
