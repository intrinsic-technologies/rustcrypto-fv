import Sha3.Proofs.Permutation.LoadStore.Store.Basic

namespace Sha3.Proofs.Permutation.Store

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

theorem readable_offset {s : RamState} {a c : BitVec 64} {total len : Nat}
    (h : MemReadable s a total) (hc : c.toNat + len ≤ total) :
    MemReadable s (a + c) len := by
  refine ⟨?_, ?_⟩
  · simp only [BitVec.toNat_add]
    have := h.low
    omega
  · intro i hi
    have hm := h.mem (c.toNat + i) (by omega)
    simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, ← BitVec.add_assoc] using hm

theorem apart_offset {a b c d : BitVec 64} {m n k l : Nat}
    (h : RangeApart a m b n) (hc : c.toNat + k ≤ m) (hd : d.toNat + l ≤ n) :
    RangeApart (a + c) k (b + d) l := by
  intro i hi j hj
  have hn := h (c.toNat + i) (by omega) (d.toNat + j) (by omega)
  simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, ← BitVec.add_assoc] using hn

theorem tables_offset {pointer c : BitVec 64}
    (h : ∀ i, i < 200 → ¬ InPageTables (pointer + BitVec.ofNat 64 i))
    (hc : c.toNat + 8 ≤ 200) :
    ∀ i, i < 8 → ¬ InPageTables (pointer + (c + BitVec.ofNat 64 i)) := by
  intro i hi
  have ht := h (c.toNat + i) (by omega)
  simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using ht

theorem codeApart_offset {copy : Copy} {pointer c : BitVec 64}
    (h : RangeApart pointer 200 (storeAddress copy) bytes.length) (hc : c.toNat + 8 ≤ 200) :
    RangeApart (pointer + c) 8 (storeAddress copy) bytes.length := by
  intro i hi j hj
  have hn := h (c.toNat + i) (by omega) j hj
  simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
    ← BitVec.add_assoc] using hn

theorem mov_register_step [Bindings] (p : BitVec 64) (dst src : BitVec 4) :
    StepEffect (fun s ↦ s.RIP = p) (codeRange p (encodeMovR64R64 dst src))
      (movR64R64Effect p (dst.setWidth 5) (src.setWidth 5)) := by
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩ := encodeMovR64R64_spec dst src
  rw [hbytes, ← hdst, ← hsrc]
  exact mov_r64_r64_effect_step p rex modrm hrex hmod

theorem mov_load_step [Bindings] (p : BitVec 64) (dst : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    StepEffect (LoadPre p (fun s ↦ am.addr s (p + BitVec.ofNat 64 (movLoadLen am))) 8)
      (codeRange p (encodeMovR64M64 dst am)) (movR64M64Effect p (dst.setWidth 5) am) := by
  obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_true_spec dst
  have h := mov_r64_m64_effect_step p _ hrex (regLow dst) am hv hx hb
  rwa [hr, gprNumber_reg] at h

end Sha3.Proofs.Permutation.Store
