import Sha1.Proofs.Compress.Machine.Interface
import X86Proofs.Program.Compose
import X86Proofs.Program.ReadWrite.Bytes

namespace Sha1.Proofs.Compress.Machine

open Prelude X86 X86.Machine X86.UserProcess X86Proofs

 theorem memReadable_slice {s : RamState} {address : BitVec 64} {length : Nat}
    (h : MemReadable s address length) (offset count : Nat) (hle : offset + count ≤ length) :
    MemReadable s (address + BitVec.ofNat 64 offset) count := by
  refine ⟨?_, ?_⟩
  · have h64 : address.toNat + offset < 2 ^ 64 := by have := h.low; omega
    rw [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show offset < 2 ^ 64 by omega), Nat.mod_eq_of_lt h64]
    have := h.low
    omega
  · intro i hi
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact h.mem (offset + i) (by omega)

 theorem memoryWritable_slice {s : RamState} {address : BitVec 64} {length : Nat}
    (h : MemWritable s address length) (offset count : Nat)
    (hle : offset + count ≤ length) :
    MemWritable s (address + BitVec.ofNat 64 offset) count := by
  have hr := memReadable_slice h.readable offset count hle
  refine ⟨hr.low, hr.mem, ?_⟩
  intro i hi
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact h.tables (offset + i) (by omega)

 theorem memWritable_of_holds {e : Effect} {s t : RamState} {a : BitVec 64} {len : Nat}
    (h : e.Holds s t) (hm : MemWritable s a len) : MemWritable t a len :=
  ⟨hm.low, fun i hi ↦ h.agrees.grow _ (hm.mem i hi), hm.tables⟩

 theorem storePre_of_holds {e : Effect} {s t : RamState} (h : e.Holds s t)
    (ho : Obs (e.after s true) t) {p : BitVec 64} {codeLen : Nat}
    {addr : RamState → BitVec 64} {len : Nat} (hrip : e.rip = p)
    (ha : AddrObs addr) (hw : MemWritable s (addr (e.after s true)) len)
    (hap : RangeApart (addr (e.after s true)) len p codeLen) :
    Sha1.Proofs.Common.Instructions.StorePre.StorePre p codeLen addr len t :=
  ⟨h.rip_of hrip, by rw [ha.eq ho]; exact memWritable_of_holds h hw,
    RangeApart.carry ho ha hap⟩

theorem storedByte_extractLsb'_of_lt {n width : Nat} (v : BitVec n) (offset i : Nat)
    (hi : 8 * (i + 1) ≤ width) :
    storedByte (v.extractLsb' (8 * offset) width) i = storedByte v (offset + i) := by
  apply UInt8.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [storedByte_eq_extract, UInt8.toBitVec_ofBitVec, BitVec.getLsbD_extractLsb']
  simp [show k < 8 by omega, show 8 * i + k < width by omega, Nat.mul_add, Nat.add_assoc]

theorem memLoad_extractLsb' (m : Ram) (base : BitVec 64) (n width offset : Nat)
    (hw : width % 8 = 0) (hspan : offset + width / 8 ≤ n / 8) :
    memLoad m (base + BitVec.ofNat 64 offset) width =
      (memLoad m base n).extractLsb' (8 * offset) width := by
  apply storedByte_injective hw
  intro i hi
  rw [storedByte_memLoad m _ i hi,
    storedByte_extractLsb'_of_lt _ _ _ (by omega),
    storedByte_memLoad m base (offset + i) (by omega),
    BitVec.add_assoc, ← BitVec.ofNat_add]

theorem memLoad_low32 (m : Ram) (a : BitVec 64) :
    (memLoad m a 64).setWidth 32 = memLoad m a 32 := by
  simpa only [Nat.mul_zero, BitVec.add_zero,
    ← BitVec.setWidth_eq_extractLsb' (by decide : 32 ≤ 64)] using
    (memLoad_extractLsb' m a 64 32 0 (by decide) (by decide)).symm

theorem read32_memStore64_low (m : Ram) (a : BitVec 64) (v : BitVec 64) :
    memLoad (memStore m a v) a 32 = v.extractLsb' 0 32 := by
  simpa only [BitVec.add_zero] using
    (memLoad_extractLsb' (memStore m a v) a 64 32 0 (by decide) (by decide)).trans
      (congrArg (fun w : BitVec 64 ↦ w.extractLsb' 0 32)
        (memLoad_memStore m a (by decide) (by decide) v))

theorem read32_memStore64_high (m : Ram) (a : BitVec 64) (v : BitVec 64) :
    memLoad (memStore m a v) (a + 4) 32 = v.extractLsb' 32 32 := by
  exact (memLoad_extractLsb' (memStore m a v) a 64 32 4 (by decide) (by decide)).trans
    (congrArg (fun w : BitVec 64 ↦ w.extractLsb' 32 32)
      (memLoad_memStore m a (by decide) (by decide) v))

theorem read32_of_read64_low {s : RamState} {a : BitVec 64} {v : BitVec 64}
    (h : (Operand.mem a : Operand 64).read s = v) :
    (Operand.mem a : Operand 32).read s = v.setWidth 32 := by
  have he := memLoad_extractLsb' s.external a 64 32 0 (by decide) (by decide)
  change memLoad s.external a 64 = v at h
  rw [h] at he
  simp only [BitVec.add_zero] at he
  refine he.trans ?_
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp [hk]

theorem read32_of_read64_high {s : RamState} {a : BitVec 64} {v : BitVec 64}
    (h : (Operand.mem a : Operand 64).read s = v) :
    (Operand.mem (a + 4) : Operand 32).read s = (v >>> 32).setWidth 32 := by
  have he := memLoad_extractLsb' s.external a 64 32 4 (by decide) (by decide)
  change memLoad s.external a 64 = v at h
  rw [h] at he
  refine he.trans ?_
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp [BitVec.getLsbD_ushiftRight, hk, Nat.add_comm]

theorem bswap32_bswap32 (x : BitVec 32) : bswapSpec (bswapSpec x) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hmod : i % 8 < 8 := Nat.mod_lt _ (by decide)
  have hdiv : i / 8 < 4 := by omega
  simp only [bswapSpec]
  rw [getLsbD_ofLanes _ i hi, ite_eq_left (by omega), lane_ofLanes _ _ (by omega)]
  simp only [lane, BitVec.getLsbD_extractLsb', hmod, decide_true, Bool.true_and]
  congr 1
  omega

end Sha1.Proofs.Compress.Machine
