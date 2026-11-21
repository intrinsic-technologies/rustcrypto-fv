import Sha2.Proofs.Common.SHA256.Absorb.Table

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Instances.Absorption

open Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.SHA256.Absorb

theorem d32_value_ofNat (n : Nat) (h : n < 2 ^ 31) :
    (Disp.d32 n).value = BitVec.ofNat 64 n := by
  change (BitVec.ofNat 32 n).signExtend 64 = BitVec.ofNat 64 n
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  by_cases hi32 : i < 32
  · have hnmod : n % 2^32 = n := Nat.mod_eq_of_lt (by omega)
    simp [BitVec.getLsbD_signExtend, hi32, BitVec.getLsbD_ofNat,
      BitVec.getElem_eq_testBit_toNat, hnmod]
  · have hn32 : n < 2^32 := by omega
    have hmsb : (BitVec.ofNat 32 n).msb = false := by
      rw [← BitVec.ofNatLT_eq_ofNat hn32]
      change (BitVec.ofNatLT n hn32).getMsbD 0 = false
      rw [BitVec.getMsbD_ofNatLT]
      simp only [Nat.sub_zero]
      exact Nat.testBit_lt_two_pow h
    have hpow : 2^31 ≤ 2^i := Nat.pow_le_pow_right (by decide) (by omega)
    have hni : n < 2^i := Nat.lt_of_lt_of_le h hpow
    have hbit : n.testBit i = false := Nat.testBit_lt_two_pow hni
    simp [BitVec.getLsbD_signExtend, hi32, BitVec.getLsbD_ofNat,
      hmsb, hbit]

theorem d8_value_ofNat (n : Nat) (h : n < 128) :
    (Disp.d8 n).value = BitVec.ofNat 64 n := by
  change (BitVec.ofNat 8 n).signExtend 64 = BitVec.ofNat 64 n
  have hn : n < 256 := by omega
  have msb : (BitVec.ofNat 8 n).msb = false := by
    apply BitVec.msb_eq_false_iff_two_mul_lt.mpr
    simp only [BitVec.toNat_ofNat]
    omega
  rw [BitVec.signExtend_eq_setWidth_of_msb_false msb]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

set_option maxHeartbeats 1000000 in
theorem loadPair_pre_of_table {l : Table.Layout} {sp : BitVec 64} {s : RamState}
    {index source length : BitVec 4} (pre : Table.LoadPre l sp s)
    (indexEq : l.index = index)
    (pointerValid : (AddrMode.sib 4 none 0 (.d32 l.pointerSlot)).Valid)
    (lengthValid : (AddrMode.sib 4 none 0 (.d32 l.lengthSlot)).Valid)
    (indexValid : (AddrMode.sib 0 (some index) 3 .none).Valid)
    (pointerValue : (Disp.d32 l.pointerSlot).value = BitVec.ofNat 64 l.pointerSlot)
    (lengthValue : (Disp.d32 l.lengthSlot).value = BitVec.ofNat 64 l.lengthSlot)
    (distinct : [index, source, length, 0, 4].Pairwise (· ≠ ·)) :
    Blocks.Pre l.head (.loadPair index source length (.d32 l.pointerSlot) (.d32 l.lengthSlot)) s := by
  constructor
  · exact pre.rip
  · exact distinct
  · exact pointerValid
  · exact lengthValid
  · exact indexValid
  · change MemReadable s (stackPtr s + (Disp.d32 l.pointerSlot).value) 8
    rw [pointerValue, pre.rsp]
    exact pre.pointerSlot
  · change MemReadable s (stackPtr s + (Disp.d32 l.lengthSlot).value) 8
    rw [lengthValue, pre.rsp]
    exact pre.lengthSlot
  · change MemReadable s (memLoad s.external
      (stackPtr s + (Disp.d32 l.pointerSlot).value) 64 + (Blocks.readReg s index <<< 3)) 8
    rw [pointerValue, pre.rsp]
    simpa [indexEq] using pre.pointer
  · change MemReadable s (memLoad s.external
      (stackPtr s + (Disp.d32 l.lengthSlot).value) 64 + (Blocks.readReg s index <<< 3)) 8
    rw [lengthValue, pre.rsp]
    simpa [indexEq] using pre.length

theorem loadTail_pre_of_table {l : Table.Layout} {sp : BitVec 64} {s : RamState}
    (pre : Table.LoadPre l sp s) {p : BitVec 64} {tail : BitVec 4} {am : AddrMode}
    (rip : s.RIP = p) (valid : am.Valid)
    (address : am.addr s (p + BitVec.ofNat 64 (Blocks.bytes (.loadTail tail am)).length) =
      l.chunk.buffer sp + 63) :
    Blocks.Pre p (.loadTail tail am) s := by
  refine ⟨rip, valid, ?_⟩
  rw [address]
  exact Common.Memory.memReadable_sub pre.active.toMemReadable 63 1 (by decide)

end Sha2.Proofs.Common.SHA256.Instances.Absorption
