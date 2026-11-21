import K256.Proofs.Signing.Nonce.Fill.State
import K256.Proofs.Verify.LIR.Fn100a40
import K256.Proofs.Verify.Core.Affine.Call
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Signing.Nonce.Fill

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Verify.LIR
open Verify.Core (Registers Reaches)


set_option maxHeartbeats 750000 in
theorem orderScanBlock {a : Registers} {m : Ram} {base gen order : BitVec 64}
    (rsp : a[4].get 64 = base)
    (stack : Writable Extracted.programImage m base 152)
    (genRead : Readable m gen 8) (orderRead : Readable m order 32)
    (genSlot : memLoad m (base + 144) 64 = gen)
    (orderSlot : memLoad m gen 64 = order)
    (bits : memLoad m (base + 56) 32 = 256)
    (w0 : memLoad m order 64 = 0xbfd25e8cd0364141)
    (w1 : memLoad m (order + 8) 64 = 0xbaaedce6af48a03b)
    (w2 : memLoad m (order + 16) 64 = 0xfffffffffffffffe)
    (w3 : memLoad m (order + 24) 64 = 0xffffffffffffffff)
    (separated : Outside [⟨(base + 8).toNat,1⟩] order 32) :
    ∃ (b : Registers) (n : Ram), program.runBlock (dialect Extracted.programImage) ⟨.l100afb,a,m⟩ =
      .jump ⟨.l100bf0,b,n⟩ ∧ RamWriteFrame m n [⟨(base + 8).toNat,1⟩] ∧
      b[4] = a[4] ∧ b[12] = ⟨64,base+8⟩ ∧ b[14] = ⟨64,0⟩ ∧ b[15] = ⟨64,order⟩ ∧
      b[8] = ⟨64,256⟩ ∧ b[9] = ⟨64,0⟩ ∧
      b[3] = a[3] ∧ b[5] = a[5] ∧ b[22] = a[22] ∧ b[39] = a[39] ∧
      b[50] = a[50] ∧ b[51] = a[51] := by
  have lim := stack.readable.low
  have z0 : BitVec.ofNat 64 (highestSetBit 0xbfd25e8cd0364141#64) = 63 := by decide +kernel
  have z1 : BitVec.ofNat 64 (highestSetBit 0xbaaedce6af48a03b#64) = 63 := by decide +kernel
  have z2 : BitVec.ofNat 64 (highestSetBit 0xfffffffffffffffe#64) = 63 := by decide +kernel
  have z3 : BitVec.ofNat 64 (highestSetBit 0xffffffffffffffff#64) = 63 := by decide +kernel
  have rd (t : Ram) (x : BitVec 8) : memLoad (memStore t (base + 8) x) (base+8) 8 = x :=
    memLoad_memStore_same _ _ _ (by decide) (by decide)
  have keepOrder (x : BitVec 8) (t : Ram) (k : BitVec 64) (hk : k.toNat ≤ 24) :
      memLoad (memStore t (base+8) x) (order+k) 64 = memLoad t (order+k) 64 := by
    apply memLoad_memStore_of_rangeApart
    have orderBound := separated.1
    have base8 : (base + 8).toNat = base.toNat + 8 := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by change base.toNat + 8 < 2^64; omega)]
      rfl
    have offset : (order + k).toNat = order.toNat + k.toNat := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
    have ap := separated.2 _ (List.mem_singleton_self _)
    change order.toNat + 32 ≤ (base + 8).toNat ∨ (base + 8).toNat + 1 ≤ order.toNat at ap
    apply RangeApart.of_toNat
    · change (base+8).toNat + 1 ≤ 2^64
      omega
    · change (order+k).toNat + 8 ≤ 2^64
      omega
    · change (base+8).toNat + 1 ≤ (order+k).toNat ∨ (order+k).toNat + 8 ≤ (base+8).toNat
      omega
  have keepZero (x : BitVec 8) (t : Ram) :
      memLoad (memStore t (base + 8) x) order 64 = memLoad t order 64 := by
    have h := keepOrder x t 0 (by decide)
    rw [show order + (0 : BitVec 64) = order by bv_omega] at h
    exact h
  have keepBits (x : BitVec 8) (t : Ram) :
      memLoad (memStore t (base + 8) x) (base + 56) 32 = memLoad t (base + 56) 32 := by
    apply memLoad_memStore_of_rangeApart
    apply RangeApart.of_diff
    rw [show base + 8 - (base + 56) = -48 by bv_omega,
      show base + 56 - (base + 8) = 48 by bv_omega]
    decide
  refine ⟨?_, ?_, ?step, ?post⟩
  case step =>
    cfg_eval [rsp,genSlot,orderSlot,rd,w3,w2,w1,w0,z0,z1,z2,z3,bits,
      keepOrder,keepZero,keepBits,BitVec.add_zero]
    segment_words [genSlot,orderSlot,rd,w3,w2,w1,w0,z0,z1,z2,z3,bits]
    simp +decide only [keepZero, w0]
    have code : ∀ x ∈ codeRange 0x100afb bytes_l100afb, x ∈ Extracted.programImage :=
      fun x hx => Verify.Core.Affine.coreText x (code_l100afb x hx)
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code)
    rfl
  case post =>
    refine ⟨?_,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
    · have here : InRegions [⟨(base+8).toNat,1⟩] (base+8) 1 := by
        refine ⟨_, List.mem_singleton_self _, Nat.le_refl _, Nat.le_refl _, ?_⟩
        have h := (base+8).isLt
        omega
      repeat' apply RamWriteFrame.memStore _ _ here
      exact RamWriteFrame.refl _ _

end K256.Proofs.Signing.Nonce.Fill
