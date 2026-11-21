import AesGcm.Proofs.Machine.Runtime.Preservation
namespace AesGcm.Proofs.Machine.Runtime
open Prelude X86 X86.Machine X86Proofs X86Proofs.Refine

theorem stack_sub_toNat (fr : Activation) {window n : Nat}
    (hroom : fr.low.toNat + window ≤ fr.rsp.toNat) (hn : n ≤ window) :
    (fr.rsp - BitVec.ofNat 64 n).toNat = fr.rsp.toNat - n := by
  have hle : BitVec.ofNat 64 n ≤ fr.rsp := by change n % 2^64 ≤ fr.rsp.toNat; omega
  rw [BitVec.toNat_sub_of_le hle, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by have := fr.rsp.isLt; omega)]

theorem local_span_disjoint_external {fr : Activation} {window n count : Nat}
    {external : MemoryRegion} (hroom : fr.low.toNat + window ≤ fr.rsp.toNat)
    (hn : n ≤ window) (hc : count ≤ n) (hsep : (callStack fr).Disjoint external) :
    (span (fr.rsp - BitVec.ofNat 64 n) count).Disjoint external := by
  intro x hx hy
  apply hsep x ?_ hy
  simp only [MemoryRegion.Contains, span, callStack, stack_sub_toNat fr hroom hn] at hx ⊢
  omega

theorem stack_local_spans_disjoint {fr : Activation} {window n count m count' : Nat}
    (hroom : fr.low.toNat + window ≤ fr.rsp.toNat) (hn : n ≤ window) (hm : m ≤ window)
    (_hc : count ≤ n) (_hc' : count' ≤ m) (hap : m + count ≤ n ∨ n + count' ≤ m) :
    (span (fr.rsp - BitVec.ofNat 64 n) count).Disjoint
      (span (fr.rsp - BitVec.ofNat 64 m) count') := by
  intro x hx hy
  simp only [MemoryRegion.Contains, span, stack_sub_toNat fr hroom hn,
    stack_sub_toNat fr hroom hm] at hx hy
  omega

theorem childStack_disjoint_local {fr child : Activation} {window callOffset n count : Nat}
    (hroom : fr.low.toNat + window ≤ fr.rsp.toNat) (hoff : callOffset ≤ window)
    (hlow : child.low = fr.rsp - BitVec.ofNat 64 window)
    (hsp : child.rsp = fr.rsp - BitVec.ofNat 64 callOffset)
    (hn : n + 8 ≤ callOffset) (_hc : count ≤ n) :
    (callStack child).Disjoint (span (fr.rsp - BitVec.ofNat 64 n) count) := by
  intro x hx hy
  simp only [MemoryRegion.Contains, span, callStack, hlow, hsp,
    stack_sub_toNat fr hroom (Nat.le_refl _), stack_sub_toNat fr hroom hoff,
    stack_sub_toNat fr hroom (show n ≤ window by omega)] at hx hy
  omega

theorem childStack_disjoint_external {fr child : Activation} {window callOffset : Nat}
    {external : MemoryRegion} (hroom : fr.low.toNat + window ≤ fr.rsp.toNat)
    (hoff : callOffset ≤ window)
    (hlow : child.low = fr.rsp - BitVec.ofNat 64 window)
    (hsp : child.rsp = fr.rsp - BitVec.ofNat 64 callOffset)
    (hsep : (callStack fr).Disjoint external) : (callStack child).Disjoint external := by
  intro x hx hy
  apply hsep x ?_ hy
  simp only [MemoryRegion.Contains, callStack, hlow, hsp,
    stack_sub_toNat fr hroom (Nat.le_refl _), stack_sub_toNat fr hroom hoff] at hx ⊢
  omega

theorem length_full_block_mask (length : BitVec 64) (hlength : length.toNat ≤ 2^32) :
    (0xffffffff0#64 &&& length) = BitVec.ofNat 64 (16 * (length.toNat / 16)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  change 68719476720 &&& length.toNat = (16 * (length.toNat / 16)) % 2^64
  have hd : (68719476720 &&& length.toNat) / 16 = length.toNat / 16 := by
    change (68719476720 &&& length.toNat) / 2^4 = _
    rw [Nat.and_div_two_pow]
    change (2^32-1) &&& (length.toNat / 16) = _
    rw [Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]
  have hm : (68719476720 &&& length.toNat) % 16 = 0 := by
    change (68719476720 &&& length.toNat) % 2^4 = _
    rw [Nat.and_mod_two_pow]
    change 0 &&& (length.toNat % 16) = 0
    exact Nat.zero_and _
  omega

theorem length_tail_byte_mask (length : BitVec 64) :
    ((length.setWidth 32) &&& 15).setWidth 64 = BitVec.ofNat 64 (length.toNat % 16) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat]
  change (((length.toNat % 2^32) &&& (2^4-1)) % 2^64) = (length.toNat % 2^4) % 2^64
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod_of_dvd _ (by decide : 2^4 ∣ 2^32)]
end AesGcm.Proofs.Machine.Runtime
