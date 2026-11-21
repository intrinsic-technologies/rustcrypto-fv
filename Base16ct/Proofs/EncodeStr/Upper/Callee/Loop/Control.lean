import Base16ct.Proofs.EncodeStr.Upper.Context
import Base16ct.Proofs.Copied.Md5.Proofs.Streaming.Control
namespace Base16ct.Proofs.EncodeStr.Upper

open Base16ct.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem callee_loop_control [Bindings] (c : CallContext) {i : Nat} {s : RamState}
    (hi : i < c.input.length) (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s)
    (hp : s.RIP = 0x100639) (hindex : s.regValue .r8 = BitVec.ofNat 64 i)
    (hlen : s.regValue .rdx = BitVec.ofNat 64 c.input.length) :
    ∃ t, Advances (returnBoundary c.initial) 3 s t ∧ ReadyToStep t ∧
      AgreesExcept [.reg 8, .flags, .rip] s t ∧
      t.regValue .r8 = BitVec.ofNat 64 (i + 1) ∧
      t.RIP = if i + 1 < c.input.length then 0x1005f0 else 0x100641 := by
  have hout := (returnBoundary_valid c.valid.stack c.valid.returnAddress).2
  have hpre : Base16ct.Proofs.Copied.Md5.Proofs.Streaming.CounterPre (returnBoundary c.initial) 0x100639 8 2 s := by
    refine ⟨hr, ?_, hp, by decide +kernel, ?_, ?_⟩
    · exact program_text_slice hc 0x639 6 (by decide +kernel)
    · exact text_address_ne_return hout 0x63c (by decide +kernel)
    · exact text_address_ne_return hout 0x63f (by decide +kernel)
  obtain ⟨u, hu⟩ := Base16ct.Proofs.Copied.Md5.Proofs.Streaming.counter_increment_compare hpre
  have hcu : CodeIn Extracted.programImage u :=
    hu.agrees.codeIn (by simp [Component.Covers]) hc
  have hindexNext : s.regValue .r8 + 1 = BitVec.ofNat 64 (i + 1) := by
    rw [hindex]
    exact (BitVec.ofNat_add i 1).symm
  have hinc : u.regValue .r8 = BitVec.ofNat 64 (i + 1) :=
    (show u.regValue .r8 = s.regValue .r8 + 1 from hu.indexValue).trans hindexNext
  have hn : c.input.length < 2^64 := by
    have hb := c.valid.inputInMemory.2.1
    have hb : (c.initial.regValue .rdi).toNat + c.input.length < 2^32 := by
      simpa only [inputRegion, registerRegion, MemoryRegion.Bounded, userAddressLimit, List.size_toByteArray] using hb
    omega
  have hin : i + 1 < 2^64 := by omega
  have hzero : (StatusFlags.ofRFLAGS u.RFLAGS).ZF = decide (c.input.length = i + 1) := by
    have hz := hu.zero
    change (StatusFlags.ofRFLAGS u.RFLAGS).ZF =
      (s.regValue .rdx == s.regValue .r8 + 1) at hz
    rw [hz, hlen, hindexNext]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq, BitVec.toNat_eq, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hin]
  have hnext : (jccEffect 0x10063f 2 5 ((0xaf : BitVec 8).signExtend 64) u).rip =
      if i + 1 < c.input.length then 0x1005f0 else 0x100641 := by
    by_cases hlt : i + 1 < c.input.length
    · have hne : c.input.length ≠ i + 1 := by omega
      simp [jccEffect, branchEffect, condHolds, hzero, hne, hlt, branchTarget]
    · have heq : c.input.length = i + 1 := by omega
      simp [jccEffect, branchEffect, condHolds, hzero, heq]
  have hne : (jccEffect 0x10063f 2 5 ((0xaf : BitVec 8).signExtend 64) u).rip ≠
      (returnBoundary c.initial).rip := by
    rw [hnext]
    split
    · exact text_address_ne_return hout 0x5f0 (by decide +kernel)
    · exact text_address_ne_return hout 0x641 (by decide +kernel)
  have hbranch : CodeIn (codeRange 0x10063f
      (jccOpcode8 5 :: immBytes 8 (0xaf : BitVec 8))) u :=
    program_text_slice hcu 0x63f 2 (by decide +kernel)
  obtain ⟨t, ht, hrt, he⟩ := (jcc_rel8_effect_step 0x10063f 5 0xaf).advances
    hu.ready hbranch ⟨hu.rip, fun _ ↦ by decide +kernel⟩ hne
  have hat : AgreesExcept [.rip] u t := he.agrees
  refine ⟨t, hu.advances.trans ht, hrt, ?_, ?_, he.rip.trans hnext⟩
  · exact (hu.agrees.trans hat).mono (by simp)
  · exact (hat.read (n := 64) (r := 8) (by simp)).trans hinc

end Base16ct.Proofs.EncodeStr.Upper
