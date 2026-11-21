import Base16ct.Proofs.Base16ctLowerEncodeCorrect.Machine.Interface
import X86Proofs.Instructions.Inc.Generated.R.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Branch.Triple

namespace Base16ct.Proofs.LowerEncode

open Base16ct.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem loop_tail [Bindings] {boundary : ReturnBoundary} (outside : ¬ InProgram boundary.rip)
    {s : RamState} (ready : ReadyToStep s) (code : CodeIn Extracted.programImage s)
    (rip : s.RIP = 0x1005a9) {index length : Nat} (hi : index < length)
    (hlen : length < 2 ^ 64)
    (indexValue : (Operand.reg 8 : Operand 64).read s = BitVec.ofNat 64 index)
    (lengthValue : (Operand.reg 2 : Operand 64).read s = BitVec.ofNat 64 length) :
    ∃ t, Advances boundary 3 s t ∧ ReadyToStep t ∧
      t.RIP = (if index + 1 < length then 0x100560 else 0x1005b1) ∧
      (Operand.reg 8 : Operand 64).read t = BitVec.ofNat 64 (index + 1) ∧
      AgreesExcept [.reg 8, .flags, .rip] s t := by
  have c1 : CodeIn (codeRange 0x1005a9 [0x49, 0xff, 0xc0]) s :=
    program_text_slice code 0x5a9 3 (by decide +kernel)
  obtain ⟨s1, run1, ready1, e1⟩ :=
    (inc_r64_effect_step 0x1005a9 0x49 0xc0 (by unfold RexWPrefix; decide +kernel) rfl rfl).advances
      ready c1 rip (text_address_ne_return outside 0x5ac (by decide +kernel))
  have code1 := e1.codeIn (incR64Effect_avoids _ _ _ _) code
  have i1 : (Operand.reg 8 : Operand 64).read s1 = BitVec.ofNat 64 (index + 1) := by
    have hw := e1.writes
    change (Operand.reg 8 : Operand 64).read s1 =
      (Operand.reg 8 : Operand 64).read s + 1 at hw
    rw [hw, indexValue, BitVec.ofNat_add]
    rfl
  have l1 : (Operand.reg 2 : Operand 64).read s1 = BitVec.ofNat 64 length :=
    (e1.agrees.read (by simp [incR64Effect_components]; decide)).trans lengthValue
  have c2 : CodeIn (codeRange 0x1005ac [0x4c, 0x39, 0xc2]) s1 :=
    program_text_slice code1 0x5ac 3 (by decide +kernel)
  obtain ⟨s2, run2, ready2, e2⟩ :=
    (cmp_r64_r64_effect_step 0x1005ac 0x4c 0xc2 (by unfold RexWPrefix; decide +kernel) rfl).advances
      ready1 c2 e1.rip (text_address_ne_return outside 0x5af (by decide +kernel))
  have code2 := e2.codeIn (cmpR64R64Effect_avoids _ _ _ _ _) code1
  have zf : (StatusFlags.ofRFLAGS s2.RFLAGS).ZF =
      (BitVec.ofNat 64 length - BitVec.ofNat 64 (index + 1) == 0) := by
    have h := e2.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS s2.RFLAGS).ZF =
      ((Operand.reg 2 : Operand 64).read s1 - (Operand.reg 8 : Operand 64).read s1 == 0) at h
    simpa only [l1, i1] using h
  have eqiff : BitVec.ofNat 64 length - BitVec.ofNat 64 (index + 1) = 0#64 ↔
      index + 1 = length := by
    rw [BitVec.sub_eq_iff_eq_add, BitVec.zero_add]
    constructor
    · intro h
      have hh := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen,
        Nat.mod_eq_of_lt (show index + 1 < 2 ^ 64 by omega)] at hh
      omega
    · intro h
      rw [h]
  have branchRip : (jccEffect 0x1005af 2 5 ((0xaf#8).signExtend 64) s2).rip =
      (if index + 1 < length then 0x100560 else 0x1005b1) := by
    change (if !(StatusFlags.ofRFLAGS s2.RFLAGS).ZF then 0x100560#64 else 0x1005b1#64) = _
    rw [zf]
    by_cases hnext : index + 1 < length
    · have hn : BitVec.ofNat 64 length - BitVec.ofNat 64 (index + 1) ≠ 0#64 := by
        intro he
        have := eqiff.mp he
        omega
      simp [hnext, hn]
    · have he : BitVec.ofNat 64 length - BitVec.ofNat 64 (index + 1) = 0#64 := by
        rw [eqiff]
        omega
      simp [hnext, he]
  have c3 : CodeIn (codeRange 0x1005af [0x75, 0xaf]) s2 :=
    program_text_slice code2 0x5af 2 (by decide +kernel)
  have hne : (jccEffect 0x1005af 2 5 ((0xaf#8).signExtend 64) s2).rip ≠ boundary.rip := by
    rw [branchRip]
    split
    · exact text_address_ne_return outside 0x560 (by decide +kernel)
    · exact text_address_ne_return outside 0x5b1 (by decide +kernel)
  obtain ⟨t, run3, readyt, e3⟩ := (jcc_rel8_effect_step 0x1005af 5 0xaf).advances
    ready2 c3 ⟨e2.rip, fun _ => by decide +kernel⟩ hne
  refine ⟨t, run1.trans (run2.trans run3), readyt, e3.rip.trans branchRip, ?_, ?_⟩
  · exact (e3.agrees.read (by simp [jccEffect])).trans ((e2.agrees.read (by simp)).trans i1)
  · exact ((e1.agrees.trans e2.agrees).trans e3.agrees).mono (by simp [jccEffect, incR64Effect_components, cmpR64R64Effect_components]; decide)

end Base16ct.Proofs.LowerEncode
