import Base16ct.Spec.Program
import X86Proofs.Program.Execution
import X86Proofs.Program.Entry
import X86Proofs.Instructions.Pop.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.Call.Triple

namespace Base16ct.Proofs.Base16ctUpperEncodeCorrect.Epilogue

open Base16ct.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem restore_return [Bindings] {initial s : RamState} (p : BitVec 64)
    (hr : ReadyToStep s) (hc : CodeIn (codeRange p [0x48, 0x83, 0xc4, 0x10, 0x5b, 0xc3]) s)
    (hip : s.RIP = p) (hsp : stackPtr s = stackPtr initial - 24)
    (hmb : MemReadable s (stackPtr initial - 8) 8)
    (hb : (Operand.mem (stackPtr initial - 8) : Operand 64).read s = initial.regValue .rbx)
    (hm : MemReadable s (stackPtr initial) 8)
    (hv : (Operand.mem (stackPtr initial) : Operand 64).read s =
      (returnBoundary initial).rip)
    (hl : (returnBoundary initial).rip.toNat < 2^32) :
    ∃ t, Returns (returnBoundary initial) 3 s t ∧ ReadyToStep t ∧
      AgreesExcept [.reg 3, .reg 4, .flags, .rip] s t ∧
      t.regValue .rbx = initial.regValue .rbx := by
  have hc1 : CodeIn (codeRange p [0x48, 0x83, 0xc4, 0x10]) s := by
    simpa using hc.mono (codeRange_slice_subset p [0x48, 0x83, 0xc4, 0x10, 0x5b, 0xc3] 0 4)
  obtain ⟨u, step1, ready1, e1⟩ := add_r64_imm8_effect_step p 0x48 0xc4 16
    (by constructor <;> decide +kernel) (by decide +kernel) (by decide +kernel) s hr hc1 hip
  change (addR64Imm8Effect p 4 16 s).Holds s u at e1
  have hu : stackPtr u = stackPtr initial - 8 := by
    have hw : stackPtr u = stackPtr s + 16 := e1.writes
    rw [hw, hsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have mem1 : u.external = s.external := e1.agrees.external (by simp [Component.Covers])
  have run1 : Advances (returnBoundary initial) 1 s u := by
    apply Advances.of_step step1
    right
    change stackPtr u ≠ stackPtr initial + 8
    rw [hu]
    intro he
    have : (-8 : BitVec 64) = 8 :=
      (BitVec.add_right_inj (stackPtr initial)).mp (by simpa only [BitVec.sub_eq_add_neg] using he)
    exact (by decide +kernel : (-8 : BitVec 64) ≠ 8) this
  have hcp : CodeIn (codeRange (p + 4) [0x5b]) u :=
    (hc.of_external_eq mem1).mono
      (codeRange_slice_subset p [0x48, 0x83, 0xc4, 0x10, 0x5b, 0xc3] 4 1)
  obtain ⟨v, stepP, readyP, ep⟩ := pop_r64_effect_step (p + 4) 0x5b
    (by decide +kernel) (by decide +kernel) u ready1 hcp
    ⟨e1.rip, by rw [hu]; exact ⟨hmb.low, fun i hi => mem1 ▸ hmb.mem i hi⟩⟩
  change (popR64Effect (p + 4) 1 3 u).Holds u v at ep
  have hvrsp : stackPtr v = stackPtr initial := by
    have hw : stackPtr v = stackPtr u + 8 := ep.writes.2
    rw [hw, hu, BitVec.sub_add_cancel]
  have memP : v.external = s.external :=
    (ep.agrees.external (by simp [Component.Covers])).trans mem1
  have runP : Advances (returnBoundary initial) 1 u v := by
    apply Advances.of_step stepP
    right
    change stackPtr v ≠ stackPtr initial + 8
    rw [hvrsp]
    intro he
    have : (0 : BitVec 64) = 8 := (BitVec.add_right_inj (stackPtr initial)).mp
      ((BitVec.add_zero _).trans he)
    contradiction
  have hc2 : CodeIn (codeRange (p + 5) [0xc3]) v :=
    (hc.of_external_eq memP).mono
      (codeRange_slice_subset p [0x48, 0x83, 0xc4, 0x10, 0x5b, 0xc3] 5 1)
  have top : stackTop v = (returnBoundary initial).rip := by
    change memLoad v.external (stackPtr v) 64 = _
    rw [hvrsp, memP]
    exact hv
  obtain ⟨t, step2, ready2, e2⟩ := ret_effect_step (p + 5) v readyP hc2
    ⟨⟨by simpa [popR64Effect, BitVec.add_assoc] using ep.rip,
      by rw [hvrsp]; exact ⟨hm.low, fun i hi => memP ▸ hm.mem i hi⟩⟩,
      top ▸ hl⟩
  have run2 : Returns (returnBoundary initial) 1 v t := by
    apply Returns.of_step step2 (e2.rip.trans top)
    change stackPtr t = stackPtr initial + 8
    have hw : stackPtr t = stackPtr v + 8 := e2.writes
    rw [hw, hvrsp]
  refine ⟨t, run1.returns (runP.returns run2), ready2,
    ((e1.agrees.trans ep.agrees).trans e2.agrees).mono (by simp), ?_⟩
  change (Operand.reg 3 : Operand 64).read t = _
  rw [e2.agrees.read (n := 64) (r := 3) (by simp)]
  change v.regValue .rbx = _
  have hw : v.regValue .rbx = (Operand.mem (stackPtr u) : Operand 64).read u := ep.writes.1
  rw [hw, hu]
  change memLoad u.external _ 64 = _
  rw [mem1]
  exact hb

end Base16ct.Proofs.Base16ctUpperEncodeCorrect.Epilogue
