import Base16ct.Proofs.EncodeStr.Upper.Epilogue.Branch
import Base16ct.Proofs.EncodeStr.Upper.Epilogue.Success
import Base16ct.Proofs.EncodeStr.Upper.Epilogue.Failure
import Base16ct.Proofs.EncodeStr.Upper.Epilogue.Memory
import Base16ct.Proofs.EncodeStr.Upper.Callee.Memory
import Base16ct.Proofs.EncodeStr.Upper.Callee.Support
import Base16ct.Proofs.Common.Output

namespace Base16ct.Proofs.EncodeStr.Upper
open Base16ct.Spec.Program Standards.RFC.BaseEncodings Prelude X86 X86.Machine X86Proofs Epilogue

theorem epilogue_run [Bindings] (c : CallContext) {s : RamState}
    (hs : RunInvariant c s) (he : CalleeExit c s) :
    ∃ fuel t, Returns (returnBoundary c.initial) fuel s t ∧ ReadyToStep t ∧
      AgreesExcept (encoderComponents c.initial c.writeLength ++
        if 2 * c.input.length ≤ c.capacity then [.mem (c.initial.regValue .rdx) 8] else [])
        c.initial t ∧ t.regValue .rbx = c.initial.regValue .rbx ∧
      if 2 * c.input.length ≤ c.capacity then
        SuccessfulStatus t ∧
        readOutput c.initial t c.encoded.length = .ok c.encoded.toByteArray ∧
        readLengthOutput c.initial t = .ok (BitVec.ofNat 64 (2 * c.input.length))
      else FailureStatus t invalidLengthStatus := by
  have hstack := c.stack32
  obtain ⟨hboundary, houtside⟩ := returnBoundary_valid hstack c.valid.returnAddress
  obtain ⟨u, branch, ru, hip, au⟩ := branch_run hs.ready hs.code he.rip
    (by rw [he.rsp]; exact hs.stack_readable c 24 8 (by decide) (by decide)) houtside
  have hu : RunInvariant c u := hs.of_agrees c ru (au.mono (by simp [encoderComponents]))
  have mu : u.external = s.external := au.external (by simp [Component.Covers])
  have spu : stackPtr u = stackPtr c.initial - 24 :=
    (au.read (n := 64) (r := 4) (by simp)).trans he.rsp
  have bxu : u.regValue .rbx = c.initial.regValue .rdx :=
    (au.read (n := 64) (r := 3) (by simp)).trans he.rbx
  have saveu : (Operand.mem (stackPtr c.initial - 8) : Operand 64).read u =
      c.initial.regValue .rbx := by
    change memLoad u.external _ 64 = _
    rw [mu]
    exact he.savedRbx
  have retu : MemReadable u (stackPtr c.initial) 8 := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.sub_zero] using hu.stack_readable c 0 8 (by decide) (by decide)
  have topu := hu.returnSlot_read c
  by_cases hcap : 2 * c.input.length ≤ c.capacity
  · have result := he.result
    simp only [ite_eq_left hcap] at result
    obtain ⟨hptr, hlen, hout⟩ := result
    have hnonzero : c.initial.regValue .rcx ≠ 0 := by
      intro hz
      apply c.valid.outputInMemory.1
      change (c.initial.regValue .rcx).toNat = 0
      rw [hz]
      rfl
    have hipu : u.RIP = 0x10047d := by
      rw [hip, he.rsp, hptr, ite_eq_right hnonzero]
    have hlenu : (Operand.mem (stackPtr c.initial - 16) : Operand 64).read u =
        BitVec.ofNat 64 (2 * c.input.length) := by
      change memLoad u.external _ 64 = _
      rw [mu]
      exact hlen
    have hw := length_output_writable c hu hcap
    obtain ⟨t, tail, rt, frame, rax, rbx, length⟩ := success_run
      (BitVec.ofNat 64 (2 * c.input.length)) ru hu.code hipu spu
      (hu.stack_readable c 16 8 (by decide) (by decide)) hlenu
      (by rw [bxu]; exact hw)
      (by rw [bxu]; exact length_output_avoids_program c hcap)
      (by rw [bxu]; exact length_output_apart_stack c hcap (offset := 8) (by decide) (by decide))
      (by rw [bxu]; simpa only [BitVec.ofNat_eq_ofNat, BitVec.sub_zero] using
        length_output_apart_stack c hcap (offset := 0) (len := 8) (by decide) (by decide))
      (hu.stack_readable c 8 8 (by decide) (by decide)) saveu retu topu hboundary houtside
    rw [bxu] at frame length
    refine ⟨8, t, branch.returns tail, rt, ?_, rbx, ?_⟩
    · exact (hu.agrees.trans frame).mono (by simp [encoderComponents, hcap])
    · rw [ite_eq_left hcap]
      refine ⟨?_, ?_, Base16ct.Proofs.readLengthOutput_of_operand_read
        (memReadable_of_agrees hw.readable frame) length⟩
      · change (t.regValue .rax).setWidth 32 = 0
        rw [rax]
        rfl
      · rw [Base16ct.Proofs.readOutput_congr_prefix (s := s) (t := t) ?_]
        exact hout
        intro j hj
        rw [← mu]
        apply frame.byte
        intro component hc hcover
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> try exact hcover.elim
        obtain ⟨i, hi, hiEq⟩ := hcover
        apply length_output_apart_output c hcap i hi j _ hiEq.symm
        have helen : c.encoded.length = 2 * c.input.length := encode_length c.input
        omega
  · have result := he.result
    simp only [ite_eq_right hcap] at result
    obtain ⟨hptr, hbyte⟩ := result
    have hipu : u.RIP = 0x10048d := by
      rw [hip, he.rsp, hptr, ite_eq_left rfl]
    have hbyteu : (Operand.mem (stackPtr c.initial - 16) : Operand 8).read u = 1 := by
      change memLoad u.external _ 8 = _
      rw [mu]
      exact hbyte
    obtain ⟨t, tail, rt, frame, rax, rbx⟩ := failure_run ru hu.code hipu spu
      (hu.stack_readable c 16 1 (by decide) (by decide)) hbyteu
      (hu.stack_readable c 8 8 (by decide) (by decide)) saveu retu topu hboundary houtside
    refine ⟨8, t, branch.returns tail, rt, ?_, rbx, ?_⟩
    · exact (hu.agrees.trans frame).mono (by simp [encoderComponents, hcap])
    · rw [ite_eq_right hcap]
      change (t.regValue .rax).setWidth 32 = 1
      rw [rax]
      rfl

end Base16ct.Proofs.EncodeStr.Upper
