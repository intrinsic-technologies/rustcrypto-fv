import Base16ct.Proofs.Base16ctUpperEncodeCorrect.Callee.Loop.Load
import Base16ct.Proofs.Base16ctUpperEncodeCorrect.Callee.Loop.Circuit
import Base16ct.Proofs.Base16ctUpperEncodeCorrect.Callee.Loop.Store
import Base16ct.Proofs.Base16ctUpperEncodeCorrect.Callee.Loop.Control
import Base16ct.Proofs.Base16ctUpperEncodeCorrect.Callee.Memory
import Base16ct.Proofs.Base16ctUpperEncodeCorrect.Callee.Support

namespace Base16ct.Proofs.Base16ctUpperEncodeCorrect

open Base16ct.Spec.Program Prelude X86 X86.Machine X86Proofs

theorem callee_loop_step [Bindings] (c : CallContext) {i : Nat} {s : RamState}
    (hc : 2 * c.input.length ≤ c.capacity) (hs : LoopState c i s)
    (hi : i < c.input.length) :
    ∃ t, Advances (returnBoundary c.initial) 21 s t ∧ LoopState c (i + 1) t := by
  have hout := (returnBoundary_valid c.valid.stack c.valid.returnAddress).2
  obtain ⟨s1, a1, r1, f1, p1, b1⟩ := callee_loop_load c hs hi
    (hs.invariant.input_byte_readable c i hi)
    ((hs.invariant.input_bytes c).loadByte i hi)
  have q1 : AgreesExcept (calleeComponents c) s s1 :=
    f1.mono (by simp [calleeComponents])
  have v1 := hs.invariant.of_callee_agrees c r1 q1
  obtain ⟨s2, a2, r2, _, p2, f2, b2⟩ := highCircuit_advances hout r1 v1.code p1
    (c.input.getD i 0) b1
  have q2 : AgreesExcept (calleeComponents c) s1 s2 :=
    f2.mono (by simp [calleeComponents])
  have v2 := v1.of_callee_agrees c r2 q2
  have f02 := f1.trans f2
  have d2 : s2.regValue .rcx = c.initial.regValue .rcx :=
    (f02.read (n := 64) (r := 1) (by simp)).trans hs.dst
  have i2 : s2.regValue .r8 = BitVec.ofNat 64 i :=
    (f02.read (n := 64) (r := 8) (by simp)).trans hs.index
  have o2 : Bytes s2.external (c.initial.regValue .rcx) (2 * i)
      (fun j ↦ (encodedBytes c.input).getD j 0) := by
    rw [f02.external (by simp [Component.Covers])]
    exact hs.output
  have e2 : (Operand.reg 11 : Operand 8).read s2 =
      ((encodedBytes c.input).getD (2 * i) 0).toBitVec := by
    rw [encodedBytes_getD_even c.input i hi]
    exact b2
  obtain ⟨s3, a3, v3, p3, f3, o3⟩ := store_high_step c v2 p2 d2 i2 hc
    (by omega) o2 e2
  have q3 := callee_output_store_widen c (offset := 2 * i) (count := 1)
    hc (by omega) f3
  have f03 := f02.trans f3
  have b3 : s3.regValue .r9 = (c.input.getD i 0).toBitVec.setWidth 64 :=
    ((f2.trans f3).read (n := 64) (r := 9) (by simp)).trans b1
  obtain ⟨s4, a4, r4, _, p4, f4, b4⟩ := lowCircuit_advances hout v3.ready v3.code p3
    (c.input.getD i 0) b3
  have q4 : AgreesExcept (calleeComponents c) s3 s4 :=
    f4.mono (by simp [calleeComponents])
  have v4 := v3.of_callee_agrees c r4 q4
  have f04 := f03.trans f4
  have d4 : s4.regValue .rcx = c.initial.regValue .rcx :=
    (f04.read (n := 64) (r := 1) (by simp)).trans hs.dst
  have i4 : s4.regValue .r8 = BitVec.ofNat 64 i :=
    (f04.read (n := 64) (r := 8) (by simp)).trans hs.index
  have o4 : Bytes s4.external (c.initial.regValue .rcx) (2 * i + 1)
      (fun j ↦ (encodedBytes c.input).getD j 0) := by
    rw [f4.external (by simp [Component.Covers])]
    exact o3
  have e4 : (Operand.reg 10 : Operand 8).read s4 =
      ((encodedBytes c.input).getD (2 * i + 1) 0).toBitVec := by
    rw [encodedBytes_getD_odd c.input i hi]
    exact b4
  obtain ⟨s5, a5, v5, p5, f5, o5⟩ := store_low_step c v4 p4 d4 i4 hc
    (by omega) o4 e4
  have q5 := callee_output_store_widen c (offset := 2 * i + 1) (count := 1)
    hc (by omega) f5
  have f05 := f04.trans f5
  have i5 : s5.regValue .r8 = BitVec.ofNat 64 i :=
    (f05.read (n := 64) (r := 8) (by simp)).trans hs.index
  have l5 : s5.regValue .rdx = BitVec.ofNat 64 c.input.length :=
    (f05.read (n := 64) (r := 2) (by simp)).trans hs.length
  obtain ⟨t, a6, r6, f6, it, pt⟩ := callee_loop_control c hi v5.ready v5.code p5 i5 l5
  have q6 : AgreesExcept (calleeComponents c) s5 t :=
    f6.mono (by simp [calleeComponents])
  have vt := v5.of_callee_agrees c r6 q6
  have f := f05.trans f6
  have q : AgreesExcept (calleeComponents c) s t :=
    (((((q1.trans q2).trans q3).trans q4).trans q5).trans q6).mono (by simp)
  refine ⟨t, (((((a1.trans a2).trans a3).trans a4).trans a5).trans a6), ?_⟩
  refine
    { invariant := vt
      rsp := (f.read (n := 64) (r := 4) (by simp)).trans hs.rsp
      result := (f.read (n := 64) (r := 0) (by simp)).trans hs.result
      returnAddress := (calleeComponents_return c q).trans hs.returnAddress
      rbx := (f.read (n := 64) (r := 3) (by simp)).trans hs.rbx
      savedRbx := (calleeComponents_savedRbx c q).trans hs.savedRbx
      bound := by omega
      rip := pt
      src := (f.read (n := 64) (r := 6) (by simp)).trans hs.src
      length := (f.read (n := 64) (r := 2) (by simp)).trans hs.length
      dst := (f.read (n := 64) (r := 1) (by simp)).trans hs.dst
      resultLength := (f.read (n := 64) (r := 7) (by simp)).trans hs.resultLength
      index := it
      output := ?_ }
  rw [f6.external (by simp [Component.Covers])]
  simpa only [show 2 * (i + 1) = 2 * i + 1 + 1 by omega] using o5

end Base16ct.Proofs.Base16ctUpperEncodeCorrect
