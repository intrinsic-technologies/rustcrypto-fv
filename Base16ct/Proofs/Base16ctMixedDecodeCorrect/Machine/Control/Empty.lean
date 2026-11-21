import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.Positive.Interface
import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.Outcome
import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.Control.Dispatch
import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.Control.Tail.Short

namespace Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine

open Base16ct.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem mixed_empty_return [Bindings] {initial : RamState} {capacity : Nat}
    {boundary : ReturnBoundary} (hCall : MixedInternalCall initial [] capacity boundary)
    (hReady : ReadyToStep initial) (hCode : CodeIn Extracted.programImage initial) :
    ∃ fuel final, Returns boundary fuel initial final ∧ final.RIP = boundary.rip ∧
      stackPtr final = boundary.rsp ∧ ReadyToStep final ∧ CodeIn Extracted.programImage final ∧
      AgreesExcept (mixedCallChanges initial 0 true) initial final ∧
      final.regValue .rbx = initial.regValue .rbx ∧
      final.regValue .rbp = initial.regValue .rbp ∧
      final.regValue .r14 = initial.regValue .r14 ∧
      (Operand.mem (initial.regValue .rdx) : Operand 64).read final = 0 ∧
      final.regValue .rax = 0 := by
  have hz : initial.regValue .rsi = 0#64 := BitVec.eq_of_toNat_eq hCall.length
  obtain ⟨fuel, a, runA, readyA, codeA, effect⟩ :=
    mixed_entry boundary hCall.returnOutside initial hReady hCode hCall.rip
  have frameA : AgreesExcept [.reg 0, .reg 9, .flags, .rip] initial a := effect.agrees
  have ripA : a.RIP = 0x1002fb := by
    simpa only [mixedEntryEffect, mixedDispatchEffect, hz, BitVec.toNat_zero,
      Nat.zero_mod, Nat.zero_div, Nat.zero_le, show (0 : BitVec 64) = 0#64 from rfl,
      ↓reduceIte] using effect.rip
  have cxA : a.regValue .rcx = initial.regValue .rcx :=
    frameA.read (n := 64) (r := 1) (by simp)
  obtain ⟨s, runS, ready, code, rip, frameS⟩ :=
    mixed_empty_tail readyA codeA ripA (by rw [cxA]; exact hCall.outputNonzero)
      hCall.returnOutside
  have frame := frameA.trans frameS
  have mem := frame.external (by simp [Component.Covers])
  have rdx : s.regValue .rdx = initial.regValue .rdx := frame.read (n := 64) (r := 2) (by simp)
  have rsp : stackPtr s = stackPtr initial := frame.read (n := 64) (r := 4) (by simp)
  have r9 : s.regValue .r9 = 0#64 := by
    apply (frameS.read (n := 64) (r := 9) (by simp)).trans
    change a.regValue .r9 = 0#64
    have hw := effect.writes.2
    change a.regValue .r9 = (if (initial.regValue .rsi).toNat % 2 = 0 then
      initial.regValue .rsi >>> 1 else initial.regValue .r9) at hw
    simpa only [hz, BitVec.toNat_zero, Nat.zero_mod, ↓reduceIte,
      BitVec.zero_ushiftRight] using hw
  have fit : ([] : List UInt8).length / 2 ≤ capacity := Nat.zero_le _
  have someOutput : ∃ output, mixedDecodeList [] = some output := ⟨[], rfl⟩
  have writable : Base16ct.Proofs.Copied.Md5.Proofs.Memory.MemWritable s (s.regValue .rdx) 8 := by
    rw [rdx]; exact (hCall.result fit someOutput).of_external_eq mem
  have avoid : ∀ i < 8, ¬ InProgram (s.regValue .rdx + BitVec.ofNat 64 i) := by
    rw [rdx]; exact hCall.resultAvoids fit someOutput
  have apart : RangeApart (s.regValue .rdx) 8 (stackPtr s) 8 := by
    rw [rdx, rsp]
    intro i hi j hj he
    exact hCall.returnResult fit someOutput j hj i hi he.symm
  have top : stackTop s = boundary.rip := by
    change memLoad s.external (stackPtr s) 64 = _
    rw [mem, rsp]; exact hCall.returnValue
  obtain ⟨final, ret, ripFinal, rspFinal, readyFinal, codeFinal, word, status, frameTail⟩ :=
    mixed_success_return ready code rip writable avoid apart
      (by rw [rsp]; exact hCall.returnRead.of_external_eq mem)
      top (by rw [rsp]; exact hCall.returnStack.symm) hCall.returnLow hCall.returnOutside
  rw [rdx] at frameTail word
  have frameAll := frame.trans frameTail
  refine ⟨(fuel + 2) + 3, final, (runA.trans runS).returns ret, ripFinal, rspFinal,
    readyFinal, codeFinal, ?_, frameAll.read (n := 64) (r := 3) (by simp),
    frameAll.read (n := 64) (r := 5) (by simp),
    frameAll.read (n := 64) (r := 14) (by simp), word.trans r9, status⟩
  exact frameAll.mono (by simp [mixedCallChanges])

end Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine
