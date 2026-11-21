import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.Control.Dispatch
import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.Control.Tail.Return
import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.Positive.Interface
import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.Outcome

namespace Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine

open Base16ct.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs

theorem mixed_length_error [Bindings] {initial : RamState} {input : List UInt8}
    {capacity : Nat} {boundary : ReturnBoundary}
    (hCall : MixedInternalCall initial input capacity boundary)
    (hReady : ReadyToStep initial) (hCode : CodeIn Extracted.programImage initial)
    (hInvalid : input.length % 2 ≠ 0 ∨ capacity < input.length / 2) :
    ∃ fuel final, Returns boundary fuel initial final ∧
      final.RIP = boundary.rip ∧ stackPtr final = boundary.rsp ∧
      ReadyToStep final ∧ CodeIn Extracted.programImage final ∧
      AgreesExcept (mixedCallChanges initial 0 false) initial final ∧
      final.regValue .rbx = initial.regValue .rbx ∧
      final.regValue .rbp = initial.regValue .rbp ∧
      final.regValue .r14 = initial.regValue .r14 ∧ final.regValue .rax = 1 := by
  obtain ⟨fuel, a, runA, readyA, codeA, effectA⟩ :=
    mixed_entry boundary hCall.returnOutside initial hReady hCode hCall.rip
  have ripA : a.RIP = 0x1002fa := by
    rw [effectA.rip]
    dsimp only [mixedEntryEffect, mixedDispatchEffect]
    rw [hCall.length, hCall.capacityArgument]
    split
    · have hCap : ¬ input.length / 2 ≤ capacity := by omega
      simp only [hCap, ↓reduceIte]
    · rfl
  have frameA : AgreesExcept [.reg 0, .reg 9, .flags, .rip] initial a := effectA.agrees
  have memA : a.external = initial.external := frameA.external (by simp [Component.Covers])
  have spA : stackPtr a = stackPtr initial := frameA.read (n := 64) (r := 4) (by simp)
  have readA : MemReadable a (stackPtr a) 8 := by
    rw [spA]; exact hCall.returnRead.of_external_eq memA
  have retA : stackTop a = boundary.rip := by
    change memLoad a.external (stackPtr a) 64 = _
    rw [memA, spA]; exact hCall.returnValue
  obtain ⟨t, runT, ripT, rspT, readyT, codeT, frameT⟩ :=
    common_return readyA codeA (Or.inl ripA) readA retA
      (by rw [spA]; exact hCall.returnStack.symm) hCall.returnLow
  have frame := frameA.trans frameT
  refine ⟨fuel + 1, t, runA.returns runT, ripT, rspT, readyT, codeT, ?_,
    frame.read (n := 64) (r := 3) (by simp),
    frame.read (n := 64) (r := 5) (by simp),
    frame.read (n := 64) (r := 14) (by simp), ?_⟩
  · exact frame.mono (by simp [mixedCallChanges])
  · exact (frameT.read (n := 64) (r := 0) (by simp)).trans effectA.writes.1

end Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine
