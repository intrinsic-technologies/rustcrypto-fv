import P256.Proofs.Sec1.Decode.Result.Choice
import P256.Proofs.Sec1.Decode.Result.Selection
import P256.Proofs.Sec1.Decode.Result.Tail
import P256.Proofs.Sec1.Representation

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decode

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem result [Bindings] {original s : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} (pre : DecodePre original boundary bytes) (state : Frame original s)
    (rip : s.RIP = 0x10e632)
    (output : s.regValue .r15 = original.regValue .rdi) (zero : s.regValue .r12 = 0)
    (affine : AffineResultAt s (stackPtr original - 312) (P256.Spec.Points.decodePoint bytes))
    (shape : EncodingShape bytes)
    (tagByte : s.external[stackPtr original - 156]? = some (bytes.data[0]?.getD 0)) :
    ∃ fuel t, Advances boundary fuel s t ∧ Frame original t ∧ t.RIP = 0x10e696 ∧
      PublicKeyResultAt t (original.regValue .rdi) (P256.Spec.Points.decodePublicKey bytes) ∧
      t.regValue .rdi = original.regValue .rdi := by
  have flagByte : s.external[stackPtr original - 240]? =
      some (Result.validityFlag (P256.Spec.Points.decodePoint bytes)) := by
    have address : stackPtr original - 312 + 72 = stackPtr original - 240 := by
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
      rfl
    cases decoded : P256.Spec.Points.decodePoint bytes with
    | none =>
      rw [decoded] at affine
      simpa only [AffineResultAt, address, Result.validityFlag] using affine
    | some point =>
      rw [decoded] at affine
      simpa only [address, Result.validityFlag] using affine.2
  have tagValid : (bytes.data[0]?.getD 0).toBitVec = 0 ∨
      (bytes.data[0]?.getD 0).toBitVec = 2 ∨ (bytes.data[0]?.getD 0).toBitVec = 3 ∨
      (bytes.data[0]?.getD 0).toBitVec = 4 ∨ (bytes.data[0]?.getD 0).toBitVec = 5 := by
    rcases shape with rfl | ⟨_, h | h | h⟩ | ⟨_, h⟩
    · exact .inl rfl
    all_goals simp only [h, Option.getD_some]; decide +kernel
  obtain ⟨n, a, runA, stateA, ripA, outputA, copied⟩ :=
    Result.selection pre state rip output zero (bytes.data[0]?.getD 0)
      (Result.validityFlag (P256.Spec.Points.decodePoint bytes)) tagByte flagByte tagValid
  rw [Result.choice_correct shape] at ripA
  cases decoded : P256.Spec.Points.decodePublicKey bytes with
  | none =>
    obtain ⟨m, t, runT, stateT, ripT, represented, destinationT⟩ :=
      Result.failure_tail pre stateA (by simpa [decoded] using ripA) outputA
    exact ⟨n + m, t, runA.trans runT, stateT, ripT, by simpa only [decoded] using represented, destinationT⟩
  | some point =>
    obtain ⟨x, y, rfl⟩ := decodePublicKey_some_affine decoded
    have raw := decodePublicKey_affine.mp decoded
    have originalAffine : AffineAt s (stackPtr original - 312) (.affine x y) := by
      rw [raw] at affine
      exact affine.1
    obtain ⟨m, t, runT, stateT, ripT, represented, destinationT⟩ :=
      Result.success_tail pre stateA
        (by simpa [decoded] using ripA)
        outputA (originalAffine.of_bytes_eq copied)
    exact ⟨n + m, t, runA.trans runT, stateT, ripT, by simpa only [decoded] using represented, destinationT⟩

end P256.Proofs.Sec1.Decode
