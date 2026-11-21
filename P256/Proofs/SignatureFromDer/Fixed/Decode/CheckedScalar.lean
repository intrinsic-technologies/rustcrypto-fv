import P256.Proofs.SignatureFromDer.Fixed.Scalar.RangeState
import P256.Proofs.SignatureFromDer.Fixed.Decode.Status

set_option autoImplicit false

open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)
open P256.Proofs.SignatureFromDer.Fixed.Scalar (ScalarResultAt)
open P256.Proofs.Program (CalleePre readyToStep)

namespace P256.Proofs.SignatureFromDer.Fixed.Decode

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem scalar_status [Bindings] {s t : RamState} {boundary : ReturnBoundary} {input : ByteArray}
    (pre : CalleePre s boundary 0x109ac0 64 72 560) (state : Stage s t boundary)
    (second : Bool) (rip : t.RIP = if second then 0x109b7f else 0x109b11)
    (result : ScalarResultAt t (stackPtr t + 8) input) :
    ∃ u, Stage s u boundary ∧
      u.RIP = (if P256.Spec.Arith.uint input < P256.Spec.Operations.domain.n
        then if second then 0x109b8a else 0x109b1c else 0x109c57) ∧
      (P256.Spec.Arith.uint input < P256.Spec.Operations.domain.n →
        Nat256At u (stackPtr u + 16) (P256.Spec.Arith.uint input)) ∧
      AgreesExcept [.flags, .rip] t u := by
  have read := stack_readable pre state.toFrame (offset := 8) (len := 8) (by decide)
  have tag : memLoad t.external (stackPtr t + 8) 32 =
      if P256.Spec.Arith.uint input < P256.Spec.Operations.domain.n then 0 else 1 := by
    by_cases range : P256.Spec.Arith.uint input < P256.Spec.Operations.domain.n
    · have result' := result
      simp only [ScalarResultAt, range, ite_true] at result'
      have h := P256.Proofs.Common.Memory.memLoad32_of_loadBytes64 read.mem result'.1
      simpa [range] using h
    · have result' := result
      simp only [ScalarResultAt, range, ite_false] at result'
      have h := P256.Proofs.Common.Memory.memLoad32_of_loadBytes64 read.mem result'
      simpa [range] using h
  obtain ⟨u, run, ready, ip, agrees⟩ := status second
    (readyToStep state.machine state.bindingsSupported) state.loaded rip
    (stack_readable pre state.toFrame (offset := 8) (len := 4) (by decide)) pre.outerBoundary
  refine ⟨u, state.after_registers run ready agrees (by simp [Component.Covers]) (by simp), ?_, ?_, agrees⟩
  · rw [tag] at ip
    by_cases range : P256.Spec.Arith.uint input < P256.Spec.Operations.domain.n
    · simpa [range] using ip
    · simpa [range] using ip
  · intro range
    have scalar : Nat256At t (stackPtr t + 16) (P256.Spec.Arith.uint input) := by
      have result' := result
      simp only [ScalarResultAt, range, ite_true] at result'
      simpa [BitVec.add_assoc] using result'.2
    have memory := agrees.external (by simp [Component.Covers])
    have sp : stackPtr u = stackPtr t := agrees.read (n := 64) (r := 4) (by simp)
    simpa only [Nat256At, memory, sp] using scalar

end P256.Proofs.SignatureFromDer.Fixed.Decode
