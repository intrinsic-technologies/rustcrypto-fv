import P256.Proofs.Signing.Core.Iteration.Components.Constructor.Decode.Status
import P256.Proofs.SignatureFromDer.Model
import P256.Proofs.SignatureFromDer.Fixed.Scalar.RangeState

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Components.Constructor.Decode

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Proofs.SignatureFromDer.Fixed.Scalar (ScalarResultAt)

theorem scalar_status [Bindings] {s t : RamState} {boundary : ReturnBoundary} {value : Nat}
    (pre : CalleePre s boundary 0x109890 32 72 512) (state : Stage s t boundary)
    (second : Bool) (rip : t.RIP = if second then 0x10994b else 0x1098c2)
    (canonical : value < Operations.domain.n)
    (result : ScalarResultAt t (stackPtr t) (Standards.SECG.ECC.Encoding.natToOctets 32 value)) :
    ∃ u, Stage s u boundary ∧ u.RIP = (if second then 0x109955 else 0x1098cc) ∧
      Nat256At u (stackPtr u + 8#64) value ∧ AgreesExcept [.flags, .rip] t u := by
  have encoding : Arith.uint (Standards.SECG.ECC.Encoding.natToOctets 32 value) = value := by
    change Standards.SECG.ECC.Encoding.octetsToNat _ = value
    rw [P256.Proofs.SignatureFromDer.octetsToNat_natToOctets, Nat.mod_eq_of_lt
      (Nat.lt_trans canonical (by decide +kernel : Operations.domain.n < 256^32))]
  have decoded : loadBytes t.external (stackPtr t) 8 = .ok (0 : BitVec 64) ∧
      Nat256At t (stackPtr t + 8#64) value := by
    unfold ScalarResultAt at result
    rw [encoding, ite_eq_left canonical] at result
    exact result
  have read : MemReadable t (stackPtr t) 8 := by
    simpa only [BitVec.add_zero] using stack_readable pre state.toFrame (offset := 0) (len := 8) (by decide)
  have tag : memLoad t.external (stackPtr t) 32 = 0 :=
    P256.Proofs.Common.Memory.memLoad32_of_loadBytes64 read.mem decoded.1
  obtain ⟨u, run, ready, ip, agrees⟩ := status second
    (readyToStep state.machine state.bindingsSupported) state.loaded rip
    (by simpa only [BitVec.add_zero] using stack_readable pre state.toFrame (offset := 0) (len := 4) (by decide))
    pre.outerBoundary
  have memory := agrees.external (by simp [Component.Covers])
  have sp : stackPtr u = stackPtr t := agrees.read (n := 64) (r := 4) (by simp)
  refine ⟨u, state.after_registers run ready agrees (by simp [Component.Covers]) (by simp),
    ?_, ?_, agrees⟩
  · rw [tag, ite_eq_right (by decide : ¬ (0 : BitVec 32) = 1)] at ip
    exact ip
  · simpa only [Nat256At, memory, sp] using decoded.2

end P256.Proofs.Signing.Core.Iteration.Components.Constructor.Decode
