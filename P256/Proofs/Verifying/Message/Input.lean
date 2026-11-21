import P256.Proofs.Verifying.Message.Frame
import P256.Proofs.Sec1.Representation
import P256.Proofs.Program.Frame

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message

open P256.Spec P256.Spec.Program.Routines Program
open Standards.SECG.ECC
open SecretKeyFromBytes.Scalar (Nat256At)
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem input_preserved [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} {key : Curve.Point} {r scalarS : Nat}
    (pre : Pre initial boundary message) (input : InputAt initial key r scalarS)
    (frame : MemoryWriteFrame initial s #v[Stack.region initial 9992]) :
    Sec1.AffineAt s (initial.regValue .rsi) key ∧
      Nat256At s (initial.regValue .r8) r ∧
      Nat256At s (initial.regValue .r8 + 32) scalarS := by
  have keyBytes (i : Nat) (hi : i < 72) :
      s.external[initial.regValue .rsi + BitVec.ofNat 64 i]? =
        initial.external[initial.regValue .rsi + BitVec.ofNat 64 i]? := by
    apply frame_read frame (region := registerRegion initial .rsi 72) _
      (memoryRegion_contains_add pre.inputBounded (Nat.le_refl _) (Nat.le_refl _) hi)
    intro region member
    have eq : region = Stack.region initial 9992 := by simpa using member
    subst region
    exact pre.separation 0 2 (by decide)
  have signatureBytes (i : Nat) (hi : i < 64) :
      s.external[initial.regValue .r8 + BitVec.ofNat 64 i]? =
        initial.external[initial.regValue .r8 + BitVec.ofNat 64 i]? := by
    apply frame_read frame (region := registerRegion initial .r8 64) _
      (memoryRegion_contains_add pre.signatureBounded (Nat.le_refl _) (Nat.le_refl _) hi)
    intro region member
    have eq : region = Stack.region initial 9992 := by simpa using member
    subst region
    exact pre.signatureStack
  refine ⟨input.key.of_bytes_eq (fun i hi => keyBytes i (by omega)),
    ⟨input.r.1, fun i hi => (signatureBytes i (by omega)).trans (input.r.2 i hi)⟩,
    input.scalarS.1, ?_⟩
  intro i hi
  have bytes := signatureBytes (32 + i) (by omega)
  rw [BitVec.ofNat_add, ← BitVec.add_assoc] at bytes
  exact bytes.trans (input.scalarS.2 i hi)

theorem message_size_bound [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} (pre : Pre s boundary message) : message.size < 2^32 := by
  have bound := pre.messageBounded
  change (memLoad s.external (s.regValue .rdx) 64).toNat + message.size < 2^32 at bound
  omega

end P256.Proofs.Verifying.Message
