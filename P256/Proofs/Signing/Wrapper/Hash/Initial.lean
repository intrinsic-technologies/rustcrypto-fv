import P256.Proofs.Signing.Wrapper.Hash.Initialize
import P256.Proofs.Signing.Wrapper.Entry.HashCall.Input

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Hash

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem message_input [Bindings] {initial start s : RamState} {secret message : ByteArray} {offset : Nat}
    (pre : HashEntry initial start secret message) (state : Frame initial start s offset) :
    (messageRegion initial message).Bounded ∧
    (messageRegion initial message).HasBytes s.external message ∧
    (messageRegion initial message).Disjoint (Stack.region initial 5112) := by
  obtain ⟨slices, call⟩ := pre.context.call
  obtain ⟨address, pointer, _, bounded, bytes, _⟩ :=
    Entry.HashCall.preserved_message_input call state.frame
  have region : messageRegion initial message = MemoryRegion.mk address.toNat message.size := by
    unfold messageRegion
    exact congrArg (fun a : BitVec 64 => MemoryRegion.mk a.toNat message.size) pointer
  refine ⟨region ▸ bounded, region ▸ bytes, ?_⟩
  intro a ha hb
  exact wrapper_read_disjoint call (Entry.HashCall.message_input_region call)
    (callStack signingKeyTrySign initial) (by simp [wrapperRegions]) a ha
    (stack_contains_callStack (routine := signingKeyTrySign) hb)

theorem message_size [Bindings] {initial start : RamState} {secret message : ByteArray}
    (pre : HashEntry initial start secret message) : message.size < 2^32 := by
  have bound := (message_input pre (initial_frame pre)).1
  change (memLoad initial.external (initial.regValue .rdi + 8) 64).toNat + message.size < 2^32 at bound
  omega

end P256.Proofs.Signing.Wrapper.Hash
