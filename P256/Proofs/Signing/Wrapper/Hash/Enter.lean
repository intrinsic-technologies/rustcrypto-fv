import P256.Proofs.Signing.Wrapper.Hash.Initial
import P256.Proofs.Signing.Wrapper.Hash.Branch

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Hash

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Entered [Bindings] (initial start t : RamState) (message : ByteArray) : Prop
    extends Frame initial start t where
  rip : t.RIP = if message.size < 64 then 0x102782 else 0x1027fd
  hash : HMAC.Sha256StateAt t (frameBase initial + 176) .empty
  pointer : t.regValue .rsi = start.regValue .rsi
  length : t.regValue .rbp = BitVec.ofNat 64 message.size

theorem enter [Bindings] {initial start s : RamState} {secret message : ByteArray}
    (pre : HashEntry initial start secret message) (state : Initialized initial start s message) :
    ∃ t, Entered initial start t message := by
  obtain ⟨t, run, ready, rip, agrees⟩ := branch
    (readyToStep state.machine state.bindingsSupported) state.loaded state.rip (outside pre.context)
  have frame := state.toFrame.after_registers pre.context run ready agrees
    (by simp [Component.Covers]) (by simp) (by simp)
  have memory := agrees.external (by simp [Component.Covers])
  refine ⟨t, frame, ?_, ?_, ?_, ?_⟩
  · have bound := message_size pre
    simpa only [state.length, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : message.size < 2^64)] using rip
  · exact state.hash.copy (by intro i _; rw [memory])
  · exact (agrees.read (n := 64) (r := 6) (by simp)).trans state.pointer
  · exact (agrees.read (n := 64) (r := 5) (by simp)).trans state.length

end P256.Proofs.Signing.Wrapper.Hash
