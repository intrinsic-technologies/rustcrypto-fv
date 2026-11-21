import P256.Proofs.Signing.Wrapper.Hash.Absorb.Interface
import P256.Proofs.Signing.Wrapper.Hash.Absorb.Short.Setup

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Hash.Absorb.Short

open P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Ready [Bindings] (initial start s t : RamState) (message : ByteArray) : Prop
    extends Frame initial start t where
  rip : t.RIP = 0x10278d
  destination : t.regValue .rdi = frameBase initial + 176
  source : t.regValue .rsi = start.regValue .rsi
  count : t.regValue .rdx = BitVec.ofNat 64 message.size
  length : t.regValue .rbp = BitVec.ofNat 64 message.size
  memory : t.external = s.external

theorem prepare [Bindings] {initial start s : RamState} {secret message : ByteArray}
    (pre : HashEntry initial start secret message) (state : Entered initial start s message)
    (short : message.size < 64) : ∃ t, Ready initial start s t message := by
  obtain ⟨fuel, t, run, ready, _, effect⟩ := Setup.run (returnBoundary initial)
    (outside pre.context) s (readyToStep state.machine state.bindingsSupported)
    (Setup.code state.loaded) (by simpa only [short, ite_true] using state.rip)
  refine ⟨t, state.toFrame.after_registers pre.context run ready effect.agrees
    (by simp [Setup.effect, Effect.components, Write.component, Operand.component, Component.Covers])
    (by simp [Setup.effect, Effect.components, Write.component, Operand.component]), effect.rip,
    effect.writes.1.trans (congrArg (· + 176) state.rsp), ?_,
    effect.writes.2.trans state.length, ?_, ?_⟩
  · exact (effect.agrees.read (n := 64) (r := 6) (by
      simp [Setup.effect, Effect.components, Write.component, Operand.component])).trans state.pointer
  · exact (effect.agrees.read (n := 64) (r := 5) (by
      simp [Setup.effect, Effect.components, Write.component, Operand.component])).trans state.length
  · exact effect.agrees.external (by
      simp [Setup.effect, Effect.components, Write.component, Operand.component, Component.Covers])

end P256.Proofs.Signing.Wrapper.Hash.Absorb.Short
