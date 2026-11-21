import P256.Proofs.Nonce.Fill.Frame
import P256.Proofs.Nonce.Fill.Mathematics

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill.Tail

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Signing.Search
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)

structure Context [Bindings] (initial s : RamState) (orderAddress : BitVec 64)
    (state : Nonce.State) : Prop extends Frame initial s, Slots initial s where
  r13 : s.regValue .r13 = 32
  r15 : s.regValue .r15 = orderAddress
  generator : GeneratorAt s (initial.regValue .rdi) orderAddress (nextState state)

structure Decoded [Bindings] (initial s : RamState) (orderAddress : BitVec 64)
    (state : Nonce.State) : Prop extends Context initial s orderAddress state where
  rip : s.RIP = 0x10757a
  r12 : s.regValue .r12 = frameBase initial + 8
  integer : Nat256At s (frameBase initial + 8) (nextCandidate state).1

structure Compared [Bindings] (initial s : RamState) (orderAddress : BitVec 64)
    (state : Nonce.State) : Prop extends Context initial s orderAddress state where
  integer : Nat256At s (frameBase initial + 72) (nextCandidate state).1

theorem Context.after_registers [Bindings] {initial s t : RamState}
    {orderAddress : BitVec 64} {state : Nonce.State} {components : List Component}
    (input : Context initial s orderAddress state) (ready : ReadyToStep t)
    (agrees : AgreesExcept components s t)
    (noMemory : ∀ c ∈ components, ∀ a, ¬ c.Covers a)
    (sp : .reg 4 ∉ components) (r13 : .reg 13 ∉ components) (r15 : .reg 15 ∉ components)
    (hdf : Component.df ∉ components := by component_not_mem)
    (hmxcsr : Component.mxcsr ∉ components := by component_not_mem)
    (hfcw : Component.fcw ∉ components := by component_not_mem) :
    Context initial t orderAddress state := by
  have memory := agrees.external noMemory
  refine ⟨input.toFrame.after_registers ready agrees noMemory sp hdf hmxcsr hfcw,
    input.toSlots.of_memory_eq memory,
    (agrees.read (n := 64) (r := 13) r13).trans input.r13,
    (agrees.read (n := 64) (r := 15) r15).trans input.r15, ?_⟩
  simpa only [GeneratorAt, DrbgAt, Nat256At, memory] using input.generator

end P256.Proofs.Nonce.Fill.Tail
