import P256.Proofs.Nonce.Fill.Frame
import P256.Proofs.Nonce.Fill.Update.Setup

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill.Update

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)

structure Ready [Bindings] (initial s : RamState) (orderAddress : BitVec 64)
    (state : State) : Prop extends Frame initial s, Slots initial s where
  rip : s.RIP = 0x1073e6
  rdi : s.regValue .rdi = initial.regValue .rdi + 8
  count : s.regValue .rdx = 0
  generator : GeneratorAt s (initial.regValue .rdi) orderAddress (updateValue state)
  output : (registerRegion initial .rsi 32).HasBytes s.external (updateValue state).value

theorem arguments [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} {original state : State}
    (pre : Pre initial boundary orderAddress original)
    (input : Generated initial s orderAddress state) :
    ∃ fuel t, Advances boundary fuel s t ∧ Ready initial t orderAddress state := by
  obtain ⟨fuel, t, run, ready, _, effect⟩ := Setup.run boundary pre.outerBoundary s
    (readyToStep input.machine input.bindingsSupported) (Setup.code input.loaded) input.rip
  have agrees : AgreesExcept [.reg 6, .reg 2, .flags, .rip] s t := by
    simpa only [Setup.effect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.cons_append, List.nil_append] using effect.agrees
  have memory : t.external = s.external := agrees.external (by simp [Component.Covers])
  have frame := input.toFrame.after_registers ready agrees (by simp [Component.Covers]) (by simp)
  have writes := effect.writes
  change t.regValue .rsi = 8 ∧ t.regValue .rdx = BitVec.setWidth 64
    ((Operand.reg 2 : Operand 32).read s ^^^ (Operand.reg 2 : Operand 32).read s) at writes
  have values : t.regValue .rsi = 8 ∧ t.regValue .rdx = 0 :=
    ⟨writes.1, writes.2.trans (by simp only [BitVec.xor_self, BitVec.setWidth_zero]; rfl)⟩
  refine ⟨fuel, t, run, frame, input.toSlots.of_memory_eq memory, effect.rip,
    (agrees.read (n := 64) (r := 7) (by simp)).trans input.rdi, values.2, ?_, ?_⟩
  · simpa only [GeneratorAt, DrbgAt, Nat256At, memory] using input.generator
  · simpa only [memory] using input.output

end P256.Proofs.Nonce.Fill.Update
