import Sha2.Proofs.Wrapper.Hash.Finalize.Mathematics
import Sha2.Proofs.Wrapper.Memory
import Sha2.Proofs.Wrapper.Hash.Padding.Branch
import Sha2.Proofs.Wrapper.Hash.Padding.Length
import Sha2.Proofs.Wrapper.Hash.Padding.Zero
import Sha2.Proofs.Common.Memory.Bytes

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper.Hash.Finalize

open Sha2.Spec Sha2.Proofs.Program Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.SHA256 Sha2.Proofs.Common.Machine

theorem branch [Bindings] {v : Variant} {initial s : RamState} {inputs : Array Input} {message : ByteArray}
    (ctx : Context initial inputs v)
    (input : Padded initial s message v) :
    ∃ t, Working initial t message (compressBlocks v.initialHash message) v ∧
      t.RIP = (if message.size % 64 < 56 then (v.pc 0x2b4) else (v.pc 0x206)) ∧
      (⟨(stackPtr initial - 344).toNat, 64⟩ : MemoryRegion).HasBytes t.external (paddedBuffer message) := by
  obtain ⟨t, run, ready, rip, frame⟩ := Padding.branch
    (supportedMachine_readyToStep input.machine) input.loaded input.rip
    (validCall_returnBoundary ctx.machine ctx.call).2.2
  have memory := frame.external (by simp [Component.Covers])
  have preserved := Wrapper.preserved_of_agrees ctx input.toPreserved run ready frame
    (by simp [Wrapper.LocalWrites, Component.Covers]) (by simp)
  refine ⟨t, ⟨⟨preserved, ?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
  · simpa only [HashStateAt, memory] using input.hashWords
  · exact (frame.read (n := 64) (r := 14) (by simp)).trans input.hashPointer
  · exact (frame.read (n := 64) (r := 12) (by simp)).trans input.blocks
  · exact (frame.read (n := 64) (r := 15) (by simp)).trans input.tailLength
  · rw [rip, input.paddingLength, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 63 - message.size % 64 < 2^64)]
    by_cases small : message.size % 64 < 56
    · rw [ite_eq_right (by omega : ¬ 63 - message.size % 64 < 8), ite_eq_left small]
    · rw [ite_eq_left (by omega : 63 - message.size % 64 < 8), ite_eq_right small]
  · simpa only [memory] using input.bytes

theorem length [Bindings] {v : Variant} {initial s : RamState} {inputs : Array Input} {message : ByteArray}
    {hash : Array UInt32} (ctx : Context initial inputs v)
    (input : Working initial s message hash v) (rip : s.RIP = (v.pc 0x2b4))
    (prefixBytes : (⟨(stackPtr initial - 344).toNat, 56⟩ : MemoryRegion).HasBytes
      s.external (finalPrefix message)) :
    ∃ t, LengthReady initial t message hash v := by
  obtain ⟨_, t, run, ready, _, effect⟩ :=
    Padding.Length.run (v := v) (returnBoundary initial) (validCall_returnBoundary ctx.machine ctx.call).2.2
      s (supportedMachine_readyToStep input.machine) (Padding.Length.code (v := v) input.loaded) rip
  have frame := effect.agrees
  have memory := frame.external (by simp [Padding.Length.effect, Effect.components,
    Write.component, Operand.component, Component.Covers])
  have preserved := Wrapper.preserved_of_agrees ctx input.toPreserved run ready frame
    (by simp [Padding.Length.effect, Effect.components, Write.component,
      Operand.component, Wrapper.LocalWrites, Component.Covers])
    (by simp [Padding.Length.effect, Effect.components, Write.component, Operand.component])
    (by simp [Padding.Length.effect, Effect.components, Write.component, Operand.component])
  refine ⟨t, ⟨⟨preserved, ?_, ?_⟩, effect.rip, ?_, ?_⟩⟩
  · simpa only [HashStateAt, memory] using input.hashWords
  · exact (frame.read (n := 64) (r := 14)
      (by simp [Padding.Length.effect, Effect.components, Write.component, Operand.component])).trans input.hashPointer
  · simpa only [memory] using prefixBytes
  · have output := effect.writes.2
    change t.regValue .r15 = Common.Instructions.bswap64
      (((s.regValue .r15).setWidth 32 <<< 3).setWidth 64 ||| (s.regValue .r12 <<< 9)) at output
    rw [output, input.tailLength, input.blocks]
    congr 1
    exact length_word message.size

end Sha2.Proofs.Wrapper.Hash.Finalize
