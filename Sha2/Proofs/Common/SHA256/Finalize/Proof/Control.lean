import Sha2.Proofs.Common.SHA256.Finalize.Proof.Frame

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Finalize

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

theorem branch [Bindings] {L : Layout} {initial before s : RamState}
    {n reserve : Nat} {regions : Vector MemoryRegion n} {message : ByteArray}
    (ctx : Context L initial regions reserve) (input : Padded L initial before s regions message) :
    ∃ t, Working L initial before t regions message (compressBlocks L.hashVariant.initialHash message) ∧
      t.RIP = (if message.size % 64 < 56 then L.length else L.firstHead) ∧
      (⟨(L.buffer (L.sp initial)).toNat, 64⟩ : MemoryRegion).HasBytes t.external (paddedBuffer message) := by
  obtain ⟨_, t, run, ready, _, effect⟩ := ctx.blocks.branch s
    (supportedMachine_readyToStep input.state.machine) (ctx.code.loaded .branch s input.state.loaded) input.rip
  have memory := effect.agrees.external (by
    cases h : L.variant <;>
      simp [Branch.effect, Effect.components, Write.component, Operand.component, Component.Covers])
  have preserved := input.toPreserved.of_agrees ctx run ready effect.agrees
    (by
      intro c hc a ha
      cases c <;> simp only [Component.Covers] at ha
      all_goals cases h : L.variant <;> simp [Branch.effect, h, Effect.components, Write.component, Operand.component] at hc)
    (by
      intro r _ kept
      cases h : L.variant <;>
        simp_all [Branch.effect, Effect.components, Write.component, Operand.component, Variant.clobbered, Variant.padReg, Variant.hashReg,
          Variant.registers, Blocks.Length.Registers.tail, Blocks.Length.Registers.blocks])
    (by
      cases h : L.variant <;>
        simp [Branch.effect, Effect.components, Write.component, Operand.component])
  refine ⟨t, ⟨⟨preserved, ?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
  · simpa only [HashStateAt, memory] using input.hashWords
  · intro notFirst
    by_cases reset : L.variant = .reset
    · have word := effect.writes
      simp only [Branch.effect, reset, ↓reduceIte] at word
      change (.reg (3#5) : Operand 64).read t = stackPtr s + 64 at word
      rw [input.rsp] at word
      simpa [Layout.hash, Layout.buffer, reset, Variant.hashReg, Variant.buffer, Blocks.Zero.Offset.value] using word
    · exact (effect.agrees.read (n := 64) (r := L.variant.hashReg) (by
        cases h : L.variant <;> simp_all [Branch.effect, Effect.components,
          Variant.hashReg])).trans
        (input.hashPointer (by cases h : L.variant <;> simp_all [Variant.needsHashPointer]))
  · exact (effect.agrees.read (n := 64) (r := L.variant.registers.tail) (by
      cases h : L.variant <;> simp [Branch.effect, Effect.components,
        Write.component, Operand.component, Variant.registers, Blocks.Length.Registers.tail])).trans input.tailLength
  · exact (effect.agrees.read (n := 64) (r := L.variant.registers.blocks) (by
      cases h : L.variant <;> simp [Branch.effect, Effect.components,
        Write.component, Operand.component, Variant.registers, Blocks.Length.Registers.blocks])).trans input.blocks
  · have rip := effect.rip
    change t.RIP = (if ((.reg L.variant.padReg : Operand 64).read s).toNat < 8 then
      L.branch + BitVec.ofNat 64 (Branch.bytes L.variant L.branchDisp).length else
      branchTarget (L.branch + BitVec.ofNat 64 (Branch.comparisonBytes L.variant).length)
        6 (L.branchDisp.signExtend 64)) at rip
    rw [input.paddingLength, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 63 - message.size % 64 < 2^64),
      ctx.flow.branchFallthrough, ctx.flow.branchTaken] at rip
    have rem := Nat.mod_lt message.size (by decide : 0 < 64)
    by_cases small : message.size % 64 < 56
    · simpa only [small, ite_true, show ¬ 63 - message.size % 64 < 8 by omega, ite_false] using rip
    · simpa only [small, ite_false, show 63 - message.size % 64 < 8 by omega, ite_true] using rip
  · simpa only [memory] using input.bytes

theorem length [Bindings] {L : Layout} {initial before s : RamState}
    {n reserve : Nat} {regions : Vector MemoryRegion n} {message : ByteArray} {hash : Array UInt32}
    (ctx : Context L initial regions reserve) (input : Working L initial before s regions message hash)
    (rip : s.RIP = L.length)
    (prefixBytes : (⟨(L.buffer (L.sp initial)).toNat, 56⟩ : MemoryRegion).HasBytes
      s.external (finalPrefix message)) :
    ∃ t, LengthReady L initial before t regions message hash := by
  have inside : BlockInProgram L.length L.variant.registers.length := by
    have h := ctx.code.inside .length
    have size : ∀ regs, (Blocks.Length.bytes regs).length = regs.length := by
      intro regs
      cases regs <;> rfl
    change BlockInProgram L.length (Blocks.Length.bytes L.variant.registers).length at h
    rwa [size] at h
  obtain ⟨_, t, run, ready, _, effect⟩ := Blocks.Length.run L.length L.variant.registers
    (returnBoundary initial) ctx.outside inside s
    (supportedMachine_readyToStep input.state.machine) (ctx.code.loaded .length s input.state.loaded) rip
  have memory := effect.agrees.external (by
    cases h : L.variant <;> simp [Blocks.Length.effect, Variant.registers,
      Blocks.Length.Registers.preShifted, Effect.components, Write.component, Operand.component, Component.Covers])
  have preserved := input.toPreserved.of_agrees ctx run ready effect.agrees
    (by
      intro c hc a ha
      cases c <;> simp only [Component.Covers] at ha
      all_goals cases h : L.variant <;> simp [Blocks.Length.effect, h, Variant.registers,
        Blocks.Length.Registers.preShifted, Effect.components, Write.component, Operand.component] at hc)
    (by
      intro r _ kept
      cases h : L.variant <;> simp_all [Blocks.Length.effect, Variant.registers,
        Blocks.Length.Registers.preShifted, Effect.components, Write.component, Operand.component, Variant.clobbered, Variant.padReg, Variant.hashReg,
        Blocks.Length.Registers.tail, Blocks.Length.Registers.blocks])
    (by
      cases h : L.variant <;> simp [Blocks.Length.effect, Variant.registers,
        Blocks.Length.Registers.preShifted, Effect.components, Write.component, Operand.component])
  refine ⟨t, ⟨⟨preserved, ?_, ?_⟩, effect.rip.trans ctx.flow.length, ?_, ?_⟩⟩
  · simpa only [HashStateAt, memory] using input.hashWords
  · intro notFirst
    exact (effect.agrees.read (n := 64) (r := L.variant.hashReg) (by
      cases h : L.variant <;> simp_all [Blocks.Length.effect, Effect.components,
        Write.component, Operand.component, Variant.hashReg, Variant.registers,
        Blocks.Length.Registers.preShifted, Blocks.Length.Registers.tail, Blocks.Length.Registers.blocks])).trans
      (input.hashPointer notFirst)
  · simpa only [memory] using prefixBytes
  · have tail := input.tailLength
    have count := input.blocks
    have word := effect.writes
    have math := Sha2.Proofs.Wrapper.Hash.Finalize.length_word message.size
    cases h : L.variant <;>
      simp only [Blocks.Length.effect, h, Variant.registers, Blocks.Length.Registers.preShifted,
        Blocks.Length.Registers.tail, Blocks.Length.Registers.blocks, ↓reduceIte,
        List.nil_append, Write.AllHold, Operand.read] at word tail count ⊢
    all_goals simp_all [countValue, Variant.registers, Blocks.Length.Registers.preShifted,
      Write.AllHold, Operand.read]

end Sha2.Proofs.Common.SHA256.Finalize
