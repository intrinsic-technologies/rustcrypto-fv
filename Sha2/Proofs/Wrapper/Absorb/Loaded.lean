import Sha2.Proofs.Wrapper.Absorb.Load
import Sha2.Proofs.Wrapper.Absorb.State

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper.Absorb

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.SHA256

theorem table_readable {v : Variant} {initial s : RamState} {inputs : Array Input}
    (call : ValidCall v.routine initial inputs) (state : MemoryWriteFrame initial s
      #v[outputRegion v.routine initial, Stack.region initial v.routine.minStackBytes])
    {table : MemoryRegion} (read : table ∈ readRegions initial inputs)
    (bounded : table.Bounded) (size : table.size = 8*inputs.size)
    (i : Fin inputs.size) {value : BitVec 64}
    (word : (tableEntry table i).Word64At initial.external value) :
    MemReadable s (BitVec.ofNat 64 (table.start + 8*i.val)) 8 := by
  have bound : table.start + table.size < 2^32 := bounded
  rw [size] at bound
  refine ⟨?_, Sha2.Proofs.Common.Memory.loadBytes_allocated
    (validCall_table_word_unchanged call state read bounded size i word)⟩
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := i.isLt; omega)]
  have := i.isLt
  omega

theorem load_slice {v : Variant} [Bindings] {initial s : RamState} {inputs : Array Input} {index : Nat}
    (ctx : Context (v := v) initial inputs) (input : LoopState (v := v) initial s inputs index) :
    ∃ t, Loaded (v := v) initial t inputs index := by
  let i : Fin inputs.size := ⟨index, input.remaining⟩
  have pointer : MemReadable s (initial.regValue .rdi + BitVec.ofNat 64 (8*index)) 8 := by
    have h := table_readable ctx.call input.frame
      (table := pointerTable initial inputs.size) (by simp [readRegions])
      ctx.call.pointerTableValid.2 rfl i (ctx.call.inputsInMemory i).2.1
    simpa only [pointerTable, registerRegion, BitVec.ofNat_add, BitVec.ofNat_toNat,
      BitVec.setWidth_eq, i] using h
  have length : MemReadable s (initial.regValue .rdx + BitVec.ofNat 64 (8*index)) 8 := by
    have h := table_readable ctx.call input.frame
      (table := lengthTable initial inputs.size) (by simp [readRegions])
      ctx.call.lengthTableValid.2 rfl i (ctx.call.inputsInMemory i).2.2.1
    simpa only [lengthTable, registerRegion, BitVec.ofNat_add, BitVec.ofNat_toNat,
      BitVec.setWidth_eq, i] using h
  have indexShift : s.regValue .r14 <<< (3 : Nat) = BitVec.ofNat 64 (8*index) := by
    rw [input.indexRegister, BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 64 index * BitVec.ofNat 64 8 = _
    rw [← BitVec.ofNat_mul, Nat.mul_comm]
  have stackAddr (offset : BitVec 64) : rspOf s + offset = stackPtr initial - (344-offset) :=
    stack_address input.rsp offset
  have pre : Load.Pre s v := {
    rip := input.rip
    stackPointer := by rw [stackAddr]; exact stack_readable (offset := 168) ctx input.toState (by decide) (by decide)
    stackLength := by rw [stackAddr]; exact stack_readable (offset := 160) ctx input.toState (by decide) (by decide)
    pointer := by rw [stackAddr, indexShift]; exact input.pointerTable ▸ pointer
    length := by rw [stackAddr, indexShift]; exact input.lengthTable ▸ length
    tail := by rw [stackAddr]; exact stack_readable (offset := 89) ctx input.toState (by decide) (by decide)
  }
  obtain ⟨fuel, t, run, ready, _, effect⟩ :=
    Load.run (returnBoundary initial) (validCall_returnBoundary ctx.machine ctx.call).2.2
      s (supportedMachine_readyToStep input.machine) (Load.code input.loaded) pre
  have frame : AgreesExcept [.reg 0, .reg 13, .reg 3, .reg 12, .rip] s t := effect.agrees
  have buffered := buffered_of_agrees ctx input.toBuffered run ready frame
    (by simp [Component.Covers]) (by simp)
  have writes := effect.writes
  simp only [Load.effect, Write.AllHold, Operand.read] at writes
  change t.regValue .rax = memLoad s.external (rspOf s + 184) 64 ∧
    t.regValue .r13 = memLoad s.external
      (memLoad s.external (rspOf s + 176) 64 + (s.regValue .r14 <<< (3 : Nat))) 64 ∧
    t.regValue .rbx = memLoad s.external
      (memLoad s.external (rspOf s + 184) 64 + (s.regValue .r14 <<< (3 : Nat))) 64 ∧
    t.regValue .r12 = (memLoad s.external (rspOf s + 255) 8).setWidth 64 at writes
  refine ⟨t, {
    toIteration := ⟨buffered,
      (frame.read (n := 64) (r := 14) (by simp)).trans input.indexRegister,
      (frame.read (n := 64) (r := 15) (by simp)).trans input.countRegister, input.remaining⟩
    rip := effect.rip
    source := ?_
    length := ?_
    position := ?_
  }⟩
  · rw [writes.2.1, stackAddr, indexShift]
    change memLoad s.external (memLoad s.external (stackPtr initial - 168) 64 + BitVec.ofNat 64 (8*index)) 64 = _
    rw [input.pointerTable]
    exact validCall_input_pointer ctx.call input.frame i
  · rw [writes.2.2.1, stackAddr, indexShift]
    change memLoad s.external (memLoad s.external (stackPtr initial - 160) 64 + BitVec.ofNat 64 (8*index)) 64 = _
    rw [input.lengthTable]
    exact validCall_input_length ctx.call input.frame i
  · rw [writes.2.2.2, stackAddr]
    change (memLoad s.external (stackPtr initial - 89) 8).setWidth 64 = _
    have bytes : Bytes s.external (stackPtr initial - 89) 1
        (storedByte (BitVec.ofNat 8 ((prefixMessage inputs index).size % 64))) := by
      intro j hj
      have eq : j = 0 := by omega
      subst j
      simpa [storedByte, BitVec.toNat_ofNat, Nat.mod_eq_of_lt
        (show (prefixMessage inputs index).size % 64 < 256 by omega)] using input.tailLength
    have word := Bytes.memLoad (n := 8) bytes (by decide) (by decide)
    rw [word]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega

end Sha2.Proofs.Wrapper.Absorb
