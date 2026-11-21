import Sha2.Proofs.Wrapper512.Hash.Finalize.Length.Machine
import Sha2.Proofs.Wrapper512.Hash.Finalize.Length.Mathematics
import Sha2.Proofs.Wrapper512.Absorb.Memory
import Sha2.Proofs.Common.Machine.CallMemory

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Hash.Finalize.Length

open Sha2.Spec Sha2.Proofs.Program Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.SHA512 Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.Instructions

attribute [local irreducible] bswap64

macro "length_form_cases" f:term:max : tactic => `(tactic|
  first |
    rcases ($f) with _ | _ | stage | second | second
    all_goals first
      | have h : stage = 0 ∨ stage = 1 ∨ stage = 2 := by omega
        rcases h with h | h | h <;> subst stage
      | cases second
      | skip)

macro "length_frame" : tactic => `(tactic|
  (simp only [Machine.effect, Effect.components, Write.component, Operand.component,
    countsShifted, ↓reduceIte, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, reduceCtorEq] <;> decide +kernel))

theorem operand_read_register (r : Syntax.Reg) (s : RamState) :
    (Operand.reg (Machine.reg r) : Operand 64).read s = s.regValue r := by
  cases r <;> rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem length_words {v : Variant} {form : Form} {s t : RamState} {message : ByteArray}
    (tailLength : s.regValue (tailRegister v form) = BitVec.ofNat 64 (message.size % 128))
    (blocks : s.regValue (lowCountRegister v form) = lowCountValue form message)
    (blocksHigh : s.regValue (highCountRegister v form) = highCountValue form message)
    (writes : Write.AllHold t (Machine.effect v form s).writes) :
    t.regValue (lowLengthRegister v form) = bswap64 (BitVec.ofNat 64 (8 * message.size)) ∧
    t.regValue (highCountRegister v form) = bswap64 (BitVec.ofNat 64 ((8 * message.size) / 2^64)) := by
  have tailRead : (Operand.reg (Machine.reg (tailRegister v form)) : Operand 64).read s =
      BitVec.ofNat 64 (message.size % 128) := by simpa only [operand_read_register] using tailLength
  have tailRead32 : (Operand.reg (Machine.reg (tailRegister v form)) : Operand 32).read s =
      (BitVec.ofNat 64 (message.size % 128)).setWidth 32 := congrArg (BitVec.setWidth 32) tailRead
  have blocksRead : (Operand.reg (Machine.reg (lowCountRegister v form)) : Operand 64).read s =
      lowCountValue form message := by simpa only [operand_read_register] using blocks
  have highRead : (Operand.reg (Machine.reg (highCountRegister v form)) : Operand 64).read s =
      highCountValue form message := by simpa only [operand_read_register] using blocksHigh
  constructor
  · have low32 : (((BitVec.ofNat 64 (message.size % 128)).setWidth 32 <<< 3).setWidth 64 |||
        (BitVec.ofNat 64 (message.size / 128) <<< 10)) = BitVec.ofNat 64 (8 * message.size) := by
      have cast : ((BitVec.ofNat 64 (message.size % 128)).setWidth 8).setWidth 32 =
          (BitVec.ofNat 64 (message.size % 128)).setWidth 32 := by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow]
        have bound := Nat.mod_lt message.size (by decide : 0 < 128)
        omega
      rw [← cast]
      exact low_word _
    length_form_cases form <;> cases v
    all_goals first
      | have h := writes.2.2
        apply h.trans
        apply congrArg bswap64
        rw [tailRead, blocksRead]
        exact low_word _
      | have h := writes.1
        apply h.trans
        apply congrArg bswap64
        simp only [lowLengthRegister, tailRegister, reduceCtorEq, ↓reduceIte] at tailRead32 ⊢
        rw [tailRead32, blocksRead]
        exact low32
  · length_form_cases form <;> cases v
    all_goals first
      | have h := writes.1
        apply h.trans
        apply congrArg bswap64
        rw [highRead, blocksRead]
        exact high_word _
      | have h := writes.2
        apply h.trans
        apply congrArg bswap64
        rw [highRead]
        exact high_word _

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem run_local [Bindings] {v : Variant} {form : Form} {initial s : RamState} {inputs : Array Input}
    {message : ByteArray} {hash : Array UInt64} (ctx : Context v initial inputs form)
    (input : Working v initial s message hash form)
    (rip : s.RIP = v.pc (lengthOffset v form) form)
    (prefixBytes : (⟨(stackPtr initial - BitVec.ofNat 64 form.finalMemory.buffer).toNat, 112⟩ : MemoryRegion).HasBytes
      s.external (finalPrefix message)) :
    ∃ n t, Advances (returnBoundary initial) n s t ∧
      AgreesExcept (Machine.effect v form s).components s t ∧
      LengthReady v initial t message hash form ∧
      MemoryWriteFrame s t #v[Stack.region initial form.stackBytes] ∧
      (¬ form.isTerminal → v.countValue form initial t = v.countValue form initial s) := by
  obtain ⟨n, t, execution, ready, _, effect⟩ :=
    Machine.run_local (form := form) (returnBoundary initial)
      ((valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2)
      s (supportedMachine_readyToStep input.machine) (Machine.code_local input.loaded) rip
  have frame := effect.agrees
  have memory := frame.external (by
    length_form_cases form <;> cases v <;>
      simp [Machine.effect, Machine.reg, countsShifted, lowLengthRegister, highCountRegister, lowCountRegister, Syntax.Reg.fin, Effect.components, Write.component, Operand.component, Component.Covers])
  have localWrites : Absorb.LocalWrites initial (Machine.effect v form s).components form := by
    length_form_cases form <;> cases v <;> simp [Machine.effect, Machine.reg, countsShifted,
      lowLengthRegister, highCountRegister, lowCountRegister, Syntax.Reg.fin, Effect.components,
      Write.component, Operand.component, Absorb.LocalWrites, Component.Covers]
  have preserved := Absorb.preserved_of_agrees ctx input.toPreserved execution ready frame localWrites
    (by length_form_cases form <;> cases v <;> length_frame)
    (by length_form_cases form <;> cases v <;> length_frame)
    (by intro h; subst form; cases v <;> length_frame)
    (by intro h; subst form; left; cases v <;> length_frame)
  have stackFrame : MemoryWriteFrame s t #v[Stack.region initial form.stackBytes] :=
    frame.memoryWriteFrame (localWrites.stack ctx)
  have countKept : ¬ form.isTerminal → v.countValue form initial t = v.countValue form initial s := by
    intro nonterminal
    cases form with
    | slices | digest => exact (nonterminal trivial).elim
    | reset stage =>
      have stages : stage = 0 ∨ stage = 1 := by
        have bound := stage.isLt
        simp only [Form.isTerminal] at nonterminal
        omega
      rcases stages with h | h <;> subst stage
      all_goals cases v <;> exact frame.read (n := 64) (r := 12) (by length_frame)
    | finalizeIntoReset second =>
      cases second
      · cases v <;> first
          | exact frame.read (n := 64) (r := 12) (by length_frame)
          | exact frame.read (n := 64) (r := 15) (by length_frame)
      · exact (nonterminal rfl).elim
    | traitFinalizeIntoReset second =>
      cases second
      · have kept : memLoad t.external (stackPtr initial - 640) 64 =
            memLoad s.external (stackPtr initial - 640) 64 := by rw [memory]
        cases v <;> exact kept
      · exact (nonterminal rfl).elim
  refine ⟨n, t, execution, frame, ⟨⟨preserved, ?_, ?_⟩, effect.rip, ?_, ?_, ?_⟩, stackFrame, countKept⟩
  · simpa only [HashStateAt, memory] using input.hashWords
  · length_form_cases form <;> cases v
    all_goals first
      | trivial
      | exact (frame.read (n := 64) (r := 14) (by length_frame)).trans input.hashPointer
      | exact (frame.read (n := 64) (r := 3) (by length_frame)).trans input.hashPointer
      | exact ⟨(frame.read (n := 64) (r := 3) (by length_frame)).trans input.hashPointer.1,
          (frame.read (n := 64) (r := 5) (by length_frame)).trans input.hashPointer.2⟩
      | exact ⟨(frame.read (n := 64) (r := 5) (by length_frame)).trans input.hashPointer.1,
          (frame.read (n := 64) (r := 13) (by length_frame)).trans input.hashPointer.2⟩
  · simpa only [memory] using prefixBytes
  · exact (length_words input.tailLength input.blocks input.blocksHigh effect.writes).1
  · exact (length_words input.tailLength input.blocks input.blocksHigh effect.writes).2

theorem run [Bindings] {v : Variant} {form : Form} {initial s : RamState} {inputs : Array Input}
    {message : ByteArray} {hash : Array UInt64} (ctx : Context v initial inputs form)
    (input : Working v initial s message hash form) (rip : s.RIP = v.pc (if form = .slices then 0x32a else 0x243) form)
    (prefixBytes : (⟨(stackPtr initial - 600).toNat, 112⟩ : MemoryRegion).HasBytes
      s.external (finalPrefix message))
    (eligible : form = .slices ∨ form = .digest := by first | assumption | simp) :
    ∃ t, LengthReady v initial t message hash form := by
  rcases eligible with h | h <;> subst form
  all_goals obtain ⟨_, t, _, _, output, _, _⟩ := run_local ctx input rip prefixBytes
  all_goals exact ⟨t, output⟩

end Sha2.Proofs.Wrapper512.Hash.Finalize.Length
