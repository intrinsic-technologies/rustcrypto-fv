import Hkdf.Proofs.Common.Machine.Boundary
import Hkdf.Proofs.Standard.Update.Control
import Hkdf.Proofs.Standard.Update.Load
import Hkdf.Proofs.Standard.Update.Prepare

set_option autoImplicit false

namespace Hkdf.Proofs.Standard.Update

open Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Machine

theorem buffered_of_noMem [Bindings] {initial s t : RamState}
    {salt : Option ByteArray} {inputs : Array Input} {message : ByteArray} {fuel : Nat}
    {components : List Component} (ctx : Context initial salt inputs)
    (state : Buffered initial s salt message)
    (run : Advances (returnBoundary initial) fuel s t) (ready : ReadyToStep t)
    (frame : AgreesExcept components s t)
    (noMem : ∀ c ∈ components, ∀ a, ¬ c.Covers a)
    (rsp : Component.reg 4 ∉ components) (df : Component.df ∉ components) :
    Buffered initial t salt message := by
  refine ⟨Preserved.of_noMem ctx state.toPreserved run ready frame noMem rsp df, ?_⟩
  apply state.hmac.of_copy
  intro i hi
  rw [frame.external noMem]

theorem start [Bindings] {initial s : RamState}
    {salt : Option ByteArray} {inputs : Array Input}
    (ctx : Context initial salt inputs) (ready : ReadyToStep s)
    (initialized : Initialized initial s salt) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ ReadyToStep t ∧
      ((inputs.size = 0 ∧ Completed initial t salt inputs) ∨
        LoopState initial t salt inputs 0) := by
  have outside := (returnBoundary_valid ctx).2.2
  have readable : MemReadable s (stackPtr s + 8) 8 := by
    change MemReadable s (rspOf s + BitVec.ofNat 64 8) 8
    rw [stack_address initialized.rsp (offset := 8) (by decide)]
    exact stack_readable ctx initialized.toState (by decide) (by decide)
  obtain ⟨u, run, readyU, target, frame⟩ := dispatch ready initialized.loaded outside
    initialized.rip readable
  have buffered := buffered_of_noMem ctx initialized.toBuffered run readyU frame
    (by simp [Component.Covers]) (by simp) (by simp)
  have word : memLoad s.external (stackPtr s + 8) 64 = initial.regValue .rsi := by
    change memLoad s.external (s.regValue .rsp + 8) 64 = _
    rw [initialized.rsp]
    exact initialized.inputCount
  have zero : memLoad s.external (stackPtr s + 8) 64 = 0 ↔ inputs.size = 0 := by
    rw [word]
    constructor
    · intro h
      rw [← ctx.call.countArgumentMatchesInputs, h]
      rfl
    · intro h
      apply BitVec.eq_of_toNat_eq
      rw [ctx.call.countArgumentMatchesInputs, h]
      rfl
  simp only [zero] at target
  by_cases empty : inputs.size = 0
  · have all : concatenation inputs = ByteArray.empty := by
      have eq : inputs = #[] := Array.eq_empty_of_size_eq_zero empty
      rw [eq]
      rfl
    exact ⟨2, u, run, readyU, .inl ⟨empty, ⟨by simpa only [all] using buffered,
      by simpa only [empty, ↓reduceIte] using target⟩⟩⟩
  · have ripU : u.RIP = 0x10160d := by simpa only [empty, ↓reduceIte] using target
    obtain ⟨t, next, readyT, ripT, index, copy, frameT⟩ :=
      enter_loop readyU buffered.loaded outside ripU
    have final := buffered_of_noMem ctx buffered next readyT frameT
      (by simp [Component.Covers]) (by simp) (by simp)
    refine ⟨5, t, run.trans next, readyT, .inr ?_⟩
    exact ⟨by simpa only [Hkdf.Proofs.Common.prefixConcatenation_zero] using final,
      ripT, index, copy, by omega⟩

theorem table_readable {initial s : RamState} {salt : Option ByteArray}
    {inputs : Array Input} (call : ValidExtractCall hkdfSha256Extract initial salt inputs)
    (frame : MemoryWriteFrame initial s #v[Stack.region initial hkdfSha256Extract.minStackBytes])
    {table : MemoryRegion}
    (member : table ∈ (pointerTable initial inputs.size :: lengthTable initial inputs.size ::
      (inputs.map Input.region).toList ++ salt.toList.map (extractSaltRegion initial)))
    (bounded : table.Bounded) (size : table.size = 8 * inputs.size)
    (i : Fin inputs.size) {value : BitVec 64}
    (word : (tableEntry table i).Word64At initial.external value) :
    MemReadable s (BitVec.ofNat 64 (table.start + 8 * i.val)) 8 := by
  have bound : table.start + table.size < 2^32 := bounded
  rw [size] at bound
  refine ⟨?_, Hkdf.Proofs.Common.Memory.loadBytes_allocated
    (Hkdf.Proofs.Common.extract_table_word_unchanged call frame member bounded size i word)⟩
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := i.isLt; omega)]
  have := i.isLt
  omega

theorem load_input [Bindings] {initial s : RamState} {salt : Option ByteArray}
    {inputs : Array Input} {index : Nat} (ctx : Context initial salt inputs)
    (input : LoopState initial s salt inputs index) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ ReadyToStep t ∧
      Buffered initial t salt (Hkdf.Proofs.Common.prefixConcatenation inputs index) ∧
      t.RIP = 0x101664 ∧ t.regValue .r13 = (inputs[index]'input.remaining).address ∧
      t.regValue .rbx = BitVec.ofNat 64 (inputs[index]'input.remaining).bytes.size ∧
      t.regValue .r15 = BitVec.ofNat 64
        ((Hkdf.Proofs.Common.prefixConcatenation inputs index).size % 64) ∧
      t.regValue .r14 = BitVec.ofNat 64 index ∧ t.regValue .r12 = 0x10dd60 := by
  let i : Fin inputs.size := ⟨index, input.remaining⟩
  have pointer : MemReadable s (initial.regValue .rdi + BitVec.ofNat 64 (8 * index)) 8 := by
    have h := table_readable ctx.call input.frame
      (table := pointerTable initial inputs.size) (by simp)
      (ctx.call.pointerTableValid (by have := input.remaining; omega)) rfl i
      (ctx.call.ikmInMemory i).1
    simpa only [pointerTable, registerRegion, BitVec.ofNat_add, BitVec.ofNat_toNat,
      BitVec.setWidth_eq, i] using h
  have length : MemReadable s (initial.regValue .rdx + BitVec.ofNat 64 (8 * index)) 8 := by
    have h := table_readable ctx.call input.frame
      (table := lengthTable initial inputs.size) (by simp)
      (ctx.call.lengthTableValid (by have := input.remaining; omega)) rfl i
      (ctx.call.ikmInMemory i).2.1
    simpa only [lengthTable, registerRegion, BitVec.ofNat_add, BitVec.ofNat_toNat,
      BitVec.setWidth_eq, i] using h
  have shift : s.regValue .r14 <<< (3 : Nat) = BitVec.ofNat 64 (8 * index) := by
    rw [input.indexRegister, BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 64 index * BitVec.ofNat 64 8 = _
    rw [← BitVec.ofNat_mul, Nat.mul_comm]
  have sp : rspOf s = frameBase initial := input.rsp
  have slot (offset : Nat) (small : offset ≤ 520) :
      rspOf s + BitVec.ofNat 64 offset =
        stackPtr initial - BitVec.ofNat 64 (520 - offset) :=
    stack_address input.rsp small
  have pre : LoadPre s := {
    rip := input.rip
    pointerSlot := by
      change MemReadable s (rspOf s + BitVec.ofNat 64 104) 8
      rw [slot 104 (by decide)]
      exact stack_readable ctx input.toState (by decide) (by decide)
    lengthSlot := by
      change MemReadable s (rspOf s + BitVec.ofNat 64 112) 8
      rw [slot 112 (by decide)]
      exact stack_readable ctx input.toState (by decide) (by decide)
    pointerEntry := by
      rw [sp, input.pointerTable, shift]
      exact pointer
    lengthEntry := by
      rw [sp, input.lengthTable, shift]
      exact length
    tailSlot := by
      change MemReadable s (rspOf s + BitVec.ofNat 64 183) 1
      rw [slot 183 (by decide)]
      exact stack_readable ctx input.toState (by decide) (by decide)
  }
  obtain ⟨fuel, t, run, ready, _, effect⟩ := load_run (returnBoundary initial)
    (returnBoundary_valid ctx).2.2 s
    (Hkdf.Proofs.Common.Machine.supportedMachine_readyToStep input.machine)
    (programText_slice (programLoaded_codeIn input.loaded) 0x1649 loadBytes
      (by decide +kernel) (by decide +kernel)) pre
  have frame : AgreesExcept [.reg 0, .reg 13, .reg 3, .reg 15, .rip] s t := effect.agrees
  have buffered := buffered_of_noMem ctx input.toBuffered run ready frame
    (by simp [Component.Covers]) (by simp) (by simp)
  have writes := effect.writes
  change t.regValue .rax = memLoad s.external (rspOf s + 112) 64 ∧
    t.regValue .r13 = memLoad s.external
      (memLoad s.external (rspOf s + 104) 64 + (s.regValue .r14 <<< (3 : Nat))) 64 ∧
    t.regValue .rbx = memLoad s.external
      (memLoad s.external (rspOf s + 112) 64 + (s.regValue .r14 <<< (3 : Nat))) 64 ∧
    t.regValue .r15 = (memLoad s.external (rspOf s + 183) 8).setWidth 64 at writes
  refine ⟨fuel, t, run, ready, buffered, effect.rip, ?_, ?_, ?_,
    (frame.read (n := 64) (r := 14) (by simp)).trans input.indexRegister,
    (frame.read (n := 64) (r := 12) (by simp)).trans input.copyRegister⟩
  · rw [writes.2.1, sp, input.pointerTable, shift]
    exact Hkdf.Proofs.Common.extract_input_pointer ctx.call input.frame i
  · rw [writes.2.2.1, sp, input.lengthTable, shift]
    exact Hkdf.Proofs.Common.extract_input_length ctx.call input.frame i
  · rw [writes.2.2.2]
    have tail := input.hmac.inner.tailLength
    have size : (Hkdf.Proofs.Common.HMAC.xorPad
        (Hkdf.Proofs.Common.HMAC.keyBlock (saltKey salt)) 0x36 ++
        Hkdf.Proofs.Common.prefixConcatenation inputs index).size % 64 =
        (Hkdf.Proofs.Common.prefixConcatenation inputs index).size % 64 := by
      rw [ByteArray.size_append, Hkdf.Proofs.Common.HMAC.xorPad_keyBlock_size]
      omega
    rw [size] at tail
    have addr : hmacBase initial + 63 = rspOf s + 183 := by
      rw [sp, hmacBase, BitVec.add_assoc]
      rfl
    rw [addr] at tail
    have bytes : Bytes s.external (rspOf s + 183) 1
        (storedByte (BitVec.ofNat 8
          ((Hkdf.Proofs.Common.prefixConcatenation inputs index).size % 64))) := by
      intro j hj
      have zero : j = 0 := by omega
      subst j
      simpa [storedByte, BitVec.toNat_ofNat, Nat.mod_eq_of_lt
        (show (Hkdf.Proofs.Common.prefixConcatenation inputs index).size % 64 < 256 by omega)] using tail
    have word := Bytes.memLoad (n := 8) bytes (by decide) (by decide)
    rw [word]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega


theorem absorb_empty [Bindings] {initial s : RamState}
    {salt : Option ByteArray} {inputs : Array Input}
    (ctx : Context initial salt inputs) (ready : ReadyToStep s)
    (initialized : Initialized initial s salt) (empty : inputs.size = 0) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ ReadyToStep t ∧
      Completed initial t salt inputs := by
  obtain ⟨fuel, t, run, readyT, result⟩ := start ctx ready initialized
  rcases result with ⟨_, completed⟩ | loop
  · exact ⟨fuel, t, run, readyT, completed⟩
  · have remaining := loop.remaining
    omega

end Hkdf.Proofs.Standard.Update
