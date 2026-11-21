import Base16ct.Proofs.EncodeStr.Lower.Encoding
import X86Proofs.Program.Entry
import X86Proofs.Program.Execution
import X86Proofs.Program.ReadWrite.WriteFrame
import X86Proofs.Step.Sse

namespace Base16ct.Proofs.EncodeStr.Lower

open Base16ct.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem program_text_slice {s : RamState} (hCode : CodeIn Extracted.programImage s)
    (offset count : Nat) (h : offset + count ≤ Extracted.textBytes.size) :
    CodeIn (codeRange (Extracted.textAddress + BitVec.ofNat 64 offset)
      (Extracted.textBytes.toListFrom offset count)) s :=
  hCode.slice_of_section
    (sec := ⟨Extracted.textAddress, Extracted.textBytes⟩)
    (by simp [Extracted.programSections]) offset count h

theorem text_address_in_program (offset : Nat) (h : offset < Extracted.textBytes.size) :
    InProgram (Extracted.textAddress + BitVec.ofNat 64 offset) := by
  have hLength : offset < Extracted.textBytes.toList.length := by
    rwa [chunked_toList_length]
  refine ⟨Extracted.textBytes.toList[offset], ?_⟩
  change _ ∈ Extracted.programSections.flatMap ImageSection.toCodeMap
  apply List.mem_flatMap.mpr
  refine ⟨⟨Extracted.textAddress, Extracted.textBytes⟩,
    by simp [Extracted.programSections], ?_⟩
  exact mem_codeRange _ _ offset hLength

theorem text_address_ne_return {boundary : ReturnBoundary} (hOutside : ¬ InProgram boundary.rip)
    (offset : Nat) (h : offset < Extracted.textBytes.size) :
    Extracted.textAddress + BitVec.ofNat 64 offset ≠ boundary.rip := by
  intro hEq
  exact hOutside (hEq ▸ text_address_in_program offset h)

def writableRegions (initial : RamState) (capacity : Nat) : Vector MemoryRegion 2 :=
  #v[outputRegion initial capacity, Stack.region initial base16ctLowerEncodeStr.minStackBytes]

structure MachineInvariant [bindings : Bindings] (initial : RamState)
    (capacity : Nat) (s : RamState) : Prop where
  ready : ReadyToStep s
  code : CodeIn Extracted.programImage s
  sse : SupportedSSE bindings.processor s
  df : DirectionFlagUnset s
  calleeSaved : ∀ register ∈ [Syntax.Reg.rbp, .r12, .r13, .r14, .r15],
    s.regValue register = initial.regValue register
  grows : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome
  memoryFrame : MemoryWriteFrame initial s (writableRegions initial capacity)
  outerReturn : (Operand.mem (stackPtr initial) : Operand 64).read s =
    (returnBoundary initial).rip

structure SubroutinePre [Bindings] (initial : RamState) (input : List UInt8)
    (capacity : Nat) (s : RamState) : Prop extends MachineInvariant initial (if 2 * input.length ≤ capacity then 2 * input.length else 0) s where
  rip : s.RIP = 0x1004a0
  rsp : stackPtr s = stackPtr initial - 32
  resultPointer : (Operand.reg 7 : Operand 64).read s = stackPtr initial - 24
  inputPointer : (Operand.reg 6 : Operand 64).read s = initial.regValue .rdi
  inputLength : (Operand.reg 2 : Operand 64).read s = BitVec.ofNat 64 input.length
  outputPointer : (Operand.reg 1 : Operand 64).read s = initial.regValue .rcx
  outputCapacity : (Operand.reg 8 : Operand 64).read s = BitVec.ofNat 64 capacity
  innerReturn : (Operand.mem (stackPtr initial - 32) : Operand 64).read s = 0x100196
  savedRbx : (Operand.mem (stackPtr initial - 8) : Operand 64).read s = initial.regValue .rbx
  lengthPointer : (Operand.reg 3 : Operand 64).read s = initial.regValue .rdx


structure LoopInvariant [Bindings] (initial : RamState) (input : List UInt8)
    (capacity index : Nat) (s : RamState) : Prop extends MachineInvariant initial (if 2 * input.length ≤ capacity then 2 * input.length else 0) s where
  rip : s.RIP = if index < input.length then 0x1004d0 else 0x100521
  rsp : stackPtr s = stackPtr initial - 32
  resultPointer : (Operand.reg 0 : Operand 64).read s = stackPtr initial - 24
  inputPointer : (Operand.reg 6 : Operand 64).read s = initial.regValue .rdi
  inputLength : (Operand.reg 2 : Operand 64).read s = BitVec.ofNat 64 input.length
  outputPointer : (Operand.reg 1 : Operand 64).read s = initial.regValue .rcx
  outputLength : (Operand.reg 7 : Operand 64).read s = BitVec.ofNat 64 (2 * input.length)
  indexValue : (Operand.reg 8 : Operand 64).read s = BitVec.ofNat 64 index
  innerReturn : (Operand.mem (stackPtr initial - 32) : Operand 64).read s = 0x100196
  output : readOutput initial s (2 * index) = .ok (encodedBytes (input.take index)).toByteArray
  savedRbx : (Operand.mem (stackPtr initial - 8) : Operand 64).read s = initial.regValue .rbx
  lengthPointer : (Operand.reg 3 : Operand 64).read s = initial.regValue .rdx


structure SubroutinePost [Bindings] (initial : RamState) (input : List UInt8)
    (capacity : Nat) (s : RamState) : Prop extends MachineInvariant initial (if 2 * input.length ≤ capacity then 2 * input.length else 0) s where
  rip : s.RIP = 0x100196
  rsp : stackPtr s = stackPtr initial - 24
  result :
    if 2 * input.length ≤ capacity then
      (Operand.mem (stackPtr initial - 24) : Operand 64).read s = initial.regValue .rcx ∧
      (Operand.mem (stackPtr initial - 16) : Operand 64).read s =
        BitVec.ofNat 64 (2 * input.length) ∧
      readOutput initial s (2 * input.length) = .ok (encodedBytes input).toByteArray
    else
      (Operand.mem (stackPtr initial - 24) : Operand 64).read s = 0 ∧
      (Operand.mem (stackPtr initial - 16) : Operand 8).read s = 1
  savedRbx : (Operand.mem (stackPtr initial - 8) : Operand 64).read s = initial.regValue .rbx
  lengthPointer : (Operand.reg 3 : Operand 64).read s = initial.regValue .rdx


structure CalleeExitPre [Bindings] (initial : RamState) (input : List UInt8)
    (capacity : Nat) (s : RamState) : Prop extends MachineInvariant initial (if 2 * input.length ≤ capacity then 2 * input.length else 0) s where
  rip : s.RIP = if 2 * input.length ≤ capacity then 0x100521 else 0x1004ac
  rsp : stackPtr s = stackPtr initial - 32
  resultPointer : (Operand.reg 0 : Operand 64).read s = stackPtr initial - 24
  innerReturn : (Operand.mem (stackPtr initial - 32) : Operand 64).read s = 0x100196
  success : 2 * input.length ≤ capacity →
    (Operand.reg 1 : Operand 64).read s = initial.regValue .rcx ∧
    (Operand.reg 7 : Operand 64).read s = BitVec.ofNat 64 (2 * input.length) ∧
    readOutput initial s (2 * input.length) = .ok (encodedBytes input).toByteArray

  savedRbx : (Operand.mem (stackPtr initial - 8) : Operand 64).read s = initial.regValue .rbx
  lengthPointer : (Operand.reg 3 : Operand 64).read s = initial.regValue .rdx

end Base16ct.Proofs.EncodeStr.Lower
