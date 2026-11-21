import P256.Proofs.Program.Compare.Interface
import P256.Proofs.Program.Compare.Support
import X86Proofs.Program.ReadWrite.Store

namespace P256.Proofs.Program.Compare

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Spec.Program P256.Spec.Program.Routines

def BytesEqual (s : RamState) (left right : BitVec 64) (length : Nat) : Prop :=
  ∀ i < length,
    memByte s.external (left + BitVec.ofNat 64 i) =
      memByte s.external (right + BitVec.ofNat 64 i)

theorem BytesEqual.slice {s : RamState} {left right : BitVec 64} {length : Nat}
    (h : BytesEqual s left right length) (offset count : Nat) (hb : offset + count ≤ length) :
    BytesEqual s (left + BitVec.ofNat 64 offset) (right + BitVec.ofNat 64 offset) count := by
  intro i hi
  simpa only [BitVec.add_assoc, ← BitVec.ofNat_add] using h (offset + i) (by omega)

theorem bytesEqual_append {s : RamState} {left right : BitVec 64} {first rest : Nat} :
    BytesEqual s left right (first + rest) ↔
      BytesEqual s left right first ∧
        BytesEqual s (left + BitVec.ofNat 64 first) (right + BitVec.ofNat 64 first) rest := by
  constructor
  · intro h
    exact ⟨fun i hi ↦ h i (by omega), h.slice first rest (by omega)⟩
  · rintro ⟨hfirst, hrest⟩ i hi
    by_cases h : i < first
    · exact hfirst i h
    · have he := hrest (i - first) (by omega)
      simpa only [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_of_le (by omega : first ≤ i)]
        using he

theorem bytesEqual_iff_load {s : RamState} {left right : BitVec 64} {width : Nat} :
    BytesEqual s left right (width / 8) ↔
      (Operand.mem left : Operand width).read s = (Operand.mem right : Operand width).read s :=
  ⟨memLoad_congr, fun h ↦ memByte_of_memLoad_eq h⟩

theorem BytesEqual.of_external {s t : RamState} {left right : BitVec 64} {length : Nat}
    (h : BytesEqual s left right length) (he : t.external = s.external) :
    BytesEqual t left right length := by
  simpa only [BytesEqual, he] using h

def callChanges (s : RamState) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 4, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11,
    .flags, .rip, .mem (stackPtr s - 64) 64]

structure CallPre [Bindings] (s : RamState) : Prop where
  rip : s.RIP = 0x11c860
  smallTail : ((Operand.reg 2 : Operand 64).read s).toNat % 16 < 8
  frame : CallFrame s 64
  left : MemReadable s ((Operand.reg 7 : Operand 64).read s)
    ((Operand.reg 2 : Operand 64).read s).toNat
  right : MemReadable s ((Operand.reg 6 : Operand 64).read s)
    ((Operand.reg 2 : Operand 64).read s).toNat
  stackLeft : RangeApart (stackPtr s - 64) 64 ((Operand.reg 7 : Operand 64).read s)
    ((Operand.reg 2 : Operand 64).read s).toNat
  stackRight : RangeApart (stackPtr s - 64) 64 ((Operand.reg 6 : Operand 64).read s)
    ((Operand.reg 2 : Operand 64).read s).toNat

structure Result [Bindings] (s t : RamState) : Prop extends CallResult s t (callChanges s) where
  zero_iff : (Operand.reg 0 : Operand 32).read t = 0 ↔
    BytesEqual s ((Operand.reg 7 : Operand 64).read s) ((Operand.reg 6 : Operand 64).read s)
      ((Operand.reg 2 : Operand 64).read s).toNat

def CallBoundary (boundary : ReturnBoundary) (s : RamState) : Prop :=
  ¬ InProgram boundary.rip ∧ (returnBoundary s).rip ≠ boundary.rip

def Correct [Bindings] : Prop :=
  ∀ (boundary : ReturnBoundary) (s : RamState), CallPre s → CallBoundary boundary s →
    ∃ fuel t, Advances boundary fuel s t ∧ Result s t

theorem program_text_slice {s : RamState} (hCode : CodeIn Extracted.programSections.toCodeMap s)
    (offset count : Nat) (h : offset + count ≤ Extracted.textBytes.size) :
    CodeIn (codeRange (Extracted.textAddress + BitVec.ofNat 64 offset)
      (Extracted.textBytes.toListFrom offset count)) s :=
  hCode.slice_of_section (sec := ⟨Extracted.textAddress, Extracted.textBytes⟩)
    (by simp [Extracted.programSections]) offset count h

end P256.Proofs.Program.Compare
