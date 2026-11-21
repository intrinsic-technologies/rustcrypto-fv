import ChaCha20Poly1305.Spec.Program
import X86Proofs.Program.Execution
import X86Proofs.Program.ReadWrite.RepString

namespace ChaCha20Poly1305.Proofs.Common

open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Spec.Program

def InPageTables (address : BitVec 64) : Prop :=
  pageTables.Contains address.toNat

theorem inPageTables_iff (address : BitVec 64) :
    InPageTables address ↔ 0x1000 ≤ address.toNat ∧ address.toNat < 0x2020 := by
  simp [InPageTables, pageTables, MemoryRegion.Contains]

structure WritableRange (s : RamState) (address : BitVec 64) (length : Nat) : Prop where
  readable : MemReadable s address length
  tables : ∀ i < length, ¬ InPageTables (address + BitVec.ofNat 64 i)
  code : ∀ i < length, ¬ InProgram (address + BitVec.ofNat 64 i)

theorem memReadable_slice {s : RamState} {address : BitVec 64} {length : Nat}
    (h : MemReadable s address length) (offset count : Nat) (hle : offset + count ≤ length) :
    MemReadable s (address + BitVec.ofNat 64 offset) count := by
  refine ⟨?_, ?_⟩
  · rw [toNat_add_ofNat _ _ (by have := h.low; omega)]
    have := h.low
    omega
  · intro i hi
    rw [add_ofNat_add_ofNat]
    exact h.mem (offset + i) (by omega)

theorem WritableRange.of_agrees {s t : RamState} {address : BitVec 64} {length : Nat}
    {changes : List Component} (h : WritableRange s address length)
    (ha : AgreesExcept changes s t) : WritableRange t address length :=
  ⟨⟨h.readable.low, fun i hi ↦ ha.grow _ (h.readable.mem i hi)⟩, h.tables, h.code⟩

theorem WritableRange.slice {s : RamState} {address : BitVec 64} {length : Nat}
    (h : WritableRange s address length) (offset count : Nat) (hle : offset + count ≤ length) :
    WritableRange s (address + BitVec.ofNat 64 offset) count := by
  refine ⟨memReadable_slice h.readable offset count hle, ?_, ?_⟩
  · intro i hi
    rw [add_ofNat_add_ofNat]
    exact h.tables (offset + i) (by omega)
  · intro i hi
    rw [add_ofNat_add_ofNat]
    exact h.code (offset + i) (by omega)

end ChaCha20Poly1305.Proofs.Common
