import Base16ct.Proofs.Copied.Md5.Proofs.Buffered.Stores.Effect
import Base16ct.Proofs.Copied.Md5.Proofs.Block.Entry
import X86Proofs.Program.ReadWrite.Bytes

namespace Base16ct.Proofs.Copied.Md5.Proofs.Buffered.Stores

open Base16ct.Proofs.Copied.Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs

theorem writable_of_agrees {s t : RamState} {addr : BitVec 64} {len : Nat}
    {cs : List Component} (h : Base16ct.Proofs.Copied.Md5.Proofs.Memory.MemWritable s addr len)
    (he : AgreesExcept cs s t) : Base16ct.Proofs.Copied.Md5.Proofs.Memory.MemWritable t addr len :=
  ⟨h.low, fun i hi ↦ he.grow _ (h.bytes i hi), h.tables⟩

theorem readable_of_agrees {s t : RamState} {addr : BitVec 64} {len : Nat}
    {cs : List Component} (h : MemReadable s addr len) (he : AgreesExcept cs s t) :
    MemReadable t addr len :=
  ⟨h.low, fun i hi ↦ he.grow _ (h.mem i hi)⟩

theorem readable_sub {s : RamState} {addr : BitVec 64} {len : Nat}
    (h : MemReadable s addr len) (offset count : Nat) (hb : offset + count ≤ len) :
    MemReadable s (addr + BitVec.ofNat 64 offset) count := by
  refine ⟨?_, ?_⟩
  · have hl := h.low
    rw [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show offset < 2^64 by omega),
      Nat.mod_eq_of_lt (show addr.toNat + offset < 2^64 by omega)]
    omega
  · intro i hi
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact h.mem (offset + i) (by omega)

theorem writable_sub {s : RamState} {addr : BitVec 64} {len : Nat}
    (h : Base16ct.Proofs.Copied.Md5.Proofs.Memory.MemWritable s addr len)
    (offset count : Nat) (hb : offset + count ≤ len) :
    Base16ct.Proofs.Copied.Md5.Proofs.Memory.MemWritable s (addr + BitVec.ofNat 64 offset) count := by
  have hr := readable_sub h.readable offset count hb
  refine ⟨hr.low, hr.mem, ?_⟩
  intro i hi
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact h.tables (offset + i) (by omega)

end Base16ct.Proofs.Copied.Md5.Proofs.Buffered.Stores
