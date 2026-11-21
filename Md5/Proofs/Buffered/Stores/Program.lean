import Md5.Proofs.Buffered.Stores.Effect
import Md5.Proofs.Block.Entry
import X86Proofs.Program.ReadWrite.Bytes

namespace Md5.Proofs.Buffered.Stores

open Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs

theorem writable_of_agrees {s t : RamState} {addr : BitVec 64} {len : Nat}
    {cs : List Component} (h : Md5.Proofs.Memory.MemWritable s addr len)
    (he : AgreesExcept cs s t) : Md5.Proofs.Memory.MemWritable t addr len :=
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
    (h : Md5.Proofs.Memory.MemWritable s addr len)
    (offset count : Nat) (hb : offset + count ≤ len) :
    Md5.Proofs.Memory.MemWritable s (addr + BitVec.ofNat 64 offset) count := by
  have hr := readable_sub h.readable offset count hb
  refine ⟨hr.low, hr.mem, ?_⟩
  intro i hi
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact h.tables (offset + i) (by omega)

theorem rangeApart_text {addr : BitVec 64} {len offset count : Nat}
    (ha : ∀ i < len, ¬ InProgram (addr + BitVec.ofNat 64 i))
    (hb : offset + count ≤ Extracted.textBytes.size) :
    RangeApart addr len (Extracted.textAddress + BitVec.ofNat 64 offset) count := by
  intro i hi j hj he
  apply ha i hi
  rw [he, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact Block.text_address_in_program (offset + j) (by omega)

theorem store_avoids_program {e : Effect} {addr : BitVec 64} {len : Nat}
    (hc : e.components = [.mem addr len, .rip])
    (ha : ∀ i < len, ¬ InProgram (addr + BitVec.ofNat 64 i)) :
    e.Avoids Extracted.programImage := by
  intro x hx c hm hcov
  rw [hc] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl
  · obtain ⟨i, hi, he⟩ := hcov
    exact ha i hi ⟨x.2, he ▸ hx⟩
  · exact hcov

theorem bytes_of_read_eq {s : RamState} {addr : BitVec 64} {value : BitVec 64}
    (hr : MemReadable s addr 8)
    (hv : (Operand.mem addr : Operand 64).read s = value) :
    Bytes s.external addr 8 (storedByte value) := by
  have hb := Bytes.of_memLoad (n := 64) hr.mem
  change memLoad s.external addr 64 = value at hv
  rwa [hv] at hb

end Md5.Proofs.Buffered.Stores
