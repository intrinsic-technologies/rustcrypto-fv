import P256.Proofs.Program.Compare.Interface

namespace P256.Proofs.Program.Compare

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Spec.Program P256.Spec.Program.Routines

theorem CallFrame.stack_bounds [Bindings] {s : RamState} {budget : Nat}
    (h : CallFrame s budget) :
    budget ≤ (stackPtr s).toNat ∧ (stackPtr s).toNat + 8 < 2^32 ∧
      (stackPtr s).toNat % 16 = 8 := by
  refine ⟨h.stack.2.2.1, ?_, h.stack.2.2.2⟩
  have bound := h.stack.1
  change (stackPtr s).toNat - budget +
    ((stackPtr s).toNat + 8 - ((stackPtr s).toNat - budget)) < 2^32 at bound
  omega

theorem CallFrame.stack_sub_toNat [Bindings] {s : RamState} {budget offset : Nat}
    (h : CallFrame s budget) (low : offset ≤ budget) :
    (stackPtr s - BitVec.ofNat 64 offset).toNat = (stackPtr s).toNat - offset := by
  have bounds := h.stack_bounds
  rw [BitVec.toNat_sub_of_le (by
    rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem CallFrame.stack_sub_contains [Bindings] {s : RamState} {budget offset len : Nat}
    (h : CallFrame s budget) (low : offset ≤ budget) (high : len ≤ offset + 8)
    {i : Nat} (hi : i < len) :
    (Stack.region s budget).Contains
      (stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat := by
  have bounds := h.stack_bounds
  have address := h.stack_sub_toNat low
  have sum : (stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat =
      (stackPtr s).toNat - offset + i := by
    rw [BitVec.toNat_add, address, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  change (stackPtr s).toNat - budget ≤ _ ∧
    _ < (stackPtr s).toNat - budget +
      ((stackPtr s).toNat + 8 - ((stackPtr s).toNat - budget))
  rw [sum]
  omega

theorem CallFrame.stack_sub_readable [Bindings] {s : RamState} {budget offset len : Nat}
    (h : CallFrame s budget) (low : offset ≤ budget) (high : len ≤ offset + 8) :
    MemReadable s (stackPtr s - BitVec.ofNat 64 offset) len :=
  by
    apply P256.Proofs.Program.memoryRegion_memReadable h.stack.1 h.stack.2.1
    · rw [h.stack_sub_toNat low]
      change (stackPtr s).toNat - budget ≤ (stackPtr s).toNat - offset
      omega
    · rw [P256.Proofs.Program.stack_region_end, h.stack_sub_toNat low]
      have hb := h.stack_bounds
      omega

theorem CallFrame.stack_sub_writable [Bindings] {s : RamState} {budget offset len : Nat}
    (h : CallFrame s budget) (low : offset ≤ budget) (high : len ≤ offset + 8)
    (positive : 0 < len)
    (_page : (stackPtr s - BitVec.ofNat 64 offset).toNat % 4096 + len ≤ 4096) :
    MemWritable s (stackPtr s - BitVec.ofNat 64 offset) len := by
  have readable := h.stack_sub_readable low high
  apply MemWritable.of_not_reserved positive readable.low readable.mem
  intro i hi
  exact h.stackTables _ (h.stack_sub_contains low high hi)

theorem CallFrame.stack_sub_writable8 [Bindings] {s : RamState} {budget offset : Nat}
    (h : CallFrame s budget) (low : offset ≤ budget) (aligned : offset % 8 = 0) :
    MemWritable s (stackPtr s - BitVec.ofNat 64 offset) 8 := by
  apply h.stack_sub_writable low (by omega) (by decide)
  rw [h.stack_sub_toNat low]
  have bounds := h.stack_bounds
  have mod4096 := Nat.mod_mod_of_dvd ((stackPtr s).toNat - offset)
    (show 8 ∣ 4096 by decide)
  omega

theorem CallFrame.stack_sub_avoids_code [Bindings] {s : RamState} {budget offset len : Nat}
    (h : CallFrame s budget) (low : offset ≤ budget) (high : len ≤ offset + 8)
    {i : Nat} (hi : i < len) :
    ¬ InProgram (stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i) :=
  h.stackCode _ (h.stack_sub_contains low high hi)

end P256.Proofs.Program.Compare
