import P256.Proofs.Program.Memory
import X86Proofs.Program.ReadWrite.WriteFrame

set_option autoImplicit false

namespace P256.Proofs.Program

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86Proofs

variable {s t : RamState} {reserve : Nat}

theorem stack_bounds (hStack : Stack.Valid s reserve) :
    reserve ≤ (stackPtr s).toNat ∧ (stackPtr s).toNat + 8 < 2^32 := by
  refine ⟨hStack.2.2.1, ?_⟩
  have hb := hStack.1
  change (Stack.region s reserve).start + (Stack.region s reserve).size < 2^32 at hb
  rwa [stack_region_end] at hb

theorem stack_sub_toNat (hStack : Stack.Valid s reserve)
    {offset : Nat} (hoffset : offset ≤ reserve) :
    (stackPtr s - BitVec.ofNat 64 offset).toNat = (stackPtr s).toNat - offset := by
  have hn := (stack_bounds hStack).1
  have hs := (stackPtr s).isLt
  have ho : offset < 2^64 := by omega
  rw [BitVec.toNat_sub_of_le (by
    rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho]
    omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho]

theorem stack_sub_readable (hStack : Stack.Valid s reserve)
    {offset len : Nat} (hoffset : offset ≤ reserve) (hlen : len ≤ offset + 8) :
    MemReadable s (stackPtr s - BitVec.ofNat 64 offset) len := by
  apply memoryRegion_memReadable hStack.1 hStack.2.1
  · rw [stack_sub_toNat hStack hoffset]
    change (stackPtr s).toNat - reserve ≤ (stackPtr s).toNat - offset
    omega
  · rw [stack_region_end, stack_sub_toNat hStack hoffset]
    have := (stack_bounds hStack).1
    omega

theorem stack_sub_writable (hStack : Stack.Valid s reserve)
    (hAvoid : (Stack.region s reserve).Avoids InPageTables)
    {offset len : Nat} (hoffset : offset ≤ reserve) (hlen : len ≤ offset + 8)
    (hpos : 0 < len)
    (_hpage : (stackPtr s - BitVec.ofNat 64 offset).toNat % 4096 + len ≤ 4096) :
    MemWritable s (stackPtr s - BitVec.ofNat 64 offset) len := by
  have hr := stack_sub_readable hStack hoffset hlen
  refine MemWritable.of_not_reserved hpos hr.low hr.mem ?_
  intro i hi hreserved
  apply hAvoid (stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i)
  · apply memoryRegion_contains_add hStack.1 (len := len) _ _ hi
    · rw [stack_sub_toNat hStack hoffset]
      change (stackPtr s).toNat - reserve ≤ (stackPtr s).toNat - offset
      omega
    · rw [stack_region_end, stack_sub_toNat hStack hoffset]
      have := (stack_bounds hStack).1
      omega
  · exact hreserved

theorem stack_sub_writable8 (hStack : Stack.Valid s reserve)
    (hAvoid : (Stack.region s reserve).Avoids InPageTables)
    {offset : Nat} (hoffset : offset ≤ reserve) (halign : offset % 8 = 0) :
    MemWritable s (stackPtr s - BitVec.ofNat 64 offset) 8 := by
  apply stack_sub_writable hStack hAvoid hoffset (by omega) (by decide)
  rw [stack_sub_toNat hStack hoffset]
  have hs : (stackPtr s).toNat % 16 = 8 := hStack.2.2.2
  have hn := (stack_bounds hStack).1
  have ha : ((stackPtr s).toNat - offset) % 8 = 0 := by omega
  have hm := Nat.mod_mod_of_dvd ((stackPtr s).toNat - offset) (show 8 ∣ 4096 by decide)
  omega

theorem readable_of_grow {addr : BitVec 64} {len : Nat}
    (hr : MemReadable s addr len)
    (hgrow : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome) :
    MemReadable t addr len :=
  ⟨hr.low, fun i hi => hgrow _ (hr.mem i hi)⟩

theorem writable_of_grow {addr : BitVec 64} {len : Nat}
    (hw : MemWritable s addr len)
    (hgrow : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome) :
    MemWritable t addr len :=
  ⟨hw.low, fun i hi => hgrow _ (hw.mem i hi), hw.tables⟩

end P256.Proofs.Program
