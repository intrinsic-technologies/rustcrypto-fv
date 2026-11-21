import Hkdf.Proofs.Common.Encoding.Serialize.State
import Hkdf.Proofs.Common.Machine.Entry

set_option autoImplicit false

open Hkdf.Proofs.Common.Machine (CalleePre memoryRegion_contains_add memoryRegion_memReadable stack_region_end)

namespace Hkdf.Proofs.Common.Encoding.Serialize

open Hkdf.Spec Hkdf.Proofs.Program Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [bindings : Bindings] {s t : RamState} {boundary : ReturnBoundary}
  {entry : BitVec 64} {inputBytes outputBytes reserve : Nat}

theorem stack_bounds (pre : CalleePre s boundary entry inputBytes outputBytes reserve) :
    reserve ≤ (stackPtr s).toNat ∧ (stackPtr s).toNat + 8 < 2^32 := by
  refine ⟨pre.stack.2.2.1, ?_⟩
  have hb := pre.stack.1
  change (Stack.region s reserve).start + (Stack.region s reserve).size < 2^32 at hb
  rwa [stack_region_end] at hb

theorem stack_sub_toNat (pre : CalleePre s boundary entry inputBytes outputBytes reserve)
    {offset : Nat} (hoffset : offset ≤ reserve) :
    (stackPtr s - BitVec.ofNat 64 offset).toNat = (stackPtr s).toNat - offset := by
  have hn := (stack_bounds pre).1
  have hs := (stackPtr s).isLt
  have ho : offset < 2^64 := by omega
  rw [BitVec.toNat_sub_of_le (by
    rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho]
    omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho]

theorem stack_sub_readable (pre : CalleePre s boundary entry inputBytes outputBytes reserve)
    {offset len : Nat} (hoffset : offset ≤ reserve) (hlen : len ≤ offset + 8) :
    MemReadable s (stackPtr s - BitVec.ofNat 64 offset) len := by
  apply memoryRegion_memReadable pre.stack.1 pre.stack.2.1
  · rw [stack_sub_toNat pre hoffset]
    change (stackPtr s).toNat - reserve ≤ (stackPtr s).toNat - offset
    omega
  · rw [stack_region_end, stack_sub_toNat pre hoffset]
    have := (stack_bounds pre).1
    omega

theorem stack_sub_writable (pre : CalleePre s boundary entry inputBytes outputBytes reserve)
    {offset len : Nat} (hoffset : offset ≤ reserve) (hlen : len ≤ offset + 8)
    (hpos : 0 < len) :
    MemWritable s (stackPtr s - BitVec.ofNat 64 offset) len := by
  have hr := stack_sub_readable pre hoffset hlen
  refine MemWritable.of_not_reserved hpos hr.low hr.mem ?_
  intro i hi hreserved
  apply pre.avoids (Stack.region s reserve) (by simp)
    (stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i)
  · apply memoryRegion_contains_add pre.stack.1 (len := len) _ _ hi
    · rw [stack_sub_toNat pre hoffset]
      change (stackPtr s).toNat - reserve ≤ (stackPtr s).toNat - offset
      omega
    · rw [stack_region_end, stack_sub_toNat pre hoffset]
      have := (stack_bounds pre).1
      omega
  · exact .inr hreserved

theorem stack_sub_writable8 (pre : CalleePre s boundary entry inputBytes outputBytes reserve)
    {offset : Nat} (hoffset : offset ≤ reserve) (halign : offset % 8 = 0) :
    MemWritable s (stackPtr s - BitVec.ofNat 64 offset) 8 := by
  exact stack_sub_writable pre hoffset (by omega) (by decide)

omit bindings in
theorem readable_of_grow {addr : BitVec 64} {len : Nat}
    (hr : MemReadable s addr len)
    (hgrow : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome) :
    MemReadable t addr len :=
  ⟨hr.low, fun i hi => hgrow _ (hr.mem i hi)⟩

omit bindings in
theorem writable_of_grow {addr : BitVec 64} {len : Nat}
    (hw : MemWritable s addr len)
    (hgrow : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome) :
    MemWritable t addr len :=
  ⟨hw.low, fun i hi => hgrow _ (hw.mem i hi), hw.tables⟩

omit bindings in
theorem agrees_of_footprint {small large : List Component}
    (h : AgreesExcept small s t)
    (hreg : ∀ c ∈ small, c.isMem = false → c ∈ large)
    (hmem : ∀ c ∈ small, ∀ a, c.Covers a → ∃ d ∈ large, d.Covers a) :
    AgreesExcept large s t := by
  refine ⟨?_, ?_, h.rest, h.grow⟩
  · intro c hc hm
    exact h.agree c (fun hs => hc (hreg c hs hm)) hm
  · intro a ha
    apply h.memory a
    intro c hc hcover
    obtain ⟨d, hd, hcover'⟩ := hmem c hc a hcover
    exact ha d hd hcover'

end Hkdf.Proofs.Common.Encoding.Serialize
