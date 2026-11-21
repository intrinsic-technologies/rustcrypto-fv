import Hkdf.Proofs.Key.State
import Hkdf.Proofs.Common.CallFrame.Stack
import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.Machine.Entry
import Hkdf.Proofs.Common.Machine.StackRegion
import Hkdf.Proofs.Common.Encoding.Serialize.Stack

set_option autoImplicit false

open Hkdf.Proofs.Common.Machine (CalleePre)
open Hkdf.Proofs.Common.Machine (memoryRegion_contains_add memoryRegion_memReadable stack_region_end)

namespace Hkdf.Proofs.Key

open Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [bindings : Bindings] {s t : RamState} {boundary : ReturnBoundary}
  {entry : BitVec 64} {inputBytes outputBytes reserve : Nat}

theorem stack_bounds (pre : CalleePre s boundary entry inputBytes outputBytes reserve) :
    reserve ≤ (stackPtr s).toNat ∧ (stackPtr s).toNat + 8 < 2^32 :=
  Hkdf.Proofs.Common.CallFrame.stack_bounds pre.stack

theorem stack_sub_toNat (pre : CalleePre s boundary entry inputBytes outputBytes reserve)
    {offset : Nat} (hoffset : offset ≤ reserve) :
    (stackPtr s - BitVec.ofNat 64 offset).toNat = (stackPtr s).toNat - offset :=
  Hkdf.Proofs.Common.CallFrame.stack_sub_toNat pre.stack hoffset

theorem stack_sub_readable (pre : CalleePre s boundary entry inputBytes outputBytes reserve)
    {offset len : Nat} (hoffset : offset ≤ reserve) (hlen : len ≤ offset + 8) :
    MemReadable s (stackPtr s - BitVec.ofNat 64 offset) len :=
  Hkdf.Proofs.Common.CallFrame.stack_readable pre.stack (fun _ h ↦ h) hoffset hlen

theorem stack_sub_writable (pre : CalleePre s boundary entry inputBytes outputBytes reserve)
    {offset len : Nat} (hoffset : offset ≤ reserve) (hlen : len ≤ offset + 8)
    (hpos : 0 < len)
    (hpage : (stackPtr s - BitVec.ofNat 64 offset).toNat % 4096 + len ≤ 4096) :
    MemWritable s (stackPtr s - BitVec.ofNat 64 offset) len :=
  Hkdf.Proofs.Common.CallFrame.stack_writable pre.stack
    (pre.avoids (Stack.region s reserve) (by simp)) (fun _ h ↦ h) hoffset hlen hpos hpage

theorem stack_sub_writable8 (pre : CalleePre s boundary entry inputBytes outputBytes reserve)
    {offset : Nat} (hoffset : offset ≤ reserve) (halign : offset % 8 = 0) :
    MemWritable s (stackPtr s - BitVec.ofNat 64 offset) 8 :=
  Hkdf.Proofs.Common.CallFrame.stack_writable8 pre.stack
    (pre.avoids (Stack.region s reserve) (by simp)) (fun _ h ↦ h) hoffset halign

export Hkdf.Proofs.Common.Encoding.Serialize (readable_of_grow writable_of_grow agrees_of_footprint)

omit bindings in
theorem stack_address {initial s : RamState}
    (rsp : stackPtr s = blockAddress initial) (i : BitVec 64) :
    rspOf s + i = stackPtr initial - (376 - i) := by
  change stackPtr s + i = _
  rw [rsp]
  simp only [blockAddress, BitVec.sub_eq_add_neg, BitVec.neg_add,
    BitVec.neg_neg, BitVec.add_assoc]

omit bindings in
theorem stack_readable [Bindings] {initial s : RamState}
    {boundary : ReturnBoundary} {key : ByteArray}
    (ctx : Context initial boundary key) (state : State initial boundary s)
    {offset len : Nat} (low : offset ≤ 720) (high : len ≤ offset + 8) :
    MemReadable s (stackPtr initial - BitVec.ofNat 64 offset) len :=
  Hkdf.Proofs.Common.CallFrame.stack_readable ctx.stack state.allocated low high

omit bindings in
theorem stack_writable [Bindings] {initial s : RamState}
    {boundary : ReturnBoundary} {key : ByteArray}
    (ctx : Context initial boundary key) (state : State initial boundary s)
    {offset len : Nat} (low : offset ≤ 720) (high : len ≤ offset + 8)
    (positive : 0 < len)
    (page : (stackPtr initial - BitVec.ofNat 64 offset).toNat % 4096 + len ≤ 4096) :
    MemWritable s (stackPtr initial - BitVec.ofNat 64 offset) len :=
  Hkdf.Proofs.Common.CallFrame.stack_writable ctx.stack
    (ctx.avoids (Stack.region initial stackBytes) (by simp)) state.allocated low high positive page

omit bindings in
theorem stack_writable8 [Bindings] {initial s : RamState}
    {boundary : ReturnBoundary} {key : ByteArray}
    (ctx : Context initial boundary key) (state : State initial boundary s)
    {offset : Nat} (low : offset ≤ 720) (align : offset % 8 = 0) :
    MemWritable s (stackPtr initial - BitVec.ofNat 64 offset) 8 :=
  Hkdf.Proofs.Common.CallFrame.stack_writable8 ctx.stack
    (ctx.avoids (Stack.region initial stackBytes) (by simp)) state.allocated low align

omit bindings in
theorem stack_writable4 [Bindings] {initial s : RamState}
    {boundary : ReturnBoundary} {key : ByteArray}
    (ctx : Context initial boundary key) (state : State initial boundary s)
    {offset : Nat} (low : offset ≤ 720) (align : offset % 4 = 0) :
    MemWritable s (stackPtr initial - BitVec.ofNat 64 offset) 4 :=
  Hkdf.Proofs.Common.CallFrame.stack_writable4 ctx.stack
    (ctx.avoids (Stack.region initial stackBytes) (by simp)) state.allocated low align

omit bindings in
theorem stack_writable1 [Bindings] {initial s : RamState}
    {boundary : ReturnBoundary} {key : ByteArray}
    (ctx : Context initial boundary key) (state : State initial boundary s)
    {offset : Nat} (low : offset ≤ 720) :
    MemWritable s (stackPtr initial - BitVec.ofNat 64 offset) 1 :=
  Hkdf.Proofs.Common.CallFrame.stack_writable1 ctx.stack
    (ctx.avoids (Stack.region initial stackBytes) (by simp)) state.allocated low

omit bindings in
theorem stack_codeApart [Bindings] {initial : RamState}
    {boundary : ReturnBoundary} {key : ByteArray}
    (ctx : Context initial boundary key) {offset len codeOffset codeLen : Nat}
    (low : offset ≤ 720) (high : len ≤ offset)
    (bound : codeOffset + codeLen ≤ 115149) :
    RangeApart (stackPtr initial - BitVec.ofNat 64 offset) len
      (Extracted.textAddress + BitVec.ofNat 64 codeOffset) codeLen :=
  Hkdf.Proofs.Common.CallFrame.stack_codeApart ctx.stack
    (fun a ha hp ↦ ctx.avoids (Stack.region initial stackBytes) (by simp) a ha (.inl hp))
    low (by omega) bound

def LocalWrites (initial : RamState) (components : List Component) : Prop :=
  ∀ c ∈ components, ∀ a, c.Covers a →
    (Component.mem (stackPtr initial - 720) 680).Covers a

omit bindings in
theorem local_memory {initial : RamState} {offset len : Nat}
    (lo : offset ≤ 720) (hi : len + 40 ≤ offset) :
    ∀ a, (Component.mem (stackPtr initial - BitVec.ofNat 64 offset) len).Covers a →
      (Component.mem (stackPtr initial - 720) 680).Covers a := by
  intro a ha
  obtain ⟨i, hi', rfl⟩ := ha
  refine ⟨720 - offset + i, by omega, ?_⟩
  rw [BitVec.ofNat_add, ← BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)]
  calc
    _ = (stackPtr initial - 720 + 720) - BitVec.ofNat 64 offset + BitVec.ofNat 64 i := by
      rw [BitVec.sub_add_cancel]
    _ = _ := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.ofNat_eq_ofNat]

omit bindings in
theorem LocalWrites.within [Bindings] {initial : RamState}
    {boundary : ReturnBoundary} {key : ByteArray} {components : List Component}
    (h : LocalWrites initial components) (ctx : Context initial boundary key) :
    WritesWithin components (writeRegions initial) := by
  intro c hc a ha
  refine ⟨Stack.region initial stackBytes, by simp [writeRegions], ?_⟩
  exact Hkdf.Proofs.Common.Machine.stackRegion_contains_sub
    ctx.stack.2.2.1 (by decide) (by decide) (h c hc a ha)

omit bindings in
theorem LocalWrites.saved {initial : RamState} {components : List Component}
    (h : LocalWrites initial components) :
    ∀ c ∈ components, ∀ a,
      (Component.mem (stackPtr initial - 40) 48).Covers a → ¬ c.Covers a := by
  intro c hc a ha hw
  obtain ⟨i, hi, rfl⟩ := ha
  obtain ⟨j, hj, he⟩ := h c hc _ hw
  exact OffsetsApart.ne (c₁ := -40) (len₁ := 48) (c₂ := -720) (len₂ := 680)
    (by unfold OffsetsApart; decide +kernel) (stackPtr initial) hi hj (by decide)
    (by simpa only [BitVec.sub_eq_add_neg] using he)

end Hkdf.Proofs.Key
