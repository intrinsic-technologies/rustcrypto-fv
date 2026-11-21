import Sha2.Proofs.Wrapper.State
import Sha2.Proofs.Common.Encoding.Serialize.Stack
import Sha2.Proofs.Common.Field.Operations.Run.Compose
import Sha2.Proofs.Common.SHA256.Words

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper

variable {v : Variant}

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

theorem validCall_stack_bounds {initial : RamState} {inputs : Array Input}
    (call : ValidCall v.routine initial inputs) :
    816 ≤ (stackPtr initial).toNat ∧ (stackPtr initial).toNat + 8 < 2^32 := by
  refine ⟨call.stack.2.2.1, ?_⟩
  have bound := call.stack.1
  change (Stack.region initial v.routine.minStackBytes).start +
    (Stack.region initial v.routine.minStackBytes).size < 2^32 at bound
  rwa [stack_region_end] at bound

theorem validCall_stack_sub_toNat {initial : RamState} {inputs : Array Input}
    (call : ValidCall v.routine initial inputs) {offset : Nat} (bound : offset ≤ 816) :
    (stackPtr initial - BitVec.ofNat 64 offset).toNat = (stackPtr initial).toNat - offset := by
  have low := (validCall_stack_bounds call).1
  rw [BitVec.toNat_sub_of_le (by
    rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem validCall_stack_sub_readable {initial : RamState} {inputs : Array Input}
    (call : ValidCall v.routine initial inputs) {offset len : Nat}
    (low : offset ≤ 816) (high : len ≤ offset + 8) :
    MemReadable initial (stackPtr initial - BitVec.ofNat 64 offset) len := by
  apply memoryRegion_memReadable call.stack.1 call.stack.2.1
  · rw [validCall_stack_sub_toNat call low]
    change (stackPtr initial).toNat - 816 ≤ (stackPtr initial).toNat - offset
    omega
  · rw [stack_region_end, validCall_stack_sub_toNat call low]
    have bounds := validCall_stack_bounds call
    omega

theorem validCall_returnBoundary [bindings : Bindings] {initial : RamState}
    {inputs : Array Input} (machine : SupportedMachine bindings initial)
    (call : ValidCall v.routine initial inputs) :
    nearReturn64Boundary initial = .ok (returnBoundary initial) ∧
      (returnBoundary initial).rip.toNat < 2^32 ∧ ¬ InProgram (returnBoundary initial).rip := by
  have read := validCall_stack_sub_readable call (offset := 0) (len := 8) (by decide) (by decide)
  simp only [BitVec.sub_zero] at read
  have near := nearReturn64Boundary_eq initial (supportedMachine_readyToStep machine).dataReady
    machine.supported.integer.ss read
  obtain ⟨address, loaded, low, outside⟩ := call.returnAddress
  have value : memLoad initial.external (stackPtr initial) 64 = address := by
    rw [stackPtr_eq_regValue_rsp]
    apply Sha2.Proofs.Common.Memory.memLoad_of_loadBytes64
    simpa only [Stack.returnSlot, BitVec.ofNat_toNat, BitVec.setWidth_eq] using loaded.2
  refine ⟨near, ?_, ?_⟩
  · change (memLoad initial.external (stackPtr initial) 64).toNat < 2^32
    rw [value]
    exact low
  · change ¬ InProgram (memLoad initial.external (stackPtr initial) 64)
    rw [value]
    exact outside

 theorem stack_address {initial s : RamState}
    (rsp : stackPtr s = stackPtr initial - 344) (i : BitVec 64) :
    rspOf s + i = stackPtr initial - (344 - i) := by
  change stackPtr s + i = _
  rw [rsp]
  simp only [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.neg_neg, BitVec.add_assoc]

 theorem stack_readable [Bindings] {initial s : RamState} {inputs : Array Input}
    (ctx : Context initial inputs v) (state : Wrapper.State initial s v)
    {offset len : Nat} (low : offset ≤ 816) (high : len ≤ offset + 8) :
    MemReadable s (stackPtr initial - BitVec.ofNat 64 offset) len :=
  Common.Encoding.Serialize.readable_of_grow
    (validCall_stack_sub_readable ctx.call low high) state.allocated

theorem validCall_stack_sub_writable {initial : RamState} {inputs : Array Input}
    (call : ValidCall v.routine initial inputs)
    {offset len : Nat} (low : offset ≤ 816) (high : len ≤ offset + 8)
    (positive : 0 < len) :
    MemWritable initial (stackPtr initial - BitVec.ofNat 64 offset) len := by
  have read := validCall_stack_sub_readable call low high
  refine MemWritable.of_not_reserved positive read.low read.mem ?_
  intro i hi reserved
  apply (call.separation.2 (Stack.region initial v.routine.minStackBytes) (by simp)).2
    (stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i) ?_ (.inr reserved)
  apply memoryRegion_contains_add call.stack.1 (len := len) _ _ hi
  · rw [validCall_stack_sub_toNat call low]
    change (stackPtr initial).toNat - 816 ≤ (stackPtr initial).toNat - offset
    omega
  · rw [stack_region_end, validCall_stack_sub_toNat call low]
    have bounds := validCall_stack_bounds call
    omega

theorem validCall_stack_sub_writable8 {initial : RamState} {inputs : Array Input}
    (call : ValidCall v.routine initial inputs)
    {offset : Nat} (low : offset ≤ 816) (align : offset % 8 = 0) :
    MemWritable initial (stackPtr initial - BitVec.ofNat 64 offset) 8 := by
  exact validCall_stack_sub_writable call low (by omega) (by decide)

theorem stack_writable [Bindings] {initial s : RamState} {inputs : Array Input}
    (ctx : Context initial inputs v) (state : State initial s v)
    {offset len : Nat} (low : offset ≤ 816) (high : len ≤ offset + 8)
    (positive : 0 < len) :
    MemWritable s (stackPtr initial - BitVec.ofNat 64 offset) len :=
  Common.Encoding.Serialize.writable_of_grow
    (validCall_stack_sub_writable ctx.call low high positive) state.allocated

theorem stack_writable4 [Bindings] {initial s : RamState} {inputs : Array Input}
    (ctx : Context initial inputs v) (state : State initial s v)
    {offset : Nat} (low : offset ≤ 816) (align : offset % 4 = 0) :
    MemWritable s (stackPtr initial - BitVec.ofNat 64 offset) 4 := by
  exact stack_writable ctx state low (by omega) (by decide)

theorem stack_writable8 [Bindings] {initial s : RamState} {inputs : Array Input}
    (ctx : Context initial inputs v) (state : State initial s v)
    {offset : Nat} (low : offset ≤ 816) (align : offset % 8 = 0) :
    MemWritable s (stackPtr initial - BitVec.ofNat 64 offset) 8 := by
  exact stack_writable ctx state low (by omega) (by decide)

theorem stack_writable1 [Bindings] {initial s : RamState} {inputs : Array Input}
    (ctx : Context initial inputs v) (state : State initial s v)
    {offset : Nat} (low : offset ≤ 816) :
    MemWritable s (stackPtr initial - BitVec.ofNat 64 offset) 1 := by
  exact stack_writable ctx state low (by omega) (by decide)

 theorem stack_codeApart [Bindings] {initial : RamState} {inputs : Array Input}
    (ctx : Context initial inputs v) {offset len codeOffset codeLen : Nat}
    (low : offset ≤ 816) (high : len ≤ offset)
    (code : codeOffset + codeLen ≤ 71757) :
    RangeApart (stackPtr initial - BitVec.ofNat 64 offset) len
      (Extracted.textAddress + BitVec.ofNat 64 codeOffset) codeLen := by
  intro j hj k hk eq
  have contains := stackRegion_contains_sub ctx.call.stack.2.2.1 low high ⟨j, hj, rfl⟩
  apply (ctx.call.separation.2 (Stack.region initial v.routine.minStackBytes) (by simp)).2 _ contains
  left
  rw [eq, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact inProgram_of_textOffset (codeOffset + k) (by omega)

def LocalWrites (initial : RamState) (components : List Component) : Prop :=
  ∀ c ∈ components, ∀ a, c.Covers a →
    (Component.mem (stackPtr initial - 816) 640).Covers a ∨
    (Component.mem (stackPtr initial - 152) 104).Covers a

theorem local_memory {initial : RamState} {offset len : Nat}
    (lo : offset ≤ 816) (hi : len + 48 ≤ offset)
    (apart : len + 176 ≤ offset ∨ offset ≤ 152) :
    ∀ a, (Component.mem (stackPtr initial - BitVec.ofNat 64 offset) len).Covers a →
      (Component.mem (stackPtr initial - 816) 640).Covers a ∨
      (Component.mem (stackPtr initial - 152) 104).Covers a := by
  intro a ha
  obtain ⟨i, hi', rfl⟩ := ha
  rcases apart with below | above
  · left
    refine ⟨816-offset+i, by omega, ?_⟩
    rw [BitVec.ofNat_add, ← BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)]
    calc
      _ = (stackPtr initial - 816 + 816) - BitVec.ofNat 64 offset + BitVec.ofNat 64 i := by
        rw [BitVec.sub_add_cancel]
      _ = _ := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.ofNat_eq_ofNat]
  · right
    refine ⟨152-offset+i, by omega, ?_⟩
    rw [BitVec.ofNat_add, ← BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)]
    calc
      _ = (stackPtr initial - 152 + 152) - BitVec.ofNat 64 offset + BitVec.ofNat 64 i := by
        rw [BitVec.sub_add_cancel]
      _ = _ := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.ofNat_eq_ofNat]

theorem LocalWrites.within [Bindings] {initial : RamState} {inputs : Array Input}
    {components : List Component} (h : LocalWrites initial components)
    (ctx : Context initial inputs v) :
    WritesWithin components #v[outputRegion v.routine initial, Stack.region initial v.routine.minStackBytes] := by
  intro c hc a ha
  refine ⟨Stack.region initial v.routine.minStackBytes, by simp, ?_⟩
  rcases h c hc a ha with low | high
  · exact stackRegion_contains_sub ctx.call.stack.2.2.1 (by change 816 ≤ 816; decide) (by decide) low
  · exact stackRegion_contains_sub ctx.call.stack.2.2.1 (by change 152 ≤ 816; decide) (by decide) high

theorem LocalWrites.saved {initial : RamState} {components : List Component}
    (h : LocalWrites initial components) :
    ∀ c ∈ components, ∀ a,
      (Component.mem (stackPtr initial - 48) 56).Covers a → ¬ c.Covers a := by
  intro c hc a ha hw
  obtain ⟨i, hi, rfl⟩ := ha
  rcases h c hc _ hw with ⟨j, hj, he⟩ | ⟨j, hj, he⟩
  · exact OffsetsApart.ne (c₁ := -48) (len₁ := 56) (c₂ := -816) (len₂ := 640)
      (by unfold OffsetsApart; decide +kernel) (stackPtr initial) hi hj (by decide) (by simpa only [BitVec.sub_eq_add_neg] using he)
  · exact OffsetsApart.ne (c₁ := -48) (len₁ := 56) (c₂ := -152) (len₂ := 104)
      (by unfold OffsetsApart; decide +kernel) (stackPtr initial) hi hj (by decide) (by simpa only [BitVec.sub_eq_add_neg] using he)

theorem LocalWrites.memory {initial s t : RamState} {components : List Component}
    (h : LocalWrites initial components) (frame : AgreesExcept components s t)
    {a : BitVec 64} (ha : (Component.mem (stackPtr initial - 176) 24).Covers a) :
    t.external[a]? = s.external[a]? := by
  apply frame.memory
  intro c hc hw
  obtain ⟨i, hi, rfl⟩ := ha
  rcases h c hc _ hw with ⟨j, hj, he⟩ | ⟨j, hj, he⟩
  · exact OffsetsApart.ne (c₁ := -176) (len₁ := 24) (c₂ := -816) (len₂ := 640)
      (by unfold OffsetsApart; decide +kernel) (stackPtr initial) hi hj (by decide) (by simpa only [BitVec.sub_eq_add_neg] using he)
  · exact OffsetsApart.ne (c₁ := -176) (len₁ := 24) (c₂ := -152) (len₂ := 104)
      (by unfold OffsetsApart; decide +kernel) (stackPtr initial) hi hj (by decide) (by simpa only [BitVec.sub_eq_add_neg] using he)

theorem preserved_of_bytes [Bindings] {initial s t : RamState}
    (input : Preserved initial s v) (state : State initial t v)
    (rsp : stackPtr t = stackPtr initial - 344)
    (bytes : ∀ a, (Component.mem (stackPtr initial - 176) 24).Covers a →
      t.external[a]? = s.external[a]?) : Preserved initial t v := by
  have same (offset : Nat) (lo : 160 ≤ offset) (hi : offset ≤ 176) :
      memLoad t.external (stackPtr initial - BitVec.ofNat 64 offset) 64 =
        memLoad s.external (stackPtr initial - BitVec.ofNat 64 offset) 64 := by
    apply memLoad_congr
    intro i bound
    change (t.external[_]?).getD 0 = (s.external[_]?).getD 0
    rw [bytes _ ⟨176-offset+i, by omega, ?_⟩]
    rw [BitVec.ofNat_add, ← BitVec.ofNat_sub_ofNat_of_le 176 offset (by omega) hi]
    calc
      _ = (stackPtr initial - 176 + 176) - BitVec.ofNat 64 offset + BitVec.ofNat 64 i := by
        rw [BitVec.sub_add_cancel]
      _ = _ := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.ofNat_eq_ofNat]
  exact ⟨state, rsp, (same 176 (by decide) (by decide)).trans input.outputPointer,
    (same 168 (by decide) (by decide)).trans input.pointerTable,
    (same 160 (by decide) (by decide)).trans input.lengthTable⟩

theorem preserved_of_agrees [Bindings] {initial s t : RamState} {inputs : Array Input}
    {fuel : Nat} {components : List Component}
    (ctx : Context initial inputs v) (input : Preserved initial s v)
    (run : Advances (returnBoundary initial) fuel s t) (ready : ReadyToStep t)
    (frame : AgreesExcept components s t) (writes : LocalWrites initial components)
    (kept4 : Component.reg 4 ∉ components) (hdf : .df ∉ components := by simp) :
    Preserved initial t v :=
  preserved_of_bytes input
    (input.toState.of_agrees ctx run ready frame (writes.within ctx) writes.saved hdf)
    ((frame.read (n := 64) kept4).trans input.rsp)
    (fun _ ha => writes.memory frame ha)

theorem store_bytes {initial s t : RamState} {written width offset len : Nat}
    (frame : AgreesExcept [.mem (stackPtr initial - BitVec.ofNat 64 written) width, .rip] s t)
    (apart : OffsetsApart (-(BitVec.ofNat 64 written)) width (-(BitVec.ofNat 64 offset)) len)
    (small : width + len < 2^64) :
    ∀ i < len, t.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      s.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  intro i hi
  apply frame.byte
  intro c hc covers
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · obtain ⟨j, hj, eq⟩ := covers
    apply OffsetsApart.ne apart (stackPtr initial) hj hi small
    simpa only [BitVec.sub_eq_add_neg] using eq.symm
  · exact covers

theorem frame_bytes [Bindings] {initial s t : RamState} {inputs : Array Input}
    {output count reserve offset len : Nat} (ctx : Context initial inputs v)
    (frame : MemoryWriteFrame s t #v[
      (⟨(stackPtr initial - BitVec.ofNat 64 output).toNat, count⟩ : MemoryRegion),
      (⟨(stackPtr initial - BitVec.ofNat 64 reserve).toNat, reserve-344⟩ : MemoryRegion)])
    (outLow : output ≤ 344) (outHigh : count ≤ output)
    (resLow : 344 ≤ reserve) (resHigh : reserve ≤ 816)
    (low : offset ≤ 344) (high : len ≤ offset)
    (apart : output + len ≤ offset ∨ offset + count ≤ output) :
    ∀ i < len, t.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      s.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  intro i hi
  apply frame
  intro region member contains
  have bounds := validCall_stack_bounds ctx.call
  have outNat := validCall_stack_sub_toNat ctx.call (offset := output) (by omega)
  have resNat := validCall_stack_sub_toNat ctx.call resHigh
  have address : (stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat =
      (stackPtr initial).toNat - offset + i := by
    rw [BitVec.toNat_add, validCall_stack_sub_toNat ctx.call (by omega), BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have cases : region = (⟨(stackPtr initial - BitVec.ofNat 64 output).toNat, count⟩ : MemoryRegion) ∨
      region = (⟨(stackPtr initial - BitVec.ofNat 64 reserve).toNat, reserve-344⟩ : MemoryRegion) := by
    simpa using member
  rcases cases with rfl | rfl
  · change (stackPtr initial - BitVec.ofNat 64 output).toNat ≤ _ ∧
      _ < (stackPtr initial - BitVec.ofNat 64 output).toNat + count at contains
    rw [outNat, address] at contains
    rcases apart with apart | apart <;> omega
  · change (stackPtr initial - BitVec.ofNat 64 reserve).toNat ≤ _ ∧
      _ < (stackPtr initial - BitVec.ofNat 64 reserve).toNat + (reserve-344) at contains
    rw [resNat, address] at contains
    omega

theorem hashState_of_bytes {s t : RamState} {a b : BitVec 64} {hash : Array UInt32}
    (input : Common.SHA256.HashStateAt s a hash)
    (bytes : ∀ i < 32, t.external[b + BitVec.ofNat 64 i]? = s.external[a + BitVec.ofNat 64 i]?) :
    Common.SHA256.HashStateAt t b hash := by
  refine ⟨input.1, fun i hi => ?_⟩
  have eq (j : Nat) (hj : j < 4) :
      t.external[b + BitVec.ofNat 64 (4*i) + BitVec.ofNat 64 j]? =
      s.external[a + BitVec.ofNat 64 (4*i) + BitVec.ofNat 64 j]? := by
    simpa only [BitVec.add_assoc, ← BitVec.ofNat_add] using bytes (4*i+j) (by omega)
  have h0 := eq 0 (by decide)
  have h1 := eq 1 (by decide)
  have h2 := eq 2 (by decide)
  have h3 := eq 3 (by decide)
  have raw := input.2 i hi
  simp only [loadBytes, loadBytes.loop, addAddress, fromNat, Nat.zero_add, Nat.reduceAdd] at raw ⊢
  rw [h0, h1, h2, h3]
  split at raw <;> try contradiction
  split at raw <;> try contradiction
  split at raw <;> try contradiction
  split at raw <;> try contradiction
  simp_all only

theorem stack_add {initial s : RamState} (rsp : stackPtr s = stackPtr initial - 344)
    {offset : Nat} (ho : offset ≤ 344) :
    rspOf s + BitVec.ofNat 64 offset = stackPtr initial - BitVec.ofNat 64 (344-offset) := by
  change stackPtr s + _ = _
  rw [rsp, ← BitVec.ofNat_sub_ofNat_of_le 344 offset (by omega) ho]
  rw [BitVec.sub_eq_add_neg (stackPtr initial) (344#64 - BitVec.ofNat 64 offset), BitVec.neg_sub]
  simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.ofNat_eq_ofNat]

theorem register_block [Bindings] {initial s : RamState}
    {inputs : Array Input} {pc : Nat} {bytes : List UInt8}
    {effect : RamState → Effect}
    (ctx : Context initial inputs v) (input : Preserved initial s v)
    (block : Common.Field.AdvanceTriple (returnBoundary initial)
      (fun s => s.RIP = Extracted.textAddress + BitVec.ofNat 64 pc)
      (codeRange (Extracted.textAddress + BitVec.ofNat 64 pc) bytes) (Effect.post effect))
    (bound : pc + bytes.length ≤ 71757)
    (image : Extracted.textBytes.toListFrom pc bytes.length = bytes)
    (rip : s.RIP = Extracted.textAddress + BitVec.ofNat 64 pc)
    (noMem : ∀ c ∈ (effect s).components, ∀ a, ¬ c.Covers a)
    (kept4 : Component.reg 4 ∉ (effect s).components) (hdf : .df ∉ (effect s).components) :
    ∃ t, Preserved initial t v ∧ (effect s).Holds s t := by
  obtain ⟨_, t, run, ready, _, result⟩ := block s
    (supportedMachine_readyToStep input.machine)
    (programText_slice (programLoaded_codeIn input.loaded) pc bytes bound image) rip
  exact ⟨t, preserved_of_agrees ctx input run ready result.agrees
    (fun c hc a ha => (noMem c hc a ha).elim) kept4 hdf, result⟩


end Sha2.Proofs.Wrapper
