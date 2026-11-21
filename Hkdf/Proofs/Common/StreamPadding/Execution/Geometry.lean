import Hkdf.Proofs.Common.StreamPadding.Stages
import Hkdf.Proofs.Common.StreamPadding.Interface

set_option autoImplicit false

namespace Hkdf.Proofs.Common.StreamPadding.Execution

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Spec.Program Hkdf.Proofs.Program Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.Machine (stack_region_end memoryRegion_memReadable memoryRegion_contains_add)

variable [Bindings] {v : Variant} {initial s : RamState} {boundary : ReturnBoundary}
  {inputBytes : Nat}

omit [Bindings] in
private theorem frame_le_reserve (v : Variant) : v.frame + 344 ≤ v.reserve := by
  cases v <;> decide +kernel

private theorem stack_avoid (v : Variant)
    (pre : CalleePre initial boundary v.helperEntry inputBytes v.outputBytes v.reserve) :
    (Stack.region initial v.reserve).Avoids (fun a => InProgram a ∨ InPageTables a) :=
  pre.avoids _ (by simp)

theorem base_toNat (v : Variant)
    (pre : CalleePre initial boundary v.helperEntry inputBytes v.outputBytes v.reserve) :
    (base v initial).toNat = (stackPtr initial).toNat - v.frame :=
  CallFrame.stack_sub_toNat pre.stack (by have := frame_le_reserve v; omega)

omit [Bindings] in
theorem below_address (v : Variant) (initial : RamState) (offset : Nat) :
    base v initial - BitVec.ofNat 64 offset =
      stackPtr initial - BitVec.ofNat 64 (v.frame + offset) := by
  simp only [base, BitVec.ofNat_add, BitVec.sub_sub]

theorem local_address (v : Variant)
    (_pre : CalleePre initial boundary v.helperEntry inputBytes v.outputBytes v.reserve)
    (offset : Nat) (high : offset ≤ v.frame) :
    base v initial + BitVec.ofNat 64 offset =
      stackPtr initial - BitVec.ofNat 64 (v.frame-offset) := by
  have sum : BitVec.ofNat 64 v.frame =
      BitVec.ofNat 64 (v.frame-offset) + BitVec.ofNat 64 offset := by
    rw [←BitVec.ofNat_add, Nat.sub_add_cancel high]
  change stackPtr initial - BitVec.ofNat 64 v.frame + BitVec.ofNat 64 offset = _
  rw [sum, ←BitVec.sub_sub, BitVec.sub_add_cancel]

theorem below_toNat (v : Variant)
    (pre : CalleePre initial boundary v.helperEntry inputBytes v.outputBytes v.reserve)
    (offset : Nat) (high : v.frame + offset ≤ v.reserve) :
    (base v initial - BitVec.ofNat 64 offset).toNat =
      (stackPtr initial).toNat - (v.frame+offset) := by
  rw [below_address]
  exact CallFrame.stack_sub_toNat pre.stack high

theorem local_toNat (v : Variant)
    (pre : CalleePre initial boundary v.helperEntry inputBytes v.outputBytes v.reserve)
    (offset : Nat) (high : offset ≤ v.frame+8) :
    (base v initial + BitVec.ofNat 64 offset).toNat =
      (stackPtr initial).toNat - v.frame + offset := by
  have bounds := CallFrame.stack_bounds pre.stack
  have capacity := frame_le_reserve v
  have small : offset < 2^64 := by omega
  rw [BitVec.toNat_add, base_toNat v pre, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt (by omega)]

private theorem local_within_stack (v : Variant)
    (pre : CalleePre initial boundary v.helperEntry inputBytes v.outputBytes v.reserve)
    (offset len : Nat) (high : offset+len ≤ v.frame+8) :
    (Stack.region initial v.reserve).start ≤
      (base v initial + BitVec.ofNat 64 offset).toNat ∧
    (base v initial + BitVec.ofNat 64 offset).toNat + len ≤
      (Stack.region initial v.reserve).start + (Stack.region initial v.reserve).size := by
  rw [local_toNat v pre offset (by omega), stack_region_end]
  change (stackPtr initial).toNat-v.reserve ≤ (stackPtr initial).toNat-v.frame+offset ∧ _
  have bounds := CallFrame.stack_bounds pre.stack
  have capacity := frame_le_reserve v
  constructor <;> omega

theorem local_readable (v : Variant)
    (pre : CalleePre initial boundary v.helperEntry inputBytes v.outputBytes v.reserve)
    (running : CallFrame.Running initial boundary (regions v initial) s)
    (rsp : stackPtr s = base v initial) (offset len : Nat)
    (high : offset+len ≤ v.frame+8) :
    MemReadable s (stackPtr s + BitVec.ofNat 64 offset) len := by
  rw [rsp]
  obtain ⟨low, high⟩ := local_within_stack v pre offset len high
  apply memoryRegion_memReadable pre.stack.1 ?_ low high
  intro a ha
  exact Option.isSome_iff_exists.mp (running.allocated a
    (Option.isSome_iff_exists.mpr (pre.stack.2.1 a ha)))

theorem local_writable8 (v : Variant)
    (pre : CalleePre initial boundary v.helperEntry inputBytes v.outputBytes v.reserve)
    (running : CallFrame.Running initial boundary (regions v initial) s)
    (rsp : stackPtr s = base v initial) (offset : Nat)
    (high : offset+8 ≤ v.frame+8) (align : offset%8=0) :
    MemWritable s (stackPtr s + BitVec.ofNat 64 offset) 8 := by
  rw [rsp, local_address v pre offset (by omega)]
  apply CallFrame.stack_writable8 pre.stack (stack_avoid v pre) running.allocated
    (by have := frame_le_reserve v; omega)
  have aligned : v.frame%8=0 := by cases v <;> decide +kernel
  omega

theorem local_writable1 (v : Variant)
    (pre : CalleePre initial boundary v.helperEntry inputBytes v.outputBytes v.reserve)
    (running : CallFrame.Running initial boundary (regions v initial) s)
    (rsp : stackPtr s = base v initial) (offset : Nat) (high : offset<v.frame+8) :
    MemWritable s (stackPtr s + BitVec.ofNat 64 offset) 1 := by
  have readable := local_readable v pre running rsp offset 1 (by omega)
  refine MemWritable.of_not_reserved (by decide) readable.low readable.mem ?_
  intro i hi reserved
  apply stack_avoid v pre _ ?_ (.inr reserved)
  rw [rsp]
  obtain ⟨low, high⟩ := local_within_stack v pre offset 1 (by omega)
  exact memoryRegion_contains_add pre.stack.1 low high hi

theorem local_codeApart (v : Variant)
    (pre : CalleePre initial boundary v.helperEntry inputBytes v.outputBytes v.reserve)
    (rsp : stackPtr s = base v initial) (offset len : Nat) (code : BitVec 64) (codeLen : Nat)
    (high : offset+len≤v.frame+8)
    (span : ∀ i : Nat, i<codeLen → InProgram (code+BitVec.ofNat 64 i)) :
    RangeApart (stackPtr s+BitVec.ofNat 64 offset) len code codeLen := by
  intro i hi j hj eq
  apply stack_avoid v pre _ ?_ (.inl (span j hj))
  rw [←eq, rsp]
  obtain ⟨low, high⟩ := local_within_stack v pre offset len high
  exact memoryRegion_contains_add pre.stack.1 low high hi

omit [Bindings] in
theorem offset_component (p : BitVec 64) (offset len start size : Nat)
    (bound : p.toNat+start+size<2^32) (low : start≤offset)
    (high : offset+len≤start+size) :
    ∀ a, (Component.mem (p+BitVec.ofNat 64 offset) len).Covers a →
      (⟨(p+BitVec.ofNat 64 start).toNat,size⟩ : MemoryRegion).Contains a.toNat := by
  have toNat (n : Nat) (hn : n≤start+size) :
      (p+BitVec.ofNat 64 n).toNat = p.toNat+n := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : n<2^64), Nat.mod_eq_of_lt (by omega)]
  intro a ha
  obtain ⟨i, hi, rfl⟩ := ha
  apply memoryRegion_contains_add (region := ⟨(p+BitVec.ofNat 64 start).toNat,size⟩)
    (len := len) ?_ ?_ ?_ hi
  · change (p+BitVec.ofNat 64 start).toNat+size<2^32
    rw [toNat start (by omega)]
    exact bound
  · change (p+BitVec.ofNat 64 start).toNat≤(p+BitVec.ofNat 64 offset).toNat
    rw [toNat start (by omega), toNat offset (by omega)]
    omega
  · change (p+BitVec.ofNat 64 offset).toNat+len≤(p+BitVec.ofNat 64 start).toNat+size
    rw [toNat start (by omega), toNat offset (by omega)]
    omega

omit [Bindings] in
private theorem pc_span (v : Variant) (point : Point) (len : Nat) (bound : len≤128) :
    ∀ i : Nat, i<len → InProgram (v.pc point+BitVec.ofNat 64 i) := by
  have address : v.pc point = Extracted.textAddress +
      BitVec.ofNat 64 ((v.pc point).toNat-0x100000) := by
    cases v <;> cases point <;> decide +kernel
  have high : (v.pc point).toNat-0x100000+128<115149 := by
    cases v <;> cases point <;> decide +kernel
  intro i hi
  rw [address, BitVec.add_assoc, ←BitVec.ofNat_add]
  exact Hkdf.Proofs.Common.Machine.inProgram_of_textOffset _ (by omega)

theorem load_pre (v : Variant)
    (pre : CalleePre initial boundary v.helperEntry inputBytes v.outputBytes v.reserve)
    (running : CallFrame.Running initial boundary (regions v initial) s)
    (rsp : stackPtr s=base v initial) (rip : s.RIP=v.pc .entry) : Stages.LoadPre v s := by
  refine ⟨rip, ?_, ?_⟩
  · exact local_readable v pre running rsp (v.tail+63) 1 (by cases v <;> decide +kernel)
  · exact local_readable v pre running rsp v.counter 8 (by cases v <;> decide +kernel)

omit [Bindings] in
private theorem marker_address (v : Variant) (s : RamState) (remaining : Nat)
    (length : s.regValue v.lengthReg=BitVec.ofNat 64 remaining) :
    rspOf s+(.reg v.lengthIndex : Operand 64).read s+BitVec.ofNat 64 v.tail =
      stackPtr s+BitVec.ofNat 64 (v.tail+remaining) := by
  change stackPtr s+(.reg v.lengthIndex : Operand 64).read s+BitVec.ofNat 64 v.tail=_
  rw [Variant.lengthIndex, read_regIndex, BitVec.setWidth_eq]
  rw [length, BitVec.ofNat_add, BitVec.add_assoc,
    BitVec.add_comm (BitVec.ofNat 64 remaining)]

theorem mark_pre (v : Variant)
    (pre : CalleePre initial boundary v.helperEntry inputBytes v.outputBytes v.reserve)
    (running : CallFrame.Running initial boundary (regions v initial) s)
    (rsp : stackPtr s=base v initial) (rip : s.RIP=v.pc .mark)
    (remaining : Nat) (length : s.regValue v.lengthReg=BitVec.ofNat 64 remaining)
    (small : remaining<64) : Stages.MarkPre v s := by
  have high : v.tail+remaining<v.frame+8 := by cases v <;> simp only [Variant.tail, Variant.frame] <;> omega
  refine ⟨rip, ?_, ?_⟩
  · rw [marker_address v s remaining length]
    exact local_writable1 v pre running rsp (v.tail+remaining) high
  · rw [marker_address v s remaining length]
    exact local_codeApart v pre rsp (v.tail+remaining) 1 (v.pc .mark) 19
      (by omega) (pc_span v .mark 19 (by decide))

theorem copy_pre (v : Variant) (last : Bool)
    (pre : CalleePre initial boundary v.helperEntry inputBytes v.outputBytes v.reserve)
    (running : CallFrame.Running initial boundary (regions v initial) s)
    (rsp : stackPtr s=base v initial) (rip : s.RIP=Stages.copyStart v last) :
    Stages.CopyPre v last s := by
  have codeSize : (Stages.copyBytes v last).length≤128 := by
    cases v <;> cases last <;> decide +kernel
  refine ⟨rip, ?_, ?_, ?_⟩
  · intro i hi
    have bound : i<8 := by cases last <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hi <;> omega
    exact local_readable v pre running rsp (v.tail+8*i) 8
      (by cases v <;> simp only [Variant.tail, Variant.frame] <;> omega)
  · intro i hi
    apply local_writable8 v pre running rsp (v.scratch+8*i)
    · cases v <;> simp only [Variant.scratch, Variant.frame] <;> omega
    · cases v <;> simp only [Variant.scratch] <;> omega
  · intro i hi
    exact local_codeApart v pre rsp (v.scratch+8*i) 8 (Stages.copyStart v last)
      (Stages.copyBytes v last).length
      (by cases v <;> simp only [Variant.scratch, Variant.frame] <;> omega)
      (pc_span v (if last then .lastHead else .firstHead) _ codeSize)

theorem zero_pre (v : Variant)
    (pre : CalleePre initial boundary v.helperEntry inputBytes v.outputBytes v.reserve)
    (running : CallFrame.Running initial boundary (regions v initial) s)
    (rsp : stackPtr s=base v initial) (rip : s.RIP=v.pc .zero) : Stages.ZeroPre v s := by
  have offsetBounds (i : Nat) (member : i∈([0,8,16,24,32,40,48] : List Nat)) :
      i≤48 ∧ i%8=0 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    omega
  refine ⟨rip, ?_, ?_⟩
  · intro i hi
    have bounds := offsetBounds i hi
    apply local_writable8 v pre running rsp (v.tail+i)
    · cases v <;> simp only [Variant.tail, Variant.frame] <;> omega
    · cases v <;> simp only [Variant.tail] <;> omega
  · intro i hi
    have bounds := offsetBounds i hi
    exact local_codeApart v pre rsp (v.tail+i) 8 (v.pc .zero) 63
      (by cases v <;> simp only [Variant.tail, Variant.frame] <;> omega)
      (pc_span v .zero 63 (by decide))

theorem length_pre (v : Variant)
    (pre : CalleePre initial boundary v.helperEntry inputBytes v.outputBytes v.reserve)
    (running : CallFrame.Running initial boundary (regions v initial) s)
    (rsp : stackPtr s=base v initial) (rip : s.RIP=v.pc .length) : Stages.LengthPre v s := by
  refine ⟨rip, ?_, ?_⟩
  · exact local_writable8 v pre running rsp (v.tail+56)
      (by cases v <;> decide +kernel) (by cases v <;> decide +kernel)
  · exact local_codeApart v pre rsp (v.tail+56) 8 (v.pc .length) (Stages.lengthByteCount v)
      (by cases v <;> decide +kernel)
      (pc_span v .length _ (by cases v <;> decide +kernel))

theorem local_bounds (v : Variant)
    (pre : CalleePre initial boundary v.helperEntry inputBytes v.outputBytes v.reserve)
    (rsp : stackPtr s=base v initial) :
    344≤(stackPtr s).toNat ∧ (stackPtr s).toNat+v.frame+8<2^32 := by
  rw [rsp, base_toNat v pre]
  have bounds := CallFrame.stack_bounds pre.stack
  have capacity := frame_le_reserve v
  constructor <;> omega

theorem writes_within_regions (v : Variant)
    (pre : CalleePre initial boundary v.helperEntry inputBytes v.outputBytes v.reserve) :
    ∀ region∈writes v (base v initial), ∀ a, region.Contains a →
      ∃ outer∈regions v initial, outer.Contains a := by
  have bounds := CallFrame.stack_bounds pre.stack
  have capacity := frame_le_reserve v
  intro region member a contains
  refine ⟨Stack.region initial v.reserve, by simp [regions], ?_⟩
  have localRegion (offset len : Nat) (high : offset+len≤v.frame+8)
      (hc : (⟨(base v initial+BitVec.ofNat 64 offset).toNat,len⟩ : MemoryRegion).Contains a) :
      (Stack.region initial v.reserve).Contains a := by
    obtain ⟨low, high⟩ := local_within_stack v pre offset len high
    change (base v initial+BitVec.ofNat 64 offset).toNat≤a ∧
      a<(base v initial+BitVec.ofNat 64 offset).toNat+len at hc
    exact ⟨Nat.le_trans low hc.1, Nat.lt_of_lt_of_le hc.2 high⟩
  have cases : region=⟨(base v initial-BitVec.ofNat 64 344).toNat,344⟩ ∨
      region=⟨(base v initial+BitVec.ofNat 64 v.tail).toNat,64⟩ ∨
      region=⟨(base v initial+BitVec.ofNat 64 v.hash).toNat,32⟩ ∨
      region=⟨(base v initial+BitVec.ofNat 64 v.scratch).toNat,64⟩ := by
    simpa only [writes, Vector.mem_mk, List.mem_toArray, List.mem_cons,
      List.not_mem_nil, or_false, BitVec.ofNat_eq_ofNat] using member
  rcases cases with rfl | rfl | rfl | rfl
  · change (base v initial-BitVec.ofNat 64 344).toNat≤a ∧ a<(base v initial-BitVec.ofNat 64 344).toNat+344 at contains
    rw [below_toNat v pre 344 capacity] at contains
    change (stackPtr initial).toNat-v.reserve≤a ∧
      a<(Stack.region initial v.reserve).start+(Stack.region initial v.reserve).size
    rw [stack_region_end]
    constructor <;> omega
  · exact localRegion v.tail 64 (by cases v <;> decide +kernel) contains
  · exact localRegion v.hash 32 (by cases v <;> decide +kernel) contains
  · exact localRegion v.scratch 64 (by cases v <;> decide +kernel) contains

theorem regions_avoids (v : Variant)
    (pre : CalleePre initial boundary v.helperEntry inputBytes v.outputBytes v.reserve) :
    ∀ region∈regions v initial, region.Avoids InProgram := by
  intro region member a contains code
  apply pre.avoids region (by simpa [regions] using member) a contains (.inl code)

theorem writes_avoids (v : Variant)
    (pre : CalleePre initial boundary v.helperEntry inputBytes v.outputBytes v.reserve) :
    ∀ region∈writes v (base v initial), region.Avoids InProgram := by
  intro region member a contains code
  obtain ⟨outer, ho, hc⟩ := writes_within_regions v pre region member a.toNat contains
  exact regions_avoids v pre outer ho a hc code

theorem call_writable (v : Variant)
    (pre : CalleePre initial boundary v.helperEntry inputBytes v.outputBytes v.reserve)
    (running : CallFrame.Running initial boundary (regions v initial) s)
    (rsp : stackPtr s=base v initial) : MemWritable s (pushAddr s) 8 := by
  change MemWritable s (stackPtr s-BitVec.ofNat 64 8) 8
  rw [rsp]
  change MemWritable s (base v initial-BitVec.ofNat 64 8) 8
  rw [below_address v initial 8]
  exact CallFrame.stack_writable8 pre.stack (stack_avoid v pre) running.allocated
    (by have := frame_le_reserve v; omega) (by cases v <;> decide +kernel)

theorem call_codeApart (v : Variant)
    (pre : CalleePre initial boundary v.helperEntry inputBytes v.outputBytes v.reserve)
    (rsp : stackPtr s=base v initial) (codeOffset codeLen : Nat)
    (bound : codeOffset+codeLen≤115149) :
    RangeApart (pushAddr s) 8 (Extracted.textAddress+BitVec.ofNat 64 codeOffset) codeLen := by
  change RangeApart (stackPtr s-BitVec.ofNat 64 8) 8 _ _
  rw [rsp]
  change RangeApart (base v initial-BitVec.ofNat 64 8) 8 _ _
  rw [below_address v initial 8]
  exact CallFrame.stack_codeApart pre.stack
    (fun a ha hp => stack_avoid v pre a ha (.inl hp))
    (by have := frame_le_reserve v; omega) (by omega) bound

theorem call_stack_region (v : Variant)
    (pre : CalleePre initial boundary v.helperEntry inputBytes v.outputBytes v.reserve)
    {c : RamState} (rspC : stackPtr c=base v initial-BitVec.ofNat 64 8) (reserve : Nat)
    (bound : v.frame+8+reserve≤v.reserve) :
    Stack.region c reserve =
      ⟨(base v initial-BitVec.ofNat 64 (8+reserve)).toNat,8+reserve⟩ := by
  have bounds := CallFrame.stack_bounds pre.stack
  have hsp : (stackPtr c).toNat=(stackPtr initial).toNat-(v.frame+8) := by
    rw [rspC]
    exact below_toNat v pre 8 (by omega)
  have hs := below_toNat v pre (8+reserve) (by omega)
  change (⟨(stackPtr c).toNat-reserve,
    (stackPtr c).toNat+8-((stackPtr c).toNat-reserve)⟩ : MemoryRegion)=_
  rw [hsp, hs]
  congr 1 <;> omega

theorem call_writes (v : Variant)
    (pre : CalleePre initial boundary v.helperEntry inputBytes v.outputBytes v.reserve)
    (rsp : stackPtr s=base v initial) (target : RamState→BitVec 64) (ret : BitVec 64) :
    WritesWithin (callEffect target ret s).components (writes v (base v initial)) := by
  have capacity := frame_le_reserve v
  have bounds := CallFrame.stack_bounds pre.stack
  intro component member a covered
  simp only [callEffect, pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact covered.elim
  · refine ⟨⟨(base v initial-BitVec.ofNat 64 344).toNat,344⟩, by simp [writes], ?_⟩
    obtain ⟨i, hi, rfl⟩ := covered
    change (⟨(base v initial-BitVec.ofNat 64 344).toNat,344⟩ : MemoryRegion).Contains
      (pushAddr s+BitVec.ofNat 64 i).toNat
    apply memoryRegion_contains_add (len := 8) ?_ ?_ ?_ hi
    · change (base v initial-BitVec.ofNat 64 344).toNat+344<2^32
      rw [below_toNat v pre 344 capacity]
      omega
    · change (base v initial-BitVec.ofNat 64 344).toNat≤(pushAddr s).toNat
      change (base v initial-BitVec.ofNat 64 344).toNat≤(stackPtr s-BitVec.ofNat 64 8).toNat
      rw [rsp, below_toNat v pre 344 capacity, below_toNat v pre 8 (by omega)]
      omega
    · change (pushAddr s).toNat+8≤(base v initial-BitVec.ofNat 64 344).toNat+344
      change (stackPtr s-BitVec.ofNat 64 8).toNat+8≤(base v initial-BitVec.ofNat 64 344).toNat+344
      rw [rsp, below_toNat v pre 344 capacity, below_toNat v pre 8 (by omega)]
      omega
  · exact covered.elim

theorem compression_within_writes (v : Variant)
    (pre : CalleePre initial boundary v.helperEntry inputBytes v.outputBytes v.reserve)
    {c : RamState} (rspC : stackPtr c=base v initial-BitVec.ofNat 64 8)
    (output : c.regValue .rdi=base v initial+BitVec.ofNat 64 v.hash) :
    ∀ region∈#v[registerRegion c .rdi 32,Stack.region c 336], ∀ a, region.Contains a →
      ∃ outer∈writes v (base v initial), outer.Contains a := by
  intro region member a contains
  have cases : region=registerRegion c .rdi 32 ∨ region=Stack.region c 336 := by simpa using member
  rcases cases with rfl | rfl
  · refine ⟨⟨(base v initial+BitVec.ofNat 64 v.hash).toNat,32⟩, by simp [writes], ?_⟩
    change (c.regValue .rdi).toNat≤a ∧ a<(c.regValue .rdi).toNat+32 at contains
    simpa only [output, MemoryRegion.Contains] using contains
  · rw [call_stack_region v pre rspC 336 (by have := frame_le_reserve v; omega)] at contains
    exact ⟨⟨(base v initial-BitVec.ofNat 64 344).toNat,344⟩, by simp [writes], contains⟩

theorem fill_within_writes (v : Variant)
    (pre : CalleePre initial boundary v.helperEntry inputBytes v.outputBytes v.reserve)
    {c : RamState} {position : Nat} (rspC : stackPtr c=base v initial-BitVec.ofNat 64 8)
    (output : c.regValue .rdi=base v initial+BitVec.ofNat 64 (v.tail+position))
    (len : Nat) (bound : position+len≤64) :
    ∀ region∈#v[registerRegion c .rdi len,Stack.region c 0], ∀ a, region.Contains a →
      ∃ outer∈writes v (base v initial), outer.Contains a := by
  have bounds := CallFrame.stack_bounds pre.stack
  have capacity := frame_le_reserve v
  intro region member a contains
  have cases : region=registerRegion c .rdi len ∨ region=Stack.region c 0 := by simpa using member
  rcases cases with rfl | rfl
  · refine ⟨⟨(base v initial+BitVec.ofNat 64 v.tail).toNat,64⟩, by simp [writes], ?_⟩
    change (c.regValue .rdi).toNat≤a ∧ a<(c.regValue .rdi).toNat+len at contains
    rw [output, local_toNat v pre (v.tail+position)
      (by cases v <;> simp only [Variant.tail,Variant.frame] <;> omega)] at contains
    change (base v initial+BitVec.ofNat 64 v.tail).toNat≤a ∧
      a<(base v initial+BitVec.ofNat 64 v.tail).toNat+64
    rw [local_toNat v pre v.tail (by cases v <;> decide +kernel)]
    constructor <;> omega
  · rw [call_stack_region v pre rspC 0 (by omega)] at contains
    refine ⟨⟨(base v initial-BitVec.ofNat 64 344).toNat,344⟩, by simp [writes], ?_⟩
    change (base v initial-BitVec.ofNat 64 (8+0)).toNat≤a ∧
      a<(base v initial-BitVec.ofNat 64 (8+0)).toNat+(8+0) at contains
    rw [below_toNat v pre (8+0) (by omega)] at contains
    change (base v initial-BitVec.ofNat 64 344).toNat≤a ∧ a<(base v initial-BitVec.ofNat 64 344).toNat+344
    rw [below_toNat v pre 344 capacity]
    constructor <;> omega

end Hkdf.Proofs.Common.StreamPadding.Execution
