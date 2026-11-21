import Hkdf.Proofs.Common.Machine.Boundary
import Hkdf.Proofs.Wrapper.Memory
import Hkdf.Proofs.Common.CallFrame.Stack
import Hkdf.Proofs.Standard.Initialization.Hash
import Hkdf.Proofs.Standard.Memory
import Hkdf.Proofs.Common.SHA256.Correctness
import Hkdf.Proofs.Common.CallFrame.Stack
import X86Proofs.Instructions.Call.Triple

set_option autoImplicit false

namespace Hkdf.Proofs.Standard.Initialization

open Hkdf.Spec Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common
open Hkdf.Proofs.Common.CallFrame
open Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.SHA256

abbrev hashCallLayout (hashOffset : Nat) (bounds : 32 ≤ hashOffset ∧ hashOffset ≤ 520 ∧
      (hashOffset + 64 ≤ 400 ∨ 432 ≤ hashOffset)) :
    Hkdf.Proofs.Common.CallFrame.StackCallLayout hkdfSha256Extract.minStackBytes 64 32 336 :=
  ⟨528, 400, hashOffset, by decide, by decide +kernel, by decide, by omega,
    by decide, by omega, by omega⟩

abbrev innerCallLayout := hashCallLayout 464 (by decide)

def innerWriteRegions (initial : RamState) (hashBytes : Nat := 40)
    (hashOffset : Nat := 464) : Vector MemoryRegion 2 :=
  #v[⟨(stackPtr initial - BitVec.ofNat 64 864).toNat, 344⟩,
    ⟨(stackPtr initial - BitVec.ofNat 64 hashOffset).toNat, hashBytes⟩]

theorem inner_frame_agrees [Bindings] {initial s t : RamState} {hashBytes hashOffset : Nat}
    {salt : Option ByteArray} {inputs : Array Input}
    (ctx : Standard.Context initial salt inputs)
    (frame : MemoryWriteFrame s t (innerWriteRegions initial hashBytes hashOffset))
    {offset len : Nat} (low : offset ≤ 1792) (high : len ≤ offset + 8)
    (below : offset ≤ 520 ∨ 864 + len ≤ offset)
    (above : offset + hashBytes ≤ hashOffset ∨ hashOffset + len ≤ offset)
    (hashBound : hashOffset ≤ 1792 := by omega) :
    (Component.mem (stackPtr initial - BitVec.ofNat 64 offset) len).Agrees s t := by
  have bounds := Standard.stack_bounds ctx
  have address := Hkdf.Proofs.Common.CallFrame.stack_sub_toNat ctx.call.stack low
  have stackStart := Hkdf.Proofs.Common.CallFrame.stack_sub_toNat ctx.call.stack
    (offset := 864) (by decide)
  have hashStart := Hkdf.Proofs.Common.CallFrame.stack_sub_toNat ctx.call.stack
    (offset := hashOffset) hashBound
  apply frame_agrees_of_disjoint frame
  · rw [address]
    omega
  · intro region member a ha hb
    have choices : region = ⟨(stackPtr initial - BitVec.ofNat 64 864).toNat, 344⟩ ∨
        region = ⟨(stackPtr initial - BitVec.ofNat 64 hashOffset).toNat, hashBytes⟩ := by
      simpa only [innerWriteRegions, Vector.mem_mk, List.mem_toArray, List.mem_cons,
        List.not_mem_nil, or_false] using member
    rcases choices with rfl | rfl
    · change (stackPtr initial - BitVec.ofNat 64 offset).toNat ≤ a ∧
        a < (stackPtr initial - BitVec.ofNat 64 offset).toNat + len at ha
      change (stackPtr initial - BitVec.ofNat 64 864).toNat ≤ a ∧ a < (stackPtr initial - BitVec.ofNat 64 864).toNat + 344 at hb
      rw [address] at ha
      rw [stackStart] at hb
      rcases below with h | h <;> omega
    · change (stackPtr initial - BitVec.ofNat 64 offset).toNat ≤ a ∧
        a < (stackPtr initial - BitVec.ofNat 64 offset).toNat + len at ha
      change (stackPtr initial - BitVec.ofNat 64 hashOffset).toNat ≤ a ∧
        a < (stackPtr initial - BitVec.ofNat 64 hashOffset).toNat + hashBytes at hb
      rw [address] at ha
      rw [hashStart] at hb
      rcases above with h | h <;> omega

theorem inner_preserved_of_frame [Bindings] {initial s t : RamState} {hashOffset hashBytes : Nat}
    {salt : Option ByteArray} {inputs : Array Input}
    (ctx : Standard.Context initial salt inputs) (state : Standard.Preserved initial s)
    (running : Running initial (returnBoundary initial)
      #v[Stack.region initial hkdfSha256Extract.minStackBytes] t)
    (frame : MemoryWriteFrame s t (innerWriteRegions initial hashBytes hashOffset))
    (rsp : t.regValue .rsp = frameBase initial)
    (hashBounds : hashOffset ≤ 504 ∧ 48 + hashBytes ≤ hashOffset ∧
      (hashOffset ≤ 400 ∨ 424 + hashBytes ≤ hashOffset) := by omega) :
    Standard.Preserved initial t := by
  apply state.of_observations running
  · exact inner_frame_agrees ctx frame (offset := 48) (by omega) (by omega)
      (by omega) (by omega)
  · intro offset member
    have address : frameBase initial + BitVec.ofNat 64 offset =
        stackPtr initial - BitVec.ofNat 64 (520-offset) := by
      have bound : offset ≤ 520 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl <;> decide
      have addr := Standard.stack_address state.rsp bound
      change rspOf s + BitVec.ofNat 64 offset = _ at addr
      rw [show rspOf s = frameBase initial from state.rsp] at addr
      exact addr
    rw [address]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    all_goals exact inner_frame_agrees ctx frame (by omega) (by omega) (by omega) (by omega)
  · exact rsp

theorem hash_write_regions_within [Bindings] {initial : RamState} {hashOffset hashBytes : Nat}
    {salt : Option ByteArray} {inputs : Array Input}
    (ctx : Standard.Context initial salt inputs)
    (hashBound : hashBytes ≤ hashOffset ∧ hashOffset ≤ 1792) :
    ∀ region ∈ innerWriteRegions initial hashBytes hashOffset, ∀ a, region.Contains a →
      (Stack.region initial hkdfSha256Extract.minStackBytes).Contains a := by
  have bounds := Standard.stack_bounds ctx
  intro region member a ha
  have choices : region = ⟨(stackPtr initial - BitVec.ofNat 64 864).toNat, 344⟩ ∨
      region = ⟨(stackPtr initial - BitVec.ofNat 64 hashOffset).toNat, hashBytes⟩ := by
    simpa only [innerWriteRegions, Vector.mem_mk, List.mem_toArray, List.mem_cons,
      List.not_mem_nil, or_false] using member
  rcases choices with rfl | rfl
  all_goals change _ ≤ a ∧ a < _ at ha
  all_goals change (Stack.region initial 1792).Contains a
  all_goals unfold MemoryRegion.Contains
  all_goals rw [Hkdf.Proofs.Common.Machine.stack_region_end]
  all_goals change (stackPtr initial).toNat - 1792 ≤ a ∧ a < (stackPtr initial).toNat + 8
  · have start := Hkdf.Proofs.Common.CallFrame.stack_sub_toNat ctx.call.stack (offset := 864) (by decide)
    change (stackPtr initial - BitVec.ofNat 64 864).toNat ≤ a ∧
      a < (stackPtr initial - BitVec.ofNat 64 864).toNat + 344 at ha
    rw [start] at ha
    constructor <;> omega
  · have start := Hkdf.Proofs.Common.CallFrame.stack_sub_toNat ctx.call.stack (offset := hashOffset) hashBound.2
    change (stackPtr initial - BitVec.ofNat 64 hashOffset).toNat ≤ a ∧
      a < (stackPtr initial - BitVec.ofNat 64 hashOffset).toNat + hashBytes at ha
    rw [start] at ha
    constructor <;> omega

theorem inner_rodata_program {j k : Nat} (hj : j < 4) (hk : k < 8) :
    InProgram (0x200ee0 + BitVec.ofNat 64 (8*j) + BitVec.ofNat 64 k) := by
  have offset : 3808 + 8*j + k < Extracted.rodataBytes.toList.length := by
    rw [chunked_toList_length, rodataBytes_size]
    omega
  have address : (0x200ee0 + BitVec.ofNat 64 (8*j) + BitVec.ofNat 64 k : BitVec 64) =
      Extracted.rodataAddress + BitVec.ofNat 64 (3808 + 8*j + k) := by
    simp only [Extracted.rodataAddress, BitVec.ofNat_add, ← BitVec.add_assoc,
      BitVec.ofNat_eq_ofNat, BitVec.reduceAdd]
  rw [address]
  refine ⟨Extracted.rodataBytes.toList[3808+8*j+k], ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨⟨Extracted.rodataAddress, Extracted.rodataBytes⟩,
    by simp [Extracted.programSections], ?_⟩
  exact (mem_codeRange_iff _ _ _).mpr ⟨⟨3808+8*j+k, offset⟩, rfl⟩

theorem inner_rodata_apart [Bindings] {initial s : RamState}
    {salt : Option ByteArray} {inputs : Array Input}
    (ctx : Standard.Context initial salt inputs) (state : Standard.Preserved initial s)
    {offset j : Nat} (bound : offset + 8 ≤ 520) (hj : j < 4) :
    RangeApart (rspOf s + BitVec.ofNat 64 offset) 8
      (0x200ee0 + BitVec.ofNat 64 (8*j)) 8 := by
  rw [Standard.stack_address state.rsp (by omega)]
  intro i hi k hk eq
  apply (ctx.call.stackSeparation.2 (Stack.region initial hkdfSha256Extract.minStackBytes)
    (by simp)).2 (stackPtr initial - BitVec.ofNat 64 (520-offset) + BitVec.ofNat 64 i) ?_ (.inl ?_)
  · exact Hkdf.Proofs.Common.Machine.stackRegion_contains_sub ctx.call.stack.2.2.1
      (offset := 520-offset) (by change 520-offset ≤ 1792; omega) (by omega) ⟨i, hi, rfl⟩
  · rw [eq]
    exact inner_rodata_program hj hk

theorem hash_output_memory [Bindings] {initial s : RamState} {hashOffset hashBytes : Nat}
    {salt : Option ByteArray} {inputs : Array Input}
    (ctx : Standard.Context initial salt inputs) (state : Standard.Preserved initial s)
    {offset len : Nat} (low : 520-hashOffset ≤ offset) (high : offset+len ≤ 520-hashOffset+hashBytes)
    (hashBound : hashBytes ≤ hashOffset ∧ hashOffset ≤ 520)
    {a : BitVec 64} (cover : (Component.mem (rspOf s + BitVec.ofNat 64 offset) len).Covers a) :
    (⟨(stackPtr initial - BitVec.ofNat 64 hashOffset).toNat, hashBytes⟩ : MemoryRegion).Contains
      a.toNat := by
  obtain ⟨i, hi, rfl⟩ := cover
  have bounds := Standard.stack_bounds ctx
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, Standard.stack_address state.rsp (by omega)]
  rw [Hkdf.Proofs.Common.CallFrame.stack_sub_toNat ctx.call.stack (offset := 520-(offset+i))
    (by change 520-(offset+i) ≤ 1792; omega)]
  change (stackPtr initial - BitVec.ofNat 64 hashOffset).toNat ≤ _ ∧
    _ < (stackPtr initial - BitVec.ofNat 64 hashOffset).toNat + hashBytes
  rw [Hkdf.Proofs.Common.CallFrame.stack_sub_toNat ctx.call.stack (offset := hashOffset)
    (by change hashOffset ≤ 1792; omega)]
  constructor <;> omega

theorem inner_stack_memory [Bindings] {initial : RamState}
    {salt : Option ByteArray} {inputs : Array Input}
    (ctx : Standard.Context initial salt inputs) {offset len : Nat}
    (low : offset ≤ 864) (high : 520+len ≤ offset)
    {a : BitVec 64} (cover : (Component.mem
      (stackPtr initial - BitVec.ofNat 64 offset) len).Covers a) :
    (⟨(stackPtr initial - BitVec.ofNat 64 864).toNat, 344⟩ : MemoryRegion).Contains a.toNat := by
  have bounds := Standard.stack_bounds ctx
  have start := Hkdf.Proofs.Common.CallFrame.stack_sub_toNat ctx.call.stack (offset := 864) (by decide)
  have addr := Hkdf.Proofs.Common.CallFrame.stack_sub_toNat ctx.call.stack
    (offset := offset) (by change offset ≤ 1792; omega)
  obtain ⟨i, hi, rfl⟩ := cover
  apply Hkdf.Proofs.Common.Machine.memoryRegion_contains_add
    (region := ⟨(stackPtr initial - BitVec.ofNat 64 864).toNat, 344⟩) (len := len) ?_ ?_ ?_ hi
  · change (stackPtr initial - BitVec.ofNat 64 864).toNat + 344 < 2^32
    rw [start]
    omega
  · change (stackPtr initial - BitVec.ofNat 64 864).toNat ≤
      (stackPtr initial - BitVec.ofNat 64 offset).toNat
    rw [start, addr]
    omega
  · change (stackPtr initial - BitVec.ofNat 64 offset).toNat + len ≤
      (stackPtr initial - BitVec.ofNat 64 864).toNat + 344
    rw [start, addr]
    omega

theorem inner_frame_mono {initial s t : RamState} {hashOffset : Nat} {small large : Nat}
    (frame : MemoryWriteFrame s t (innerWriteRegions initial small hashOffset))
    (size : small ≤ large) :
    MemoryWriteFrame s t (innerWriteRegions initial large hashOffset) := by
  apply CallFrame.frame_mono frame
  intro region member a contains
  have choices : region = ⟨(stackPtr initial - BitVec.ofNat 64 864).toNat, 344⟩ ∨
      region = ⟨(stackPtr initial - BitVec.ofNat 64 hashOffset).toNat, small⟩ := by
    simpa [innerWriteRegions] using member
  rcases choices with rfl | rfl
  · exact ⟨_, by simp [innerWriteRegions], contains⟩
  · refine ⟨⟨(stackPtr initial - BitVec.ofNat 64 hashOffset).toNat, large⟩,
      by simp [innerWriteRegions], ?_⟩
    change (stackPtr initial - BitVec.ofNat 64 hashOffset).toNat ≤ a ∧
      a < (stackPtr initial - BitVec.ofNat 64 hashOffset).toNat + small at contains
    change (stackPtr initial - BitVec.ofNat 64 hashOffset).toNat ≤ a ∧
      a < (stackPtr initial - BitVec.ofNat 64 hashOffset).toNat + large
    exact ⟨contains.1, by omega⟩

theorem hash_zero_frame {initial s t : RamState} {hashOffset bytes : Nat}
    (frame : MemoryWriteFrame s t (innerWriteRegions initial 0)) :
    MemoryWriteFrame s t (innerWriteRegions initial bytes hashOffset) := by
  apply CallFrame.frame_mono frame
  intro region member a contains
  have choices : region = ⟨(stackPtr initial - BitVec.ofNat 64 864).toNat, 344⟩ ∨
      region = ⟨(stackPtr initial - BitVec.ofNat 64 464).toNat, 0⟩ := by
    simpa [innerWriteRegions] using member
  rcases choices with rfl | rfl
  · exact ⟨_, by simp [innerWriteRegions], contains⟩
  · have h := contains.2
    have h' := contains.1
    change (stackPtr initial - BitVec.ofNat 64 464).toNat ≤ a at h'
    change a < (stackPtr initial - BitVec.ofNat 64 464).toNat + 0 at h
    omega

theorem inner_hasBytes_of_frame [Bindings] {initial s t : RamState} {hashOffset : Nat} {hashBytes : Nat}
    {salt : Option ByteArray} {inputs : Array Input} {bytes : ByteArray}
    (ctx : Standard.Context initial salt inputs)
    (frame : MemoryWriteFrame s t (innerWriteRegions initial hashBytes hashOffset))
    {offset len : Nat} (low : offset ≤ 1792) (high : len ≤ offset+8)
    (below : offset ≤ 520 ∨ 864+len ≤ offset)
    (above : offset+hashBytes ≤ hashOffset ∨ hashOffset+len ≤ offset)
    (stored : (⟨(stackPtr initial - BitVec.ofNat 64 offset).toNat, len⟩ : MemoryRegion).HasBytes
      s.external bytes)
    (hashBound : hashOffset ≤ 1792 := by omega) :
    (⟨(stackPtr initial - BitVec.ofNat 64 offset).toNat, len⟩ : MemoryRegion).HasBytes
      t.external bytes := by
  have same := inner_frame_agrees ctx frame low high below above hashBound
  refine ⟨stored.1, ?_⟩
  intro i
  have hi : i.val < len := by
    have h := stored.1
    change bytes.size = len at h
    rw [← h]
    exact i.isLt
  have equal := same i.val hi
  have before := stored.2 i
  simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at before ⊢
  exact equal.trans before

theorem hash_call [Bindings] {initial u : RamState} {pc ret : BitVec 64} {code : CodeMap}
    {salt : Option ByteArray} {inputs : Array Input}
    (ctx : Standard.Context initial salt inputs) (state : Standard.Preserved initial u)
    (ready : ReadyToStep u) (rip : u.RIP = pc)
    (step : StepEffect (PushPre pc 5) code (callEffect (fun _ => 0x1095c0) ret))
    (instruction : CodeIn code u)
    (apart : RangeApart (stackPtr initial - BitVec.ofNat 64 528) 8 pc 5) :
    ∃ v, Advances (returnBoundary initial) 1 u v ∧ ReadyToStep v ∧
      Running initial (returnBoundary initial)
        #v[Stack.region initial hkdfSha256Extract.minStackBytes] v ∧
      (callEffect (fun _ => 0x1095c0) ret u).Holds u v ∧
      MemoryWriteFrame u v (innerWriteRegions initial 0) ∧
      stackPtr v = stackPtr initial - BitVec.ofNat 64 528 ∧
      returnBoundary v = ⟨ret, frameBase initial⟩ := by
  have pushed : pushAddr u = stackPtr initial - BitVec.ofNat 64 528 := by
    change stackPtr u - 8 = _
    rw [show stackPtr u = frameBase initial from state.rsp]
    change stackPtr initial - BitVec.ofNat 64 520 - BitVec.ofNat 64 8 = _
    rw [BitVec.sub_sub]
    rfl
  obtain ⟨v, run, readyV, effect⟩ := step.advances ready instruction
    ⟨rip, by
      rw [pushed]
      exact CallFrame.stack_writable8 ctx.call.stack
        (ctx.call.stackSeparation.2 _ (by simp)).2 state.allocated (by decide) (by decide), by
      rw [pushed]
      exact apart⟩
    (boundary_ne_program (Standard.returnBoundary_valid ctx).2.2
      (inProgram_of_textOffset 0x95c0 (by decide)))
  have writes : WritesWithin (callEffect (fun _ => (0x1095c0 : BitVec 64)) ret u).components
      (innerWriteRegions initial 0) := by
    intro c hc a ha
    simp only [callEffect, pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact ha.elim
    · rw [pushed] at ha
      exact ⟨⟨(stackPtr initial - BitVec.ofNat 64 864).toNat, 344⟩, by simp [innerWriteRegions],
        inner_stack_memory ctx (by decide) (by decide) ha⟩
    · exact ha.elim
  have frame := effect.agrees.memoryWriteFrame writes
  have within : ∀ region ∈ innerWriteRegions initial 0, ∀ a, region.Contains a →
      (Stack.region initial hkdfSha256Extract.minStackBytes).Contains a := by
    intro region member a contains
    have choose : region = ⟨(stackPtr initial - BitVec.ofNat 64 864).toNat, 344⟩ ∨
        region = ⟨(stackPtr initial - BitVec.ofNat 64 464).toNat, 0⟩ := by
      simpa [innerWriteRegions] using member
    rcases choose with rfl | rfl
    · exact hash_write_regions_within (hashOffset := 464) (hashBytes := 40) ctx (by decide)
        _ (by simp [innerWriteRegions]) a contains
    · apply hash_write_regions_within (hashOffset := 464) (hashBytes := 40) ctx (by decide)
        ⟨(stackPtr initial - BitVec.ofNat 64 464).toNat, 40⟩ (by simp [innerWriteRegions]) a
      change (stackPtr initial - BitVec.ofNat 64 464).toNat ≤ a ∧
        a < (stackPtr initial - BitVec.ofNat 64 464).toNat + 40
      change (stackPtr initial - BitVec.ofNat 64 464).toNat ≤ a ∧
        a < (stackPtr initial - BitVec.ofNat 64 464).toNat + 0 at contains
      exact ⟨contains.1, by omega⟩
  have running := state.toRunning.of_agrees run readyV effect.agrees
    (by intro c hc a ha
        obtain ⟨region, member, contains⟩ := writes c hc a ha
        exact ⟨Stack.region initial hkdfSha256Extract.minStackBytes, by simp,
          within region member a.toNat contains⟩)
    (by intro region member a contains inside
        exact (ctx.call.stackSeparation.2 region (by simpa using member)).2 a contains (.inl inside))
    (by simp [callEffect, pushEffect_components])
  refine ⟨v, run, readyV, running, effect, frame, effect.writes.1.trans pushed, ?_⟩
  rw [CallFrame.call_boundary effect, show stackPtr u = frameBase initial from state.rsp]

theorem inner_call [Bindings] {initial u : RamState}
    {salt : Option ByteArray} {inputs : Array Input}
    (ctx : Standard.Context initial salt inputs) (state : Standard.Preserved initial u)
    (ready : ReadyToStep u) (rip : u.RIP = 0x101506) :
    ∃ v, Advances (returnBoundary initial) 1 u v ∧ ReadyToStep v ∧
      Running initial (returnBoundary initial)
        #v[Stack.region initial hkdfSha256Extract.minStackBytes] v ∧
      (callEffect (fun _ => 0x1095c0) 0x10150b u).Holds u v ∧
      MemoryWriteFrame u v (innerWriteRegions initial 0) ∧
      stackPtr v = stackPtr initial - BitVec.ofNat 64 528 ∧
      returnBoundary v = ⟨0x10150b, frameBase initial⟩ := by
  apply hash_call ctx state ready rip
    (call_rel32_effect_step 0x101506 0x80b5 (by decide))
    (programText_slice (programLoaded_codeIn state.loaded) 0x1506 _
      (by decide) (by decide +kernel))
  exact Standard.stack_codeApart ctx (codeOffset := 0x1506) (by decide) (by decide) (by decide)

theorem hash_compression_frame [Bindings] {initial v t : RamState} {hashOffset : Nat}
    {salt : Option ByteArray} {inputs : Array Input}
    (ctx : Standard.Context initial salt inputs)
    (hashBounds : 32 ≤ hashOffset ∧ hashOffset ≤ 520 ∧
      (hashOffset + 64 ≤ 400 ∨ 432 ≤ hashOffset))
    (rsp : stackPtr v = stackPtr initial - BitVec.ofNat 64 528)
    (output : v.regValue .rdi = stackPtr initial - BitVec.ofNat 64 hashOffset)
    (frame : MemoryWriteFrame v t #v[registerRegion v .rdi 32, Stack.region v 336]) :
    MemoryWriteFrame v t (innerWriteRegions initial 32 hashOffset) := by
  have bounds := Standard.stack_bounds ctx
  obtain ⟨outStart, stackStart, stackEnd⟩ := stack_layout_bounds ctx.call.stack
    (hashCallLayout hashOffset hashBounds) rsp output
  have outerStack := Hkdf.Proofs.Common.CallFrame.stack_sub_toNat ctx.call.stack (offset := 864) (by decide)
  have outerHash := Hkdf.Proofs.Common.CallFrame.stack_sub_toNat ctx.call.stack (offset := hashOffset)
    (by change hashOffset ≤ 1792; omega)
  apply CallFrame.frame_mono frame
  intro region member a contains
  have cases : region = registerRegion v .rdi 32 ∨ region = Stack.region v 336 := by
    simpa using member
  rcases cases with rfl | rfl
  · refine ⟨⟨(stackPtr initial - BitVec.ofNat 64 hashOffset).toNat, 32⟩,
      by simp [innerWriteRegions], ?_⟩
    change (registerRegion v .rdi 32).start ≤ a ∧ a < (registerRegion v .rdi 32).start + 32 at contains
    change (stackPtr initial - BitVec.ofNat 64 hashOffset).toNat ≤ a ∧
      a < (stackPtr initial - BitVec.ofNat 64 hashOffset).toNat + 32
    rw [outerHash]
    simpa only [hashCallLayout] using (show (stackPtr initial).toNat - hashOffset ≤ a ∧
      a < (stackPtr initial).toNat - hashOffset + 32 from by simpa only [outStart] using contains)
  · refine ⟨⟨(stackPtr initial - BitVec.ofNat 64 864).toNat, 344⟩,
      by simp [innerWriteRegions], ?_⟩
    change (Stack.region v 336).start ≤ a ∧
      a < (Stack.region v 336).start + (Stack.region v 336).size at contains
    rw [stackEnd, stackStart] at contains
    change (stackPtr initial - BitVec.ofNat 64 864).toNat ≤ a ∧
      a < (stackPtr initial - BitVec.ofNat 64 864).toNat + 344
    rw [outerStack]
    change (stackPtr initial).toNat - (528+336) ≤ a ∧
      a < (stackPtr initial).toNat - 528 + 8 at contains
    constructor <;> omega

theorem hash_compression_pre [Bindings] {initial v : RamState} {hashOffset : Nat}
    {salt : Option ByteArray} {inputs : Array Input} {input : ByteArray} {hash : Array UInt32}
    (ctx : Standard.Context initial salt inputs)
    (hashBounds : 32 ≤ hashOffset ∧ hashOffset ≤ 520 ∧
      (hashOffset + 64 ≤ 400 ∨ 432 ≤ hashOffset))
    (hashAligned : hashOffset % 4 = 0)
    (running : Running initial (returnBoundary initial)
      #v[Stack.region initial hkdfSha256Extract.minStackBytes] v)
    (rip : v.RIP = 0x1095c0)
    (rsp : stackPtr v = stackPtr initial - BitVec.ofNat 64 528)
    (output : v.regValue .rdi = stackPtr initial - BitVec.ofNat 64 hashOffset)
    (source : v.regValue .rsi = stackPtr initial - BitVec.ofNat 64 400)
    (ret : InProgram (returnBoundary v).rip) (count : v.regValue .rdx = BitVec.ofNat 64 1)
    (bytes : (⟨(stackPtr initial - BitVec.ofNat 64 400).toNat, 64⟩ : MemoryRegion).HasBytes v.external input)
    (words : HashStateAt v (stackPtr initial - BitVec.ofNat 64 hashOffset)
      hash) :
    Common.SHA256.CompressionPre v (returnBoundary initial)
      hash input 1 := by
  refine ⟨callee_pre_of_stack ctx.environment.stringStride ctx.call.stack
    (ctx.call.stackSeparation.2 _ (by simp)).2 (Standard.returnBoundary_valid ctx).2.2
    running.machine running.directionFlag running.loaded running.allocated
    (hashCallLayout hashOffset hashBounds)
    rip rsp source output ret, ?_, count, ?_, ?_⟩
  · rw [output, Hkdf.Proofs.Common.CallFrame.stack_sub_toNat ctx.call.stack (offset := hashOffset)
      (by change hashOffset ≤ 1792; omega)]
    have aligned : (stackPtr initial).toNat % 16 = 8 := ctx.call.stack.2.2.2
    have bounds := Standard.stack_bounds ctx
    omega
  · change (⟨(v.regValue .rsi).toNat, 64⟩ : MemoryRegion).HasBytes _ _
    rw [source]
    exact bytes
  · rw [output]
    exact words


theorem inner_pre [Bindings] {initial s : RamState}
    {salt : Option ByteArray} {inputs : Array Input}
    (ctx : Standard.Context initial salt inputs) (state : Standard.Preserved initial s)
    (rip : s.RIP = 0x1014be) : InnerPre s := by
  refine ⟨rip, fun j hj => (iv_loaded state.loaded j hj).1, ?_, ?_, ?_⟩
  · intro offset member
    rw [Standard.stack_address state.rsp (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl <;> decide)]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    all_goals (exact CallFrame.stack_writable8 ctx.call.stack (ctx.call.stackSeparation.2 _ (by simp)).2 state.allocated (by decide) (by decide))
  · intro offset member
    rw [Standard.stack_address state.rsp (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl <;> decide)]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    all_goals (exact Standard.stack_codeApart ctx (codeOffset := 0x14be) (by decide) (by decide) (by decide))
  · intro m value offset member j hj
    apply memLoad_memStore_of_rangeApart
    apply inner_rodata_apart ctx state ?_ hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> decide

theorem inner_hash [Bindings] {initial s : RamState}
    {salt : Option ByteArray} {inputs : Array Input}
    (ctx : Standard.Context initial salt inputs) (ready : ReadyToStep s)
    (state : Standard.Preserved initial s) (rip : s.RIP = 0x1014be)
    (block : (⟨(hmacBase initial).toNat, 64⟩ : MemoryRegion).HasBytes s.external
      (HMAC.xorPad (HMAC.keyBlock (saltKey salt)) 0x36)) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ ReadyToStep t ∧
      InnerHashed initial t salt := by
  obtain ⟨stageFuel, u, stageRun, readyU, _, effect⟩ :=
    inner_stage_run (returnBoundary initial) (Standard.returnBoundary_valid ctx).2.2
      s ready (programText_slice (programLoaded_codeIn state.loaded) 0x14be innerBytes
        (by decide) (by decide +kernel)) (inner_pre ctx state rip)
  have writes : WritesWithin (innerEffect s).components (innerWriteRegions initial) := by
    intro c hc a ha
    simp only [innerEffect, Effect.components, List.map_cons, List.map_nil, Write.component,
      Operand.component, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals refine ⟨⟨(stackPtr initial - BitVec.ofNat 64 464).toNat, 40⟩,
      by simp [innerWriteRegions], ?_⟩
    all_goals exact hash_output_memory (hashBytes := 40) ctx state (by decide) (by decide) (by decide) ha
  have stageFrame := effect.agrees.memoryWriteFrame writes
  have runningU := state.toRunning.of_agrees stageRun readyU effect.agrees
    (by intro c hc a ha
        obtain ⟨region, member, contains⟩ := writes c hc a ha
        exact ⟨Stack.region initial hkdfSha256Extract.minStackBytes, by simp,
          hash_write_regions_within (hashOffset := 464) (hashBytes := 40) ctx (by decide)
            region member a.toNat contains⟩)
    (by intro region member a contains inside
        exact (ctx.call.stackSeparation.2 region (by simpa using member)).2 a contains (.inl inside))
    (by simp [innerEffect, Effect.components, Write.component, Operand.component])
  have rspU : u.regValue .rsp = frameBase initial :=
    (effect.agrees.read (n := 64) (r := 4)
      (by simp [innerEffect, Effect.components, Write.component, Operand.component])).trans state.rsp
  have stateU := inner_preserved_of_frame ctx state runningU stageFrame rspU
  have stores := effect.writes
  simp only [innerEffect, Write.AllHold] at stores
  have outputU : u.regValue .rdi = stackPtr initial - BitVec.ofNat 64 464 := by
    have value : (Operand.reg 7 : Operand 64).read u = rspOf s + BitVec.ofNat 64 56 := stores.2.2.2.2.2.2.2.2.2.1
    have addr := Standard.stack_address state.rsp (offset := 56) (by decide)
    rw [addr] at value
    exact value
  have inputU : u.regValue .rsi = stackPtr initial - BitVec.ofNat 64 400 := by
    have value : (Operand.reg 6 : Operand 64).read u = rspOf s + BitVec.ofNat 64 120 := stores.2.2.2.2.2.2.2.2.2.2.1
    have addr := Standard.stack_address state.rsp (offset := 120) (by decide)
    rw [addr] at value
    exact value
  have countU : u.regValue .rdx = BitVec.ofNat 64 1 := stores.2.2.2.2.2.2.2.2.2.2.2
  have blockAddress : hmacBase initial = stackPtr initial - BitVec.ofNat 64 400 := by
    have addr := Standard.stack_address state.rsp (offset := 120) (by decide)
    rw [show rspOf s = frameBase initial from state.rsp] at addr
    exact addr
  have blockU := inner_hasBytes_of_frame ctx stageFrame (offset := 400) (len := 64)
    (by decide) (by decide) (by decide) (by decide) (by simpa only [blockAddress] using block)
  have packed : ∀ j < 4, memLoad u.external
      (stackPtr initial - BitVec.ofNat 64 464 + BitVec.ofNat 64 (8*j)) 64 = ivWords[j]! := by
    intro j hj
    rw [← Standard.stack_address state.rsp (offset := 56) (by decide),
      BitVec.add_assoc, ← BitVec.ofNat_add]
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
    · have word := stores.2.2.2.2.2.2.2.1
      change memLoad u.external _ 64 = _ at word
      have iv := (iv_loaded state.loaded 0 (by decide)).2
      simp only [ivWords, List.getElem!_cons_zero,
        Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at iv
      simpa only [ivWords, List.getElem!_cons_zero, List.getElem!_cons_succ,
        rspOf, Operand.read, BitVec.setWidth_eq, Nat.reduceMul, Nat.reduceAdd,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero] using word.trans iv
    · have word := stores.2.2.2.2.2.2.1
      change memLoad u.external _ 64 = _ at word
      have iv := (iv_loaded state.loaded 1 (by decide)).2
      simp only [ivWords, List.getElem!_cons_zero, List.getElem!_cons_succ,
        Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at iv
      simpa only [ivWords, List.getElem!_cons_zero, List.getElem!_cons_succ,
        rspOf, Operand.read, BitVec.setWidth_eq, Nat.reduceMul, Nat.reduceAdd,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero] using word.trans iv
    · have word := stores.2.2.2.2.2.1
      change memLoad u.external _ 64 = _ at word
      have iv := (iv_loaded state.loaded 2 (by decide)).2
      simp only [ivWords, List.getElem!_cons_zero, List.getElem!_cons_succ,
        Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at iv
      simpa only [ivWords, List.getElem!_cons_zero, List.getElem!_cons_succ,
        rspOf, Operand.read, BitVec.setWidth_eq, Nat.reduceMul, Nat.reduceAdd,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero] using word.trans iv
    · have word := stores.2.2.2.2.1
      change memLoad u.external _ 64 = _ at word
      have iv := (iv_loaded state.loaded 3 (by decide)).2
      simp only [ivWords, List.getElem!_cons_zero, List.getElem!_cons_succ,
        Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at iv
      simpa only [ivWords, List.getElem!_cons_zero, List.getElem!_cons_succ,
        rspOf, Operand.read, BitVec.setWidth_eq, Nat.reduceMul, Nat.reduceAdd,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero] using word.trans iv
  have hashU : HashStateAt u (stackPtr initial - BitVec.ofNat 64 464)
      Hkdf.Proofs.NIST.SHA256.initialHash :=
    Key.Hash.Initialize.hashStateAt_initialHash_of_packedWords
      (Standard.stack_readable ctx stateU.toState (by decide) (by decide)) packed
  obtain ⟨v, callRun, readyV, runningV, callEffect, callFrame, rspV, retV⟩ :=
    inner_call ctx stateU readyU effect.rip
  have inputV : v.regValue .rsi = stackPtr initial - BitVec.ofNat 64 400 :=
    (callEffect.agrees.read (n := 64) (r := 6)
      (by simp [X86Proofs.callEffect, pushEffect_components])).trans inputU
  have outputV : v.regValue .rdi = stackPtr initial - BitVec.ofNat 64 464 :=
    (callEffect.agrees.read (n := 64) (r := 7)
      (by simp [X86Proofs.callEffect, pushEffect_components])).trans outputU
  have countV : v.regValue .rdx = BitVec.ofNat 64 1 :=
    (callEffect.agrees.read (n := 64) (r := 2)
      (by simp [X86Proofs.callEffect, pushEffect_components])).trans countU
  have blockV := inner_hasBytes_of_frame ctx callFrame (offset := 400) (len := 64)
    (by decide) (by decide) (by decide) (by decide) blockU
  have hashV := Hkdf.Proofs.Wrapper.hashState_of_bytes hashU
    (inner_frame_agrees ctx callFrame (offset := 464) (len := 32)
      (by decide) (by decide) (by decide) (by decide))
  have pre := hash_compression_pre ctx (by decide) (by decide) runningV callEffect.rip
    rspV outputV inputV
    (by rw [retV]; exact inProgram_of_textOffset 0x150b (by decide)) countV blockV hashV
  obtain ⟨t, result⟩ := Common.SHA256.compression_correct pre
  have resultFrame := hash_compression_frame ctx (by decide) rspV outputV result.frame
  have laterFrame := memoryWriteFrame_trans (inner_frame_mono callFrame (by decide : 0 ≤ 32)) resultFrame
  have fullFrame := memoryWriteFrame_trans stageFrame (inner_frame_mono laterFrame (by decide : 32 ≤ 40))
  have runningT := runningV.of_callee result.toCalleeResult
    (by intro region member a contains
        exact ⟨Stack.region initial hkdfSha256Extract.minStackBytes, by simp,
          stack_layout_within ctx.call.stack innerCallLayout rspV outputV region member a contains⟩)
  have rspT : t.regValue .rsp = frameBase initial := by rw [result.rsp, retV]
  have stateT := inner_preserved_of_frame ctx state runningT fullFrame rspT
  have blockT := inner_hasBytes_of_frame ctx fullFrame (offset := 400) (len := 64)
    (by decide) (by decide) (by decide) (by decide) (by simpa only [blockAddress] using block)
  have hashT : HashStateAt t (frameBase initial + 56)
      (compressBlocks Hkdf.Proofs.NIST.SHA256.initialHash
        (HMAC.xorPad (HMAC.keyBlock (saltKey salt)) 0x36)) := by
    change HashStateAt t (frameBase initial + BitVec.ofNat 64 56) _
    have value := result.hashWords
    rw [outputV] at value
    have addr := Standard.stack_address state.rsp (offset := 56) (by decide)
    rw [show rspOf s = frameBase initial from state.rsp] at addr
    rw [addr]
    exact value
  have countWordU : memLoad u.external (stackPtr initial - BitVec.ofNat 64 432) 64 = 1 := by
    have word := stores.2.2.2.2.2.2.2.2.1
    change memLoad u.external (rspOf s + BitVec.ofNat 64 88) 64 = 1 at word
    have addr := Standard.stack_address state.rsp (offset := 88) (by decide)
    rw [addr] at word
    exact word
  have countWordT := (CallFrame.agrees_memLoad
    (inner_frame_agrees ctx laterFrame (offset := 432) (len := 8)
      (by decide) (by decide) (by decide) (by decide))).trans countWordU
  have countT : loadBytes t.external (frameBase initial + 88) 8 = .ok 1 := by
    change loadBytes t.external (frameBase initial + BitVec.ofNat 64 88) 8 = .ok 1
    have bytes := Bytes.of_memLoad (n := 64)
      (Standard.stack_readable ctx stateT.toState (offset := 432) (len := 8) (by decide) (by decide)).mem
    rw [countWordT] at bytes
    have addr := Standard.stack_address state.rsp (offset := 88) (by decide)
    rw [show rspOf s = frameBase initial from state.rsp] at addr
    rw [addr]
    exact bytes.loadBytes64
  have ivs : t.regValue .rbx = 0x5be0cd191f83d9ab ∧
      t.regValue .r14 = 0x9b05688c510e527f ∧ t.regValue .r12 = 0xa54ff53a3c6ef372 ∧
      t.regValue .r13 = 0xbb67ae856a09e667 := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · have same : t.regValue .rbx = u.regValue .rbx :=
        (result.abi.1 .rbx (by simp)).trans
          (callEffect.agrees.read (n := 64) (r := 3)
            (by simp [X86Proofs.callEffect, pushEffect_components]))
      rw [same]
      have iv := (iv_loaded state.loaded 3 (by decide)).2
      simp only [ivWords, List.getElem!_cons_zero, List.getElem!_cons_succ,
        Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at iv
      exact stores.1.trans iv
    · have same : t.regValue .r14 = u.regValue .r14 :=
        (result.abi.1 .r14 (by simp)).trans
          (callEffect.agrees.read (n := 64) (r := 14)
            (by simp [X86Proofs.callEffect, pushEffect_components]))
      rw [same]
      have iv := (iv_loaded state.loaded 2 (by decide)).2
      simp only [ivWords, List.getElem!_cons_zero, List.getElem!_cons_succ,
        Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at iv
      exact stores.2.1.trans iv
    · have same : t.regValue .r12 = u.regValue .r12 :=
        (result.abi.1 .r12 (by simp)).trans
          (callEffect.agrees.read (n := 64) (r := 12)
            (by simp [X86Proofs.callEffect, pushEffect_components]))
      rw [same]
      have iv := (iv_loaded state.loaded 1 (by decide)).2
      simp only [ivWords, List.getElem!_cons_zero, List.getElem!_cons_succ,
        Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at iv
      exact stores.2.2.1.trans iv
    · have same : t.regValue .r13 = u.regValue .r13 :=
        (result.abi.1 .r13 (by simp)).trans
          (callEffect.agrees.read (n := 64) (r := 13)
            (by simp [X86Proofs.callEffect, pushEffect_components]))
      rw [same]
      have iv := (iv_loaded state.loaded 0 (by decide)).2
      simp only [ivWords, List.getElem!_cons_zero,
        Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at iv
      exact stores.2.2.2.1.trans iv
  obtain ⟨fuel, execution⟩ := result.execution
  refine ⟨stageFuel+1+fuel, t, (stageRun.trans callRun).trans execution,
    supportedMachine_readyToStep result.machine, ?_⟩
  refine ⟨⟨stateT, hashT, countT, ivs⟩, ?_, ?_⟩
  · rw [result.rip, retV]
  · simpa only [blockAddress] using blockT

end Hkdf.Proofs.Standard.Initialization
