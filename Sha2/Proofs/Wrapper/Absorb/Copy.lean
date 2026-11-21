import Sha2.Proofs.Wrapper.Call

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper.Absorb.Copy

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

inductive Site where
  | short
  | fill
  | tail

def Site.offset (site : Site) (v : Variant := .sha256) : Nat :=
  v.textOffset + match site with
  | .short => 0xb1
  | .fill => 0x119
  | .tail => 0x199

def Site.displacement (site : Site) (v : Variant := .sha256) : BitVec 32 :=
  BitVec.ofNat 32 (0x100280 - (site.offset v + 6))

theorem Site.bound (site : Site) (v : Variant := .sha256) : site.offset v + 6 < 71757 := by
  cases site <;> cases v <;> decide

theorem Site.bytes (site : Site) (v : Variant := .sha256) :
    Extracted.textBytes.toListFrom (site.offset v) 6 = encodeCallM64 (.rip (site.displacement v)) := by
  cases site <;> cases v <;> decide +kernel

theorem Site.pointer (site : Site) (v : Variant := .sha256) :
    Extracted.textAddress + BitVec.ofNat 64 (site.offset v) + 6 + (site.displacement v).signExtend 64 =
      0x200280 := by
  cases site <;> cases v <;> decide

theorem destination_eq {initial : RamState} {position : Nat} (bound : position ≤ 64) :
    stackPtr initial - 152 + BitVec.ofNat 64 position =
      stackPtr initial - BitVec.ofNat 64 (152-position) := by
  rw [← BitVec.ofNat_sub_ofNat_of_le 152 position (by omega) (by omega),
    BitVec.sub_eq_add_neg (stackPtr initial) (152#64 - BitVec.ofNat 64 position), BitVec.neg_sub]
  simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.ofNat_eq_ofNat]

theorem source_region [Bindings] {v : Variant} {initial s : RamState} {inputs : Array Input}
    (ctx : Context (v := v) initial inputs) (state : State (v := v) initial s)
    (i : Fin inputs.size) {offset count : Nat} (bound : offset + count ≤ inputs[i].bytes.size) :
    let source := inputs[i].address + BitVec.ofNat 64 offset
    (⟨source.toNat, count⟩ : MemoryRegion).Bounded ∧
    (⟨source.toNat, count⟩ : MemoryRegion).Allocated s.external ∧
    (⟨source.toNat, count⟩ : MemoryRegion).Disjoint
      (Stack.region initial v.routine.minStackBytes) := by
  dsimp only
  have bounded := validCall_input_bounded ctx.call i
  have address : (inputs[i].address + BitVec.ofNat 64 offset).toNat =
      inputs[i].address.toNat + offset := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have subset : ∀ a, (⟨(inputs[i].address + BitVec.ofNat 64 offset).toNat, count⟩ :
      MemoryRegion).Contains a → inputs[i].region.Contains a := by
    intro a ha
    change (inputs[i].address + BitVec.ofNat 64 offset).toNat ≤ a ∧
      a < (inputs[i].address + BitVec.ofNat 64 offset).toNat + count at ha
    rw [address] at ha
    change inputs[i].address.toNat ≤ a ∧ a < inputs[i].address.toNat + inputs[i].bytes.size
    omega
  refine ⟨?_, ?_, ?_⟩
  · change (inputs[i].address + BitVec.ofNat 64 offset).toNat + count < 2^32
    rw [address]
    omega
  · exact allocated_of_grow (allocated_of_memReadable
      (validCall_input_readable ctx.call state.frame i)) subset (fun _ h => h)
  · apply fun a ha => (ctx.call.separation.2 (Stack.region initial v.routine.minStackBytes)
      (by simp)).1 inputs[i].region ?_ a (subset a ha)
    simp only [readRegions, List.mem_cons]
    right
    right
    apply List.mem_iff_getElem.mpr
    refine ⟨i.val, by simp, ?_⟩
    simp

structure Result [Bindings] (initial s t : RamState) (input : Input)
    (site : Site) (offset position count : Nat) (v : Variant := .sha256) : Prop where
  preserved : Preserved (v := v) initial t
  rip : t.RIP = (Extracted.textAddress + BitVec.ofNat 64 (site.offset v) + 6 : BitVec 64)
  abi : PreservesABI s t
  frame : MemoryWriteFrame s t #v[
    (⟨(stackPtr initial - BitVec.ofNat 64 (152-position)).toNat, count⟩ : MemoryRegion),
    (⟨(stackPtr initial - 352).toNat, 8⟩ : MemoryRegion)]
  bytes : (⟨(stackPtr initial - 152 + BitVec.ofNat 64 position).toNat, count⟩ : MemoryRegion).HasBytes
    t.external (input.bytes.extract offset (offset + count))

theorem copy [Bindings] {v : Variant} {initial s : RamState} {inputs : Array Input}
    (ctx : Context (v := v) initial inputs) (input : Preserved (v := v) initial s)
    (site : Site) (i : Fin inputs.size) {offset position count : Nat}
    (sourceBound : offset + count ≤ inputs[i].bytes.size)
    (destinationBound : position + count ≤ 64)
    (rip : s.RIP = (Extracted.textAddress + BitVec.ofNat 64 (site.offset v) : BitVec 64))
    (destination : s.regValue .rdi = stackPtr initial - 152 + BitVec.ofNat 64 position)
    (source : s.regValue .rsi = inputs[i].address + BitVec.ofNat 64 offset)
    (length : s.regValue .rdx = BitVec.ofNat 64 count) :
    ∃ t, Result (v := v) initial s t inputs[i] site offset position count := by
  have destination' := destination.trans (destination_eq (by omega))
  have pointer := memcpy_pointer input.loaded
  obtain ⟨u, stateU, effect, rspU, returnU⟩ := call_m64 ctx input.toState
    (site.offset v) (site.displacement v) 0x10dd60 (Nat.le_of_lt (site.bound v)) (site.bytes v)
    (by cases v <;> decide) (inProgram_of_textOffset 0xdd60 (by cases v <;> decide))
    (by change MemReadable s (Extracted.textAddress + BitVec.ofNat 64 (site.offset v) + 6 +
          (site.displacement v).signExtend 64) 8
        rw [(site.pointer v)]
        exact pointer.1)
    (by change (Operand.mem (Extracted.textAddress + BitVec.ofNat 64 (site.offset v) + 6 +
          (site.displacement v).signExtend 64) : Operand 64).read s = 0x10dd60
        rw [(site.pointer v)]
        exact pointer.2) rip input.rsp
  have push : pushAddr s = stackPtr initial - 352 := by
    rw [pushAddr, input.rsp, BitVec.sub_sub]
    rfl
  have callFrame : AgreesExcept [.reg 4, .mem (stackPtr initial - 352) 8, .rip] s u := by
    simpa only [callEffect, pushEffect_components, push] using effect.agrees
  have destinationU : u.regValue .rdi = stackPtr initial - BitVec.ofNat 64 (152-position) :=
    (callFrame.read (n := 64) (r := 7) (by simp)).trans destination'
  have sourceU : u.regValue .rsi = inputs[i].address + BitVec.ofNat 64 offset :=
    (callFrame.read (n := 64) (r := 6) (by simp)).trans source
  have lengthU : u.regValue .rdx = BitVec.ofNat 64 count :=
    (callFrame.read (n := 64) (r := 2) (by simp)).trans length
  obtain ⟨bounded, allocated, apart⟩ := source_region ctx stateU i sourceBound
  have region : registerRegion u .rsi count =
      (⟨(inputs[i].address + BitVec.ofNat 64 offset).toNat, count⟩ : MemoryRegion) := by
    simp only [registerRegion, sourceU]
  have returnInside : InProgram (returnBoundary u).rip := by
    rw [returnU]
    change InProgram ((Extracted.textAddress + BitVec.ofNat 64 (site.offset v)) + BitVec.ofNat 64 6)
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact inProgram_of_textOffset ((site.offset v) + 6) (site.bound v)
  have pre := callee_pre (inputBytes := count) (outputBytes := count)
    (outputOffset := 152-position) (reserve := 0) ctx stateU effect.rip rspU destinationU
    (by omega) (by omega) (by cases v <;> decide) (region ▸ bounded) (region ▸ allocated) (region ▸ apart)
    returnInside
  obtain ⟨t, result, copied, copyFrame⟩ := Common.Memory.memcpy_correct pre lengthU (by omega) returnInside
  have stateT := stateU.of_callee (outputOffset := 152-position) ctx result rspU destinationU
    (by omega) (by omega) (by cases v <;> decide)
  have rspT : stackPtr t = stackPtr initial - 344 := by
    change t.regValue .rsp = _
    rw [result.rsp]
    change stackPtr u + 8 = _
    rw [rspU]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd]
  have abi : PreservesABI s t := by
    apply preservesABI_of_agrees (callFrame.trans copyFrame) input.directionFlag
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (callFrame.trans copyFrame).read (n := 64) (r := 3)
        (by simp [Common.Memory.Copy.copyComponents, Common.Memory.Copy.registerComponents])
    · exact (callFrame.trans copyFrame).read (n := 64) (r := 5)
        (by simp [Common.Memory.Copy.copyComponents, Common.Memory.Copy.registerComponents])
    · exact (callFrame.trans copyFrame).read (n := 64) (r := 12)
        (by simp [Common.Memory.Copy.copyComponents, Common.Memory.Copy.registerComponents])
    · exact (callFrame.trans copyFrame).read (n := 64) (r := 13)
        (by simp [Common.Memory.Copy.copyComponents, Common.Memory.Copy.registerComponents])
    · exact (callFrame.trans copyFrame).read (n := 64) (r := 14)
        (by simp [Common.Memory.Copy.copyComponents, Common.Memory.Copy.registerComponents])
    · exact (callFrame.trans copyFrame).read (n := 64) (r := 15)
        (by simp [Common.Memory.Copy.copyComponents, Common.Memory.Copy.registerComponents])
    all_goals simp [Common.Memory.Copy.copyComponents, Common.Memory.Copy.registerComponents]
  have outputRegion : registerRegion u .rdi count =
      (⟨(stackPtr initial - BitVec.ofNat 64 (152-position)).toNat, count⟩ : MemoryRegion) := by
    simp only [registerRegion, destinationU]
  have stackRegion : Stack.region u 0 =
      (⟨(stackPtr initial - 352).toNat, 8⟩ : MemoryRegion) := by
    change (⟨(stackPtr u).toNat - 0,
      (stackPtr u).toNat + 8 - ((stackPtr u).toNat - 0)⟩ : MemoryRegion) = _
    simp only [Nat.sub_zero, Nat.add_sub_cancel_left, rspU]
  have bounds := validCall_stack_bounds ctx.call
  have slotBound : (⟨(stackPtr initial - 352).toNat, 8⟩ : MemoryRegion).Bounded := by
    change (stackPtr initial - BitVec.ofNat 64 352).toNat + 8 < 2^32
    rw [validCall_stack_sub_toNat ctx.call (offset := 352) (by cases v <;> decide)]
    omega
  have frame : MemoryWriteFrame s t #v[
      (⟨(stackPtr initial - BitVec.ofNat 64 (152-position)).toNat, count⟩ : MemoryRegion),
      (⟨(stackPtr initial - 352).toNat, 8⟩ : MemoryRegion)] := by
    apply memoryWriteFrame_trans (callFrame.memoryWriteFrame ?_) ?_
    · intro c hc a covers
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact covers.elim
      · obtain ⟨j, hj, rfl⟩ := covers
        exact ⟨⟨(stackPtr initial - 352).toNat, 8⟩, by simp,
          memoryRegion_contains_add slotBound (Nat.le_refl _) (Nat.le_refl _) hj⟩
      · exact covers.elim
    · simpa only [outputRegion, stackRegion] using result.frame
  have metadata : ∀ a, (Component.mem (stackPtr initial - 176) 24).Covers a →
      t.external[a]? = s.external[a]? := by
    intro a ha
    obtain ⟨j, hj, rfl⟩ := ha
    exact frame_bytes (offset := 176) (len := 24) (reserve := 352) ctx frame (by omega) (by omega) (by cases v <;> decide) (by cases v <;> decide)
      (by cases v <;> decide) (by cases v <;> decide) (by left; omega) j hj
  have size : (inputs[i].bytes.extract offset (offset + count)).size = count := by
    rw [ByteArray.size_extract]
    omega
  refine ⟨t, ⟨preserved_of_bytes input stateT rspT metadata, result.rip.trans returnU, abi, frame, size, ?_⟩⟩
  intro j
  have hj : j.val < count := by have := j.isLt; omega
  have byte := copied j.val hj
  rw [destinationU, sourceU] at byte
  rw [destination_eq (by omega), BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [byte]
  have sourceByte := validCall_input_byte_unchanged ctx.call stateU.frame i
    ⟨offset + j.val, by omega⟩
  simpa only [BitVec.add_assoc, ← BitVec.ofNat_add, ByteArray.getElem_extract] using sourceByte


theorem Result.bytes_unchanged [Bindings] {v : Variant} {initial s t : RamState} {inputs : Array Input}
    {input : Input} {site : Site} {sourceOffset position count offset len : Nat}
    (result : Result (v := v) initial s t input site sourceOffset position count)
    (ctx : Context (v := v) initial inputs) (destinationBound : position + count ≤ 64)
    (low : offset ≤ 344) (high : len ≤ offset)
    (apart : (152-position) + len ≤ offset ∨ offset + count ≤ 152-position) :
    ∀ i < len, t.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      s.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  exact frame_bytes (reserve := 352) ctx result.frame
    (by omega) (by omega) (by cases v <;> decide) (by cases v <;> decide) low high apart

end Sha2.Proofs.Wrapper.Absorb.Copy
