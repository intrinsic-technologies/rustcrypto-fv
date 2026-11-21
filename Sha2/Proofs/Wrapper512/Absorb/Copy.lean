import Sha2.Proofs.Common.SHA256.Absorb.DirectProof.CopyCall
import Sha2.Proofs.Wrapper512.Call
import Sha2.Proofs.Wrapper512.Absorb.Memory

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Absorb.Copy

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine
open Sha2.Proofs.Wrapper

inductive Site where
  | short
  | fill
  | tail

def Site.relativeOffset (site : Site) (form : Form := .slices) (v : Variant := .sha384) : Nat :=
  match form, site with
  | .slices, .short => 0x101
  | .slices, .fill => 0x163
  | .slices, .tail => 0x1f6
  | .digest, .short | .digest, .fill => 0xdb
  | .digest, .tail => 0x13d
  | .reset stage, _ =>
    if stage.val = 0 then match site with
      | .short => 0x10a | .fill => 0x166 | .tail => 0x1e8
    else if stage.val = 1 then match site with
      | .short => 0x2b7 | .fill => 0x310 | .tail => 0x393
    else (match v with | .sha384 => 0x20 | .sha512 => 0x40 | _ => 0) +
      (match site with | .short => 0x607 | .fill => 0x65c | .tail => 0x6db)
  | .finalizeIntoReset false, _ =>
    match site with | .short => 0xfe | .fill => 0x15d | .tail => 0x1e9
  | .finalizeIntoReset true, _ =>
    match v with
    | .sha384 | .sha512 => (if v = .sha512 then 0x20 else 0) +
      (match site with | .short => 0x46b | .fill => 0x4c3 | .tail => 0x54c)
    | _ => match site with | .short => 0x44b | .fill => 0x4a3 | .tail => 0x52d
  | .traitFinalizeIntoReset false, _ =>
    match site with | .short => 0x11e | .fill => 0x1a5 | .tail => 0x23b
  | .traitFinalizeIntoReset true, _ =>
    (match v with | .sha384 => 0x20 | .sha512 => 0x40 | _ => 0) +
      (match site with | .short => 0x4de | .fill => 0x562 | .tail => 0x5f8)

def Site.register (site : Site) (v : Variant) (form : Form) : Option (BitVec 5) :=
  match form, site with
  | .reset stage, _ => if stage.val = 2 then some 3 else none
  | .finalizeIntoReset true, _ =>
    some (match v with | .sha384 | .sha512 => 3 | _ => 12)
  | .traitFinalizeIntoReset _, .fill => none
  | .traitFinalizeIntoReset false, _ => some 13
  | .traitFinalizeIntoReset true, _ => some 5
  | _, _ => none

def Site.size (site : Site) (v : Variant) (form : Form := .slices) : Nat :=
  match site.register v form with
  | none => 6
  | some r => if r.toNat < 8 then 2 else 3

def Site.offset (site : Site) (v : Variant) (form : Form := .slices) : Nat :=
  v.textOffset form + site.relativeOffset form v

def Site.displacement (site : Site) (v : Variant) (form : Form := .slices) : BitVec 32 :=
  BitVec.ofNat 32 (0x200280 - (0x100000 + site.offset v form + 6))

def Site.code (site : Site) (v : Variant) (form : Form := .slices) : List UInt8 :=
  match site.register v form with
  | none => encodeCallM64 (.rip (site.displacement v form))
  | some r => if r.toNat < 8 then [0xff, UInt8.ofNat (0xd0 + r.toNat)]
      else [0x41, 0xff, UInt8.ofNat (0xd0 + r.toNat - 8)]

theorem Site.bound (site : Site) (v : Variant) (form : Form := .slices) :
    site.offset v form + site.size v form < 71757 := by
  cases v <;> cases site <;> cases form with
  | reset stage => revert stage; decide +kernel
  | finalizeIntoReset second | traitFinalizeIntoReset second => revert second; decide +kernel
  | _ => decide +kernel

theorem Site.bytes (site : Site) (v : Variant) (form : Form := .slices) :
    Extracted.textBytes.toListFrom (site.offset v form) (site.size v form) =
      site.code v form := by
  cases v <;> cases site <;> cases form with
  | reset stage => revert stage; decide +kernel
  | finalizeIntoReset second | traitFinalizeIntoReset second => revert second; decide +kernel
  | _ => decide +kernel

theorem Site.pointer (site : Site) (v : Variant) (form : Form := .slices) :
    Extracted.textAddress + BitVec.ofNat 64 (site.offset v form) + 6 +
      (site.displacement v form).signExtend 64 = 0x200280 := by
  cases v <;> cases site <;> cases form with
  | reset stage => revert stage; decide +kernel
  | finalizeIntoReset second | traitFinalizeIntoReset second => revert second; decide +kernel
  | _ => decide +kernel

def Site.callSite (site : Site) (v : Variant) (form : Form) : Common.SHA256.Absorb.CallSite :=
  ⟨Extracted.textAddress + BitVec.ofNat 64 (site.offset v form),
    match site.register v form with
    | none => .memory (.rip (site.displacement v form))
    | some r => .register (r.setWidth 4)⟩

theorem Site.callSite_code (site : Site) (v : Variant) (form : Form) :
    (site.callSite v form).encoding.bytes = site.code v form := by
  cases v <;> cases site <;> cases form with
  | reset stage => revert stage; decide +kernel
  | finalizeIntoReset second | traitFinalizeIntoReset second => revert second; decide +kernel
  | _ => decide +kernel

theorem Site.code_size (site : Site) (v : Variant) (form : Form) :
    (site.code v form).length = site.size v form := by
  cases v <;> cases site <;> cases form with
  | reset stage => revert stage; decide +kernel
  | finalizeIntoReset second | traitFinalizeIntoReset second => revert second; decide +kernel
  | _ => decide +kernel

theorem Site.register_width (site : Site) (v : Variant) (form : Form) :
    ∀ r, site.register v form = some r → (r.setWidth 4).setWidth 5 = r := by
  cases v <;> cases site <;> cases form <;>
    simp [Site.register] <;> split <;> simp_all

theorem input_region_mem {initial : RamState} {inputs : Array Input}
    (form : Form) (i : Fin inputs.size) : inputs[i].region ∈ form.readRegions initial inputs := by
  have member : inputs[i].region ∈ (inputs.map Input.region).toList := by
    apply List.mem_iff_getElem.mpr
    refine ⟨i.val, by simp, ?_⟩
    simp
  cases form with
  | slices | reset _ | finalizeIntoReset _ | traitFinalizeIntoReset _ =>
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member)
  | digest => exact member

theorem input_byte_unchanged [Bindings] {v : Variant} {initial s : RamState}
    {inputs : Array Input} {form : Form} (ctx : Context v initial inputs form)
    (frame : MemoryWriteFrame initial s (v.writeRegions initial form))
    (i : Fin inputs.size) (j : Fin inputs[i].bytes.size) :
    s.external[inputs[i].address + BitVec.ofNat 64 j.val]? = some inputs[i].bytes[j.val] := by
  have bounded : inputs[i].address.toNat + inputs[i].bytes.size < 2^32 := (ctx.inputInMemory i).2.1
  have contains : inputs[i].region.Contains (inputs[i].address + BitVec.ofNat 64 j.val).toNat := by
    change inputs[i].address.toNat ≤ _ ∧ _ < inputs[i].address.toNat + inputs[i].bytes.size
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
    constructor <;> omega
  rw [frame _ (fun region hr =>
    (ctx.separation.2 region (by simpa using hr)).1 _ (input_region_mem form i) _ contains)]
  simpa only [Input.region, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
    (ctx.inputInMemory i).2.2.2 j

theorem input_readable [Bindings] {v : Variant} {initial s : RamState}
    {inputs : Array Input} {form : Form} (ctx : Context v initial inputs form)
    (frame : MemoryWriteFrame initial s (v.writeRegions initial form)) (i : Fin inputs.size) :
    MemReadable s inputs[i].address inputs[i].bytes.size := by
  refine ⟨Nat.le_of_lt (ctx.inputInMemory i).2.1, ?_⟩
  intro j hj
  rw [input_byte_unchanged ctx frame i ⟨j, hj⟩]
  rfl

theorem destination_eq {form : Form} {initial : RamState} {position : Nat} (bound : position ≤ 128) :
    stackPtr initial - BitVec.ofNat 64 form.activeMemory.buffer + BitVec.ofNat 64 position =
      stackPtr initial - BitVec.ofNat 64 (form.activeMemory.buffer-position) := by
  have bufferLow : 128 ≤ form.activeMemory.buffer := by cases form <;> dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, Variant.routine, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory] <;> decide
  have bufferHigh : form.activeMemory.buffer < 2^64 := by cases form <;> dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, Variant.routine, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory] <;> decide
  rw [← BitVec.ofNat_sub_ofNat_of_le form.activeMemory.buffer position (by omega) (by omega),
    BitVec.sub_eq_add_neg (stackPtr initial) (BitVec.ofNat 64 form.activeMemory.buffer - BitVec.ofNat 64 position), BitVec.neg_sub]
  simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]

theorem source_region [Bindings] {v : Variant} {form : Form} {initial s : RamState} {inputs : Array Input}
    (ctx : Context v initial inputs form) (state : ReturnState v initial s form)
    (i : Fin inputs.size) {offset count : Nat} (bound : offset + count ≤ inputs[i].bytes.size) :
    let source := inputs[i].address + BitVec.ofNat 64 offset
    (⟨source.toNat, count⟩ : MemoryRegion).Bounded ∧
    (⟨source.toNat, count⟩ : MemoryRegion).Allocated s.external ∧
    (⟨source.toNat, count⟩ : MemoryRegion).Disjoint
      (Stack.region initial (v.routine form).minStackBytes) := by
  dsimp only
  have bounded := show inputs[i].address.toNat + inputs[i].bytes.size < 2^32 from (ctx.inputInMemory i).2.1
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
      (input_readable ctx state.frame i)) subset (fun _ h => h)
  · apply fun a ha => (ctx.separation.2 (Stack.region initial (v.routine form).minStackBytes)
      (by cases form <;> simp [Variant.writeRegions, Form.writeRegionCount, Form.twoOutputs])).1 inputs[i].region ?_ a (subset a ha)
    exact input_region_mem form i

structure Result [Bindings] (v : Variant) (initial s t : RamState) (input : Input)
    (site : Site) (offset position count : Nat) (form : Form := .slices) : Prop where
  preserved : Preserved v initial t form
  rip : t.RIP = (Extracted.textAddress + BitVec.ofNat 64 (site.offset v form) + BitVec.ofNat 64 (site.size v form) : BitVec 64)
  abi : PreservesABI s t
  frame : MemoryWriteFrame s t #v[
    (⟨(stackPtr initial - BitVec.ofNat 64 (form.activeMemory.buffer-position)).toNat, count⟩ : MemoryRegion),
    (⟨(stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8)).toNat, 8⟩ : MemoryRegion)]
  bytes : (⟨(stackPtr initial - BitVec.ofNat 64 form.activeMemory.buffer + BitVec.ofNat 64 position).toNat, count⟩ : MemoryRegion).HasBytes
    t.external (input.bytes.extract offset (offset + count))
  execution : ∃ fuel, Advances (returnBoundary initial) fuel s t
  stackFrame : MemoryWriteFrame s t #v[Stack.region initial (v.routine form).minStackBytes]

theorem metadataBounds (form : Form) (off : Nat) (hd : form ≠ .digest)
    (member : off ∈ [form.outputSlot, form.secondOutputSlot, form.pointerSlot, form.lengthSlot]) :
    off ≤ form.frameBytes ∧ 8 ≤ off ∧
      (form.activeMemory.buffer + 8 ≤ off ∨ off + 128 ≤ form.activeMemory.buffer) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  all_goals cases form <;> first | contradiction | decide +revert

theorem copy_after_call [Bindings] {v : Variant} {form : Form} {initial s : RamState} {inputs : Array Input}
    (ctx : Context v initial inputs form) (input : Preserved v initial s form)
    (site : Site) (i : Fin inputs.size) {offset position count : Nat}
    (sourceBound : offset + count ≤ inputs[i].bytes.size)
    (destinationBound : position + count ≤ 128)
    (destination : s.regValue .rdi = stackPtr initial - BitVec.ofNat 64 form.activeMemory.buffer + BitVec.ofNat 64 position)
    (source : s.regValue .rsi = inputs[i].address + BitVec.ofNat 64 offset)
    (length : s.regValue .rdx = BitVec.ofNat 64 count)
    {u : RamState} (callRun : Advances (returnBoundary initial) 1 s u) (stateU : ReturnState v initial u form)
    (effect : (callEffect (fun _ => 0x10dd60)
      (Extracted.textAddress + BitVec.ofNat 64 (site.offset v form) + BitVec.ofNat 64 (site.size v form)) s).Holds s u)
    (rspU : stackPtr u = stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8))
    (returnU : (returnBoundary u).rip = Extracted.textAddress + BitVec.ofNat 64 (site.offset v form) + BitVec.ofNat 64 (site.size v form)) :
    ∃ t, Result v initial s t inputs[i] site offset position count form := by
  have bufferLow : 176 ≤ form.activeMemory.buffer := by cases form <;> dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, Variant.routine, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory] <;> decide
  have bufferHigh : form.activeMemory.buffer ≤ form.frameBytes := by cases form <;> dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, Variant.routine, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory] <;> decide
  have destination' := destination.trans (destination_eq (by omega))
  have push : pushAddr s = stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8) := by
    rw [pushAddr, input.rsp, BitVec.sub_sub, BitVec.ofNat_add]
    rfl
  have callFrame : AgreesExcept [.reg 4, .mem (stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8)) 8, .rip] s u := by
    simpa only [callEffect, pushEffect_components, push] using effect.agrees
  have destinationU : u.regValue .rdi = stackPtr initial - BitVec.ofNat 64 (form.activeMemory.buffer-position) :=
    (callFrame.read (n := 64) (r := 7) (by simp)).trans destination'
  have sourceU : u.regValue .rsi = inputs[i].address + BitVec.ofNat 64 offset :=
    (callFrame.read (n := 64) (r := 6) (by simp)).trans source
  have lengthU : u.regValue .rdx = BitVec.ofNat 64 count :=
    (callFrame.read (n := 64) (r := 2) (by simp)).trans length
  obtain ⟨bounded, allocated, apart⟩ := source_region ctx stateU i sourceBound
  have region : registerRegion u .rsi count =
      (⟨(inputs[i].address + BitVec.ofNat 64 offset).toNat, count⟩ : MemoryRegion) := by
    simp only [registerRegion, sourceU]
  have returnInProgram : InProgram (returnBoundary u).rip := by
    rw [returnU]
    change InProgram ((Extracted.textAddress + BitVec.ofNat 64 (site.offset v form)) + BitVec.ofNat 64 (site.size v form))
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact inProgram_of_textOffset ((site.offset v form) + site.size v form) (site.bound v form)
  have pre := callee_pre (inputBytes := count) (outputBytes := count)
    (outputOffset := form.activeMemory.buffer-position) (reserve := 0) ctx stateU effect.rip rspU destinationU
    (by omega) (by omega) (by decide) (region ▸ bounded) (region ▸ allocated) (region ▸ apart)
    returnInProgram
  obtain ⟨t, result, copied, copyFrame⟩ := Common.Memory.memcpy_correct pre lengthU (by omega)
    returnInProgram
  have stateT := stateU.of_callee (outputOffset := form.activeMemory.buffer-position) ctx result rspU destinationU
    (by omega) (by omega) (by decide)
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
      (⟨(stackPtr initial - BitVec.ofNat 64 (form.activeMemory.buffer-position)).toNat, count⟩ : MemoryRegion) := by
    simp only [registerRegion, destinationU]
  have stackRegion : Stack.region u 0 =
      (⟨(stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8)).toNat, 8⟩ : MemoryRegion) := by
    change (⟨(stackPtr u).toNat - 0,
      (stackPtr u).toNat + 8 - ((stackPtr u).toNat - 0)⟩ : MemoryRegion) = _
    simp only [Nat.sub_zero, Nat.add_sub_cancel_left, rspU]
  have budget : (v.routine form).minStackBytes = form.stackBytes := rfl
  have bounds := Dispatch.stack_bounds512 ctx
  have slotBound : (⟨(stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8)).toNat, 8⟩ : MemoryRegion).Bounded := by
    change (stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8)).toNat + 8 < 2^32
    rw [Dispatch.stack_sub_toNat512 ctx (offset := form.frameBytes + 8) (by cases v <;> cases form <;> dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, Variant.routine, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory] <;> decide)]
    omega
  have frame : MemoryWriteFrame s t #v[
      (⟨(stackPtr initial - BitVec.ofNat 64 (form.activeMemory.buffer-position)).toNat, count⟩ : MemoryRegion),
      (⟨(stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8)).toNat, 8⟩ : MemoryRegion)] := by
    apply memoryWriteFrame_trans (callFrame.memoryWriteFrame ?_) ?_
    · intro c hc a covers
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact covers.elim
      · obtain ⟨j, hj, rfl⟩ := covers
        exact ⟨⟨(stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8)).toNat, 8⟩, by simp,
          memoryRegion_contains_add slotBound (Nat.le_refl _) (Nat.le_refl _) hj⟩
      · exact covers.elim
    · simpa only [outputRegion, stackRegion] using result.frame
  have metadataReset (hd : form ≠ .digest) (off : Nat)
      (member : off ∈ [form.outputSlot, form.secondOutputSlot, form.pointerSlot, form.lengthSlot]) :
      ∀ a, (Component.mem (stackPtr initial - BitVec.ofNat 64 off) 8).Covers a →
        t.external[a]? = s.external[a]? := by
    intro a ha
    obtain ⟨j, hj, rfl⟩ := ha
    have bounds := metadataBounds form off hd member
    exact frame_bytes (reserve := form.frameBytes + 8) ctx
      (by simpa only [Nat.add_sub_cancel_left] using frame)
      (by omega) (by omega) (by omega)
      (by cases form <;> dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, Variant.routine, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory] <;> decide)
      bounds.1 bounds.2.1 (by rcases bounds.2.2 with h | h <;> omega) j hj
  have metadata : match form with
      | .slices => ∀ a, (Component.mem (stackPtr initial - 624) 24).Covers a →
          t.external[a]? = s.external[a]?
      | .digest => True
      | _ => ∀ off ∈ [form.outputSlot, form.secondOutputSlot, form.pointerSlot, form.lengthSlot],
          ∀ a, (Component.mem (stackPtr initial - BitVec.ofNat 64 off) 8).Covers a →
            t.external[a]? = s.external[a]? := by
    cases form with
    | digest => trivial
    | slices =>
      intro a ha
      obtain ⟨j, hj, rfl⟩ := ha
      exact frame_bytes (offset := 624) (len := 24) (reserve := 640) ctx frame
        (by change 392-position ≤ 632; omega) (by change count ≤ 392-position; omega)
        (by decide) (by decide) (by decide) (by decide)
        (by left; change 392-position+24 ≤ 624; omega) j hj
    | reset stage | finalizeIntoReset second | traitFinalizeIntoReset second =>
      exact metadataReset (by intro h; cases h)
  have size : (inputs[i].bytes.extract offset (offset + count)).size = count := by
    rw [ByteArray.size_extract]
    omega
  obtain ⟨fuel, calleeRun⟩ := result.execution
  have execution : ∃ fuel, Advances (returnBoundary initial) fuel s t :=
    ⟨1 + fuel, callRun.trans calleeRun⟩
  have stackFrame := call_callee_stack_frame ctx effect result input.rsp destinationU
    (by omega) (by omega) (by decide)
  refine ⟨t, ⟨preserved_of_bytes input stateT (by cases form <;> exact metadata) (fun _ => abi.1 .rbx (by simp))
    (fun _ => .inl (by cases v <;> exact abi.1 _ (by simp))), result.rip.trans returnU, abi, frame, ⟨size, ?_⟩, execution, stackFrame⟩⟩
  intro j
  have hj : j.val < count := by have := j.isLt; omega
  have byte := copied j.val hj
  rw [destinationU, sourceU] at byte
  rw [destination_eq (by omega), BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [byte]
  have sourceByte := input_byte_unchanged ctx stateU.frame i
    ⟨offset + j.val, by omega⟩
  simpa only [BitVec.add_assoc, ← BitVec.ofNat_add, ByteArray.getElem_extract] using sourceByte


theorem copy [Bindings] {v : Variant} {form : Form} {initial s : RamState} {inputs : Array Input}
    (ctx : Context v initial inputs form) (input : Preserved v initial s form)
    (site : Site) (i : Fin inputs.size) {offset position count : Nat}
    (sourceBound : offset + count ≤ inputs[i].bytes.size)
    (destinationBound : position + count ≤ 128)
    (rip : s.RIP = Extracted.textAddress + BitVec.ofNat 64 (site.offset v form))
    (destination : s.regValue .rdi = stackPtr initial - BitVec.ofNat 64 form.activeMemory.buffer + BitVec.ofNat 64 position)
    (source : s.regValue .rsi = inputs[i].address + BitVec.ofNat 64 offset)
    (length : s.regValue .rdx = BitVec.ofNat 64 count)
    (targetRegister : ∀ r, site.register v form = some r →
      (Operand.reg r : Operand 64).read s = 0x10dd60 := by simp [Sha2.Proofs.Wrapper512.Absorb.Copy.Site.register]) :
    ∃ t, Result v initial s t inputs[i] site offset position count form := by
  have address : pushAddr s = stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8) := by
    rw [pushAddr, input.rsp, BitVec.sub_sub, BitVec.ofNat_add]
    rfl
  have writable : MemWritable s (pushAddr s) 8 := by
    rw [address]
    have hw := Dispatch.stack_sub_writable8_512 ctx (offset := form.frameBytes + 8)
      (by cases form <;> dsimp only [Form.frameBytes, Variant.routine, Form.stackBytes] <;> decide)
      (by cases form <;> dsimp only [Form.frameBytes] <;> decide)
    exact ⟨hw.low, fun i hi => input.allocated _ (hw.mem i hi), hw.tables⟩
  have code : CodeIn (codeRange (site.callSite v form).pc (site.callSite v form).encoding.bytes) s := by
    rw [site.callSite_code]
    exact programText_slice (programLoaded_codeIn input.loaded) (site.offset v form)
      (site.code v form) (by rw [site.code_size]; exact Nat.le_of_lt (site.bound v form))
      (by rw [site.code_size]; exact site.bytes v form)
  have apart : RangeApart (pushAddr s) 8 (site.callSite v form).pc
      (site.callSite v form).encoding.bytes.length := by
    rw [address, site.callSite_code, site.code_size]
    exact Machine.Stages.stack_slot_codeApart ctx
      (by cases form <;> dsimp only [Form.frameBytes, Variant.routine, Form.stackBytes] <;> decide)
      (by cases form <;> dsimp only [Form.frameBytes] <;> decide)
      (Nat.le_of_lt (site.bound v form))
  have target : Common.SHA256.Absorb.CopyCall.Target (site.callSite v form) s := by
    unfold Site.callSite
    cases hr : site.register v form with
    | none =>
      have pointer := Wrapper.memcpy_pointer input.loaded
      refine ⟨trivial, rfl, rfl, ?_, ?_⟩
      · change MemReadable s (Extracted.textAddress + BitVec.ofNat 64 (site.offset v form) + 6 +
          (site.displacement v form).signExtend 64) 8
        rw [site.pointer v form]
        exact pointer.1
      · change (Operand.mem (Extracted.textAddress + BitVec.ofNat 64 (site.offset v form) + 6 +
          (site.displacement v form).signExtend 64) : Operand 64).read s = _
        rw [site.pointer v form]
        exact pointer.2
    | some r =>
      change (Operand.reg ((r.setWidth 4).setWidth 5) : Operand 64).read s = _
      rw [site.register_width v form r hr]
      exact targetRegister r hr
  obtain ⟨u, run, ready, effect⟩ := Common.SHA256.Absorb.CopyCall.enter
    (site.callSite v form) (returnBoundary initial)
    (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2
    (supportedMachine_readyToStep input.machine) code ⟨rip, writable, apart⟩ target
  rw [site.callSite_code, site.code_size] at effect
  obtain ⟨stateU, rspU, returnU⟩ := ReturnState.of_call ctx input.toState run ready effect input.rsp
  exact copy_after_call ctx input site i sourceBound destinationBound destination source length
    run stateU effect rspU returnU

theorem Result.bytes_unchanged [Bindings] {v : Variant} {form : Form} {initial s t : RamState} {inputs : Array Input}
    {input : Input} {site : Site} {sourceOffset position count offset len : Nat}
    (result : Result v initial s t input site sourceOffset position count form)
    (ctx : Context v initial inputs form) (destinationBound : position + count ≤ 128)
    (low : offset ≤ form.frameBytes) (high : len ≤ offset)
    (apart : (form.activeMemory.buffer-position) + len ≤ offset ∨ offset + count ≤ form.activeMemory.buffer-position) :
    ∀ i < len, t.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      s.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  have bufferLow : 176 ≤ form.activeMemory.buffer := by cases form <;> dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, Variant.routine, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory] <;> decide
  have bufferHigh : form.activeMemory.buffer ≤ form.frameBytes := by cases form <;> dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, Variant.routine, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory] <;> decide
  exact frame_bytes (reserve := form.frameBytes + 8) ctx
    (by simpa only [Nat.add_sub_cancel_left] using result.frame)
    (by omega) (by omega) (by omega) (by cases form <;> dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, Variant.routine, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory] <;> decide) low high apart

end Sha2.Proofs.Wrapper512.Absorb.Copy
