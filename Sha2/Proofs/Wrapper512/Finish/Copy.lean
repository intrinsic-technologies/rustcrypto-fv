import Sha2.Proofs.Common.Memory.LoadBytes
import Sha2.Proofs.Wrapper512.Call
import Sha2.Proofs.Wrapper512.Absorb.Memory
import Sha2.Proofs.Common.Memory.Copy
import Sha2.Proofs.Wrapper512.Finish.Setup

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Finish.Copy

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

inductive Site where
  | initial
  | first
  | last

def Site.relativeOffset (site : Site) (form : Form := .slices) : Nat :=
  match site, form with
  | .initial, .slices => 0x22a
  | .first, .slices => 0x290
  | .last, .slices => 0x368
  | .initial, _ => 0x153
  | .first, _ => 0x1b0
  | .last, _ => 0x279

def Site.inputOffset : Site → Nat
  | .initial => 392
  | .first | .last => 600

def Site.outputOffset : Site → Nat
  | .initial => 600
  | .first | .last => 176

def Site.count : Site → Nat
  | .initial => 208
  | .first | .last => 128

def Site.offset (site : Site) (v : Variant) (form : Form := .slices) : Nat :=
  v.textOffset form + site.relativeOffset form

def Site.displacement (site : Site) (v : Variant) (form : Form := .slices) : BitVec 32 :=
  BitVec.ofNat 32 (0x200280 - (0x100000 + site.offset v form + 6))

theorem Site.bound (site : Site) (v : Variant) (form : Form := .slices)
    (eligible : form = .slices ∨ form = .digest := by first | exact Or.inl rfl | exact Or.inr rfl) : site.offset v form + 6 < 71757 := by
  rcases eligible with rfl | rfl <;> cases v <;> cases site <;> decide +kernel

theorem Site.bytes (site : Site) (v : Variant) (form : Form := .slices)
    (eligible : form = .slices ∨ form = .digest := by first | exact Or.inl rfl | exact Or.inr rfl) :
    Extracted.textBytes.toListFrom (site.offset v form) 6 = encodeCallM64 (.rip (site.displacement v form)) := by
  rcases eligible with rfl | rfl <;> cases v <;> cases site <;> decide +kernel

theorem Site.pointer (site : Site) (v : Variant) (form : Form := .slices)
    (eligible : form = .slices ∨ form = .digest := by first | exact Or.inl rfl | exact Or.inr rfl) :
    Extracted.textAddress + BitVec.ofNat 64 (site.offset v form) + 6 + (site.displacement v form).signExtend 64 =
      0x200280 := by
  rcases eligible with rfl | rfl <;> cases v <;> cases site <;> decide +kernel

def Site.layout (site : Site) (form : Form := .slices)
    (eligible : form = .slices ∨ form = .digest := by first | exact Or.inl rfl | exact Or.inr rfl) :
    Wrapper.StackCallLayout form.stackBytes site.count site.count 0 :=
  ⟨form.frameBytes + 8, site.inputOffset, site.outputOffset, by rcases eligible with rfl | rfl <;> decide, by rcases eligible with rfl | rfl <;> decide,
    by rcases eligible with rfl | rfl <;> cases site <;> decide, by rcases eligible with rfl | rfl <;> cases site <;> decide,
    by rcases eligible with rfl | rfl <;> cases site <;> decide, by rcases eligible with rfl | rfl <;> cases site <;> decide, by rcases eligible with rfl | rfl <;> cases site <;> decide⟩

structure Result [Bindings] (v : Variant) (initial s t : RamState) (site : Site) (form : Form := .slices) : Prop where
  execution : ∃ fuel, Advances (returnBoundary initial) fuel s t
  stackFrame : MemoryWriteFrame s t #v[Stack.region initial form.stackBytes]
  preserved : Preserved v initial t form
  rip : t.RIP = v.pc (site.relativeOffset form + 6) form
  abi : PreservesABI s t
  frame : MemoryWriteFrame s t #v[
    (⟨(stackPtr initial - BitVec.ofNat 64 site.outputOffset).toNat, site.count⟩ : MemoryRegion),
    (⟨(stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8)).toNat, 8⟩ : MemoryRegion)]
  bytes : ∀ i < site.count,
    t.external[stackPtr initial - BitVec.ofNat 64 site.outputOffset + BitVec.ofNat 64 i]? =
      s.external[stackPtr initial - BitVec.ofNat 64 site.inputOffset + BitVec.ofNat 64 i]?

structure StackResult [Bindings] (v : Variant) (initial s t : RamState)
    (count inputOffset outputOffset : Nat) (returnPC : BitVec 64) (form : Form) : Prop where
  execution : ∃ fuel, Advances (returnBoundary initial) fuel s t
  stackFrame : MemoryWriteFrame s t #v[Stack.region initial form.stackBytes]
  state : State v initial t form
  rip : t.RIP = returnPC
  abi : PreservesABI s t
  rbx : t.regValue .rbx = s.regValue .rbx
  frame : MemoryWriteFrame s t #v[
    (⟨(stackPtr initial - BitVec.ofNat 64 outputOffset).toNat, count⟩ : MemoryRegion),
    (⟨(stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8)).toNat, 8⟩ : MemoryRegion)]
  bytes : ∀ i < count,
    t.external[stackPtr initial - BitVec.ofNat 64 outputOffset + BitVec.ofNat 64 i]? =
      s.external[stackPtr initial - BitVec.ofNat 64 inputOffset + BitVec.ofNat 64 i]?

set_option maxHeartbeats 800000 in
theorem copy_at [Bindings] {v : Variant} {initial s u : RamState}
    {inputs : Array Input} {form : Form} {count : Nat} {returnPC : BitVec 64}
    (ctx : Context v initial inputs form) (input : State v initial s form)
    (stateU : ReturnState v initial u form)
    (layout : Wrapper.StackCallLayout form.stackBytes count count 0)
    (stackOffset : layout.stackOffset = form.frameBytes + 8)
    (outputHigh : count + 48 ≤ layout.outputOffset)
    (outputLow : layout.outputOffset ≤ form.frameBytes)
    (countBound : count < 2^32)
    (sourceApart : OffsetsApart (-BitVec.ofNat 64 (form.frameBytes + 8)) 8
      (-BitVec.ofNat 64 layout.inputOffset) count)
    (callFrame : AgreesExcept [.reg 4,
      .mem (stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8)) 8, .rip] s u)
    (entry : u.RIP = 0x10dd60)
    (rspU : stackPtr u = stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8))
    (returnU : (returnBoundary u).rip = returnPC)
    (returned : InProgram (returnBoundary u).rip)
    (destination : s.regValue .rdi = stackPtr initial - BitVec.ofNat 64 layout.outputOffset)
    (source : s.regValue .rsi = stackPtr initial - BitVec.ofNat 64 layout.inputOffset)
    (length : s.regValue .rdx = BitVec.ofNat 64 count)
    (callRun : ∃ fuel, Advances (returnBoundary initial) fuel s u) :
    ∃ t, StackResult v initial s t count layout.inputOffset layout.outputOffset returnPC form := by
  have destinationU : u.regValue .rdi = stackPtr initial - BitVec.ofNat 64 layout.outputOffset :=
    (callFrame.read (n := 64) (r := 7) (by simp)).trans destination
  have sourceU : u.regValue .rsi = stackPtr initial - BitVec.ofNat 64 layout.inputOffset :=
    (callFrame.read (n := 64) (r := 6) (by simp)).trans source
  have lengthU : u.regValue .rdx = BitVec.ofNat 64 count :=
    (callFrame.read (n := 64) (r := 2) (by simp)).trans length
  have pre := callee_pre_of_stack ctx stateU layout entry (by rw [stackOffset]; exact rspU) sourceU destinationU returned
  obtain ⟨t, result, copied, copyFrame⟩ := Common.Memory.memcpy_correct pre lengthU
    countBound returned
  have stateT := stateU.of_callee (outputOffset := layout.outputOffset) ctx result rspU destinationU
    outputHigh outputLow (by decide)
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
      (⟨(stackPtr initial - BitVec.ofNat 64 layout.outputOffset).toNat, count⟩ : MemoryRegion) := by
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
    rw [Dispatch.stack_sub_toNat512 ctx (offset := form.frameBytes + 8) (by cases form <;> simp [Variant.routine, Form.frameBytes, Form.stackBytes])]
    omega
  have frame : MemoryWriteFrame s t #v[
      (⟨(stackPtr initial - BitVec.ofNat 64 layout.outputOffset).toNat, count⟩ : MemoryRegion),
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
  obtain ⟨callFuel, callExecution⟩ := callRun
  obtain ⟨copyFuel, copyExecution⟩ := result.execution
  refine ⟨t, ⟨callFuel + copyFuel, callExecution.trans copyExecution⟩,
    memoryWriteFrame_trans (callFrame.memoryWriteFrame (call_stack_writes ctx))
      (callee_stack_frame ctx result rspU destinationU outputHigh outputLow (by decide)),
    stateT, result.rip.trans returnU, abi, ?_, frame, ?_⟩
  · exact (callFrame.trans copyFrame).read (n := 64) (r := 3)
      (by simp [Common.Memory.Copy.copyComponents, Common.Memory.Copy.registerComponents])
  · intro i hi
    have byte := copied i hi
    rw [destinationU, sourceU] at byte
    rw [byte]
    apply callFrame.byte
    intro c hc covers
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact covers
    · obtain ⟨j, hj, eq⟩ := covers
      apply OffsetsApart.ne (c₁ := -BitVec.ofNat 64 (form.frameBytes + 8)) (len₁ := 8)
        (c₂ := -BitVec.ofNat 64 layout.inputOffset) (len₂ := count)
        sourceApart
        (stackPtr initial) hj hi (by omega)
      simpa only [BitVec.sub_eq_add_neg] using eq.symm
    · exact covers

set_option maxHeartbeats 800000 in
theorem copy_m64_at [Bindings] {v : Variant} {initial s : RamState}
    {inputs : Array Input} {form : Form} {count : Nat}
    (ctx : Context v initial inputs form) (input : State v initial s form)
    (layout : Wrapper.StackCallLayout form.stackBytes count count 0)
    (stackOffset : layout.stackOffset = form.frameBytes + 8)
    (outputHigh : count + 48 ≤ layout.outputOffset)
    (outputLow : layout.outputOffset ≤ form.frameBytes)
    (countBound : count < 2^32)
    (sourceApart : OffsetsApart (-BitVec.ofNat 64 (form.frameBytes + 8)) 8
      (-BitVec.ofNat 64 layout.inputOffset) count)
    (relative : Nat) (displacement : BitVec 32)
    (size : v.textOffset form + relative + 6 ≤ 71757)
    (bytes : Extracted.textBytes.toListFrom (v.textOffset form + relative) 6 =
      encodeCallM64 (.rip displacement))
    (pointerAddress : Extracted.textAddress + BitVec.ofNat 64 (v.textOffset form + relative) +
      6 + displacement.signExtend 64 = 0x200280)
    (returnInProgram : InProgram (v.pc (relative + 6) form))
    (rip : s.RIP = v.pc relative form)
    (destination : s.regValue .rdi = stackPtr initial - BitVec.ofNat 64 layout.outputOffset)
    (source : s.regValue .rsi = stackPtr initial - BitVec.ofNat 64 layout.inputOffset)
    (length : s.regValue .rdx = BitVec.ofNat 64 count) :
    ∃ t, StackResult v initial s t count layout.inputOffset layout.outputOffset
      (v.pc (relative + 6) form) form := by
  have pointer := Wrapper.memcpy_pointer input.loaded
  obtain ⟨u, stateU, effect, rspU, returnU, callRun⟩ := call_m64_local ctx input
    (v.textOffset form + relative) displacement 0x10dd60 size bytes
    (by decide) (inProgram_of_textOffset 0xdd60 (by decide))
    (by change MemReadable s (Extracted.textAddress + BitVec.ofNat 64 (v.textOffset form + relative) + 6 +
          displacement.signExtend 64) 8
        rw [pointerAddress]
        exact pointer.1)
    (by change (Operand.mem (Extracted.textAddress + BitVec.ofNat 64 (v.textOffset form + relative) + 6 +
          displacement.signExtend 64) : Operand 64).read s = 0x10dd60
        rw [pointerAddress]
        exact pointer.2) rip input.rsp
  have push : pushAddr s = stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8) := by
    rw [pushAddr, input.rsp, BitVec.sub_sub]
    rw [BitVec.ofNat_add]
    rfl
  have callFrame : AgreesExcept [.reg 4, .mem (stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8)) 8, .rip] s u := by
    simpa only [callEffect, pushEffect_components, push] using effect.agrees
  have returnU' : (returnBoundary u).rip = v.pc (relative + 6) form := by
    simpa only [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc, Nat.add_assoc,
      BitVec.ofNat_eq_ofNat] using returnU
  have returned : InProgram (returnBoundary u).rip := by rw [returnU']; exact returnInProgram
  exact copy_at ctx input stateU layout stackOffset outputHigh outputLow countBound
    sourceApart callFrame effect.rip rspU returnU' returned destination source length ⟨1, callRun⟩

set_option maxHeartbeats 800000 in
theorem copy [Bindings] {v : Variant} {initial s : RamState} {inputs : Array Input} {form : Form}
    (ctx : Context v initial inputs form) (input : Preserved v initial s form)
    (site : Site)
    (rip : s.RIP = v.pc (site.relativeOffset form) form)
    (destination : s.regValue .rdi = stackPtr initial - BitVec.ofNat 64 site.outputOffset)
    (source : s.regValue .rsi = stackPtr initial - BitVec.ofNat 64 site.inputOffset)
    (length : s.regValue .rdx = BitVec.ofNat 64 site.count)
    (eligible : form = .slices ∨ form = .digest := by first | exact Or.inl rfl | exact Or.inr rfl) :
    ∃ t, Result v initial s t site form := by
  obtain ⟨t, result⟩ := copy_m64_at ctx input.toState (site.layout form eligible) rfl
    (by rcases eligible with rfl | rfl <;> cases site <;> decide)
    (by rcases eligible with rfl | rfl <;> cases site <;> decide)
    (by cases site <;> decide)
    (by rcases eligible with rfl | rfl <;> cases site <;> unfold OffsetsApart <;> decide +kernel)
    (site.relativeOffset form) (site.displacement v form)
    (Nat.le_of_lt (site.bound v form eligible)) (site.bytes v form eligible)
    (site.pointer v form eligible)
    (Variant.pc_inProgram v (by rcases eligible with rfl | rfl <;> cases site <;> decide) form)
    rip destination source length
  have metadata : (match form with
      | .slices => ∀ a, (Component.mem (stackPtr initial - 624) 24).Covers a →
          t.external[a]? = s.external[a]?
      | _ => True) := by
    rcases eligible with rfl | rfl
    ·

      intro a ha
      obtain ⟨j, hj, rfl⟩ := ha
      exact Absorb.frame_bytes (offset := 624) (len := 24) (reserve := 640) ctx result.frame (by cases site <;> decide) (by cases site <;> decide) (by decide) (by decide)
        (by decide) (by decide) (by left; cases site <;> decide) j hj
    · trivial
  refine ⟨t, result.execution, result.stackFrame, Absorb.preserved_of_bytes input result.state
    (by rcases eligible with rfl | rfl <;> exact metadata) (fun _ => result.rbx)
    (by rcases eligible with rfl | rfl <;> simp), ?_,
    result.abi, result.frame, result.bytes⟩
  simpa only [Variant.pc, Site.offset, Nat.add_assoc, BitVec.ofNat_add,
    BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using result.rip

theorem initial_result [Bindings] {v : Variant} {initial s : RamState} {inputs : Array Input} {form : Form}
    (ctx : Context v initial inputs form) (input : Preserved v initial s form)
    (rip : s.RIP = v.pc (if form = .slices then 0x218 else 0x143) form)
    (eligible : form = .slices ∨ form = .digest := by first | exact Or.inl rfl | exact Or.inr rfl) :
    ∃ t, Result v initial s t .initial form := by
  obtain ⟨fuel, u, run, ready, _, effect⟩ := setupTriple v (returnBoundary initial)
    (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2 form eligible s
    (supportedMachine_readyToStep input.machine) (setupCode input.loaded form eligible) rip
  have noMem : ∀ c ∈ (setupEffect v s form).components, ∀ a, ¬ c.Covers a := by
    simp [setupEffect, Effect.components, Component.Covers]
  have stateU := Absorb.preserved_of_agrees ctx input run ready effect.agrees
    (fun c hc a ha => (noMem c hc a ha).elim)
    (by simp [setupEffect, Effect.components])
    (by simp [setupEffect, Effect.components])
    (by simp [setupEffect, Effect.components])
    (by rcases eligible with rfl | rfl <;> simp)
  have pointers : u.regValue .rdi = stackPtr initial - BitVec.ofNat 64 600 ∧
      u.regValue .rsi = stackPtr initial - BitVec.ofNat 64 392 ∧
      u.regValue .rdx = BitVec.ofNat 64 208 := by
    refine ⟨?_, ?_, ?_⟩
    · have w := effect.writes.1
      change u.regValue .rdi = stackPtr s + (if form = .slices then 32 else 0) at w
      rw [w, input.rsp]
      rcases eligible with rfl | rfl <;> simp only [Form.frameBytes, reduceIte, BitVec.sub_eq_add_neg,
        BitVec.add_assoc] <;> rfl
    · have w := effect.writes.2.1
      change u.regValue .rsi = stackPtr s + (if form = .slices then 240 else 208) at w
      rw [w, input.rsp]
      rcases eligible with rfl | rfl <;> simp only [Form.frameBytes, reduceIte, BitVec.sub_eq_add_neg,
        BitVec.add_assoc] <;> rfl
    · exact effect.writes.2.2
  obtain ⟨t, result⟩ := copy ctx stateU .initial (by rcases eligible with rfl | rfl <;> exact effect.rip) pointers.1 pointers.2.1 pointers.2.2 eligible
  have memory : u.external = s.external := effect.agrees.external noMem
  have abiSU : PreservesABI s u := by
    apply preservesABI_of_agrees effect.agrees input.directionFlag
    · intro r member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl
      · exact effect.agrees.read (n := 64) (r := 3)
          (by simp [setupEffect, Effect.components])
      · exact effect.agrees.read (n := 64) (r := 5)
          (by simp [setupEffect, Effect.components])
      · exact effect.agrees.read (n := 64) (r := 12)
          (by simp [setupEffect, Effect.components])
      · exact effect.agrees.read (n := 64) (r := 13)
          (by simp [setupEffect, Effect.components])
      · exact effect.agrees.read (n := 64) (r := 14)
          (by simp [setupEffect, Effect.components])
      · exact effect.agrees.read (n := 64) (r := 15)
          (by simp [setupEffect, Effect.components])
    all_goals simp [setupEffect, Effect.components]
  obtain ⟨copyFuel, copyRun⟩ := result.execution
  refine ⟨t, ⟨fuel + copyFuel, run.trans copyRun⟩, ?_, result.preserved, result.rip, ?_, ?_, ?_⟩
  · intro a outside
    rw [result.stackFrame a outside, memory]
  · exact ⟨fun r hr => (result.abi.1 r hr).trans (abiSU.1 r hr),
      result.abi.2.1, result.abi.2.2.1.trans abiSU.2.2.1,
      result.abi.2.2.2.trans abiSU.2.2.2⟩
  · intro a outside
    rw [result.frame a outside, memory]
  · intro i hi
    rw [result.bytes i hi, memory]

theorem initial [Bindings] {v : Variant} {initial s : RamState} {inputs : Array Input} {form : Form}
    (ctx : Context v initial inputs form) (input : Preserved v initial s form)
    (rip : s.RIP = v.pc (if form = .slices then 0x218 else 0x143) form)
    (eligible : form = .slices ∨ form = .digest := by first | exact Or.inl rfl | exact Or.inr rfl) :
    ∃ t, Preserved v initial t form ∧ t.RIP = v.pc (if form = .slices then 0x230 else 0x159) form ∧
      ∀ i < 208, t.external[stackPtr initial - 600 + BitVec.ofNat 64 i]? =
        s.external[stackPtr initial - 392 + BitVec.ofNat 64 i]? := by
  obtain ⟨t, result⟩ := initial_result ctx input rip eligible
  refine ⟨t, result.preserved, ?_, result.bytes⟩
  rcases eligible with rfl | rfl <;> exact result.rip

end Sha2.Proofs.Wrapper512.Finish.Copy

namespace Sha2.Proofs.Wrapper512.Finish.Copy

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.SHA512

set_option maxRecDepth 2000 in
theorem StackResult.buffered [Bindings] {v : Variant} {initial s t : RamState}
    {message : ByteArray} {form : Form} {returnPC : BitVec 64} {src dst : Nat}
    {sourceMemory destinationMemory : ResetLayout.MemoryOffsets}
    (result : StackResult v initial s t 208 src dst returnPC form)
    (sourceShape : sourceMemory = ⟨src - 128, src, src - 127, src - 192, src - 200⟩)
    (destinationShape : destinationMemory = ⟨dst - 128, dst, dst - 127, dst - 192, dst - 200⟩)
    (sourceBound : 200 ≤ src) (destinationBound : 200 ≤ dst)
    (input : Buffered v initial s message form sourceMemory)
    (preserved : Preserved v initial t form) :
    Buffered v initial t message form destinationMemory := by
  subst sourceMemory destinationMemory
  have address (base offset : Nat) (bound : offset ≤ base) :
      stackPtr initial - BitVec.ofNat 64 (base - offset) =
        stackPtr initial - BitVec.ofNat 64 base + BitVec.ofNat 64 offset := by
    have h : BitVec.ofNat 64 base =
        BitVec.ofNat 64 (base - offset) + BitVec.ofNat 64 offset := by
      rw [← BitVec.ofNat_add, Nat.sub_add_cancel bound]
    rw [h, ← BitVec.sub_sub, BitVec.sub_add_cancel]
  have bytes (offset j : Nat) (ho : offset ≤ 200) (hj : offset + j < 208) :
      t.external[stackPtr initial - BitVec.ofNat 64 (dst - offset) + BitVec.ofNat 64 j]? =
        s.external[stackPtr initial - BitVec.ofNat 64 (src - offset) + BitVec.ofNat 64 j]? := by
    rw [address dst offset (by omega), address src offset (by omega)]
    simpa only [BitVec.ofNat_add, BitVec.add_assoc] using result.bytes (offset + j) hj
  refine ⟨preserved, ⟨input.hashWords.1, ?_⟩, ⟨input.tailBytes.1, ?_⟩, ?_, ?_, ?_⟩
  · intro i hi
    apply Bytes.loadBytes64
    intro j hj
    have old := Common.Memory.bytes_of_loadBytes64 (input.hashWords.2 i hi) j hj
    change t.external[(stackPtr initial - BitVec.ofNat 64 (dst - 128)) +
      BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j]? = _
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, bytes 128 (8 * i + j) (by decide) (by omega)]
    simpa only [hashPointer, BitVec.add_assoc, BitVec.ofNat_add] using old
  · intro i
    have old := input.tailBytes.2 i
    have hi : i.val < 128 := Nat.lt_of_lt_of_le i.isLt (by
      have h := input.tailBytes_size
      omega)
    have copied := result.bytes i.val (by omega)
    simpa only [tailRegion, bufferPointer, BitVec.ofNat_add, BitVec.ofNat_toNat,
      BitVec.setWidth_eq] using copied.trans (by
        simpa only [tailRegion, bufferPointer, BitVec.ofNat_add, BitVec.ofNat_toNat,
          BitVec.setWidth_eq] using old)
  · have copied := bytes 127 0 (by decide) (by decide)
    simpa only [tailLengthPointer, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      copied.trans (by simpa only [tailLengthPointer, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using input.tailLength)
  · apply Eq.trans _ input.blockCount
    apply memLoad_congr
    intro j hj
    exact congrArg (fun b : Option UInt8 => b.getD 0) (bytes 192 j (by decide) (by omega))
  · apply Eq.trans _ input.blockCountHigh
    apply memLoad_congr
    intro j hj
    exact congrArg (fun b : Option UInt8 => b.getD 0) (bytes 200 j (by decide) (by omega))

end Sha2.Proofs.Wrapper512.Finish.Copy

namespace Sha2.Proofs.Wrapper512.Finish.Copy

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

theorem StackResult.kept_bytes [Bindings] {v : Variant} {initial s t : RamState}
    {inputs : Array Input} {form : Form} {count src dst offset len : Nat}
    {returnPC : BitVec 64} (result : StackResult v initial s t count src dst returnPC form)
    (ctx : Context v initial inputs form)
    (outLow : dst ≤ form.frameBytes) (outHigh : count ≤ dst)
    (low : offset ≤ form.frameBytes) (high : len ≤ offset)
    (apart : dst + len ≤ offset ∨ offset + count ≤ dst) :
    ∀ i < len, t.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      s.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  apply Absorb.frame_bytes (reserve := form.frameBytes + 8) ctx
    (by simpa only [Nat.add_sub_cancel_left] using result.frame) outLow outHigh
    (by omega) (by cases form <;> simp [Form.frameBytes, Form.stackBytes]) low high apart

theorem StackResult.preserved_trait [Bindings] {v : Variant} {initial s t : RamState}
    {inputs : Array Input} {second : Bool} {src dst : Nat} {returnPC : BitVec 64}
    (result : StackResult v initial s t 208 src dst returnPC (.traitFinalizeIntoReset second))
    (ctx : Context v initial inputs (.traitFinalizeIntoReset second))
    (input : Preserved v initial s (.traitFinalizeIntoReset second))
    (destination : dst = 392 ∨ dst = 616) :
    Preserved v initial t (.traitFinalizeIntoReset second) := by
  refine Absorb.preserved_of_bytes input result.state ?_ ?_ ?_
  · intro offset member a covers
    obtain ⟨j, hj, rfl⟩ := covers
    apply result.kept_bytes ctx (by rcases destination with rfl | rfl <;> simp [Form.frameBytes])
      (by rcases destination with rfl | rfl <;> decide) ?_ ?_ ?_ j hj
    all_goals cases second <;>
      simp only [Form.outputSlot, Form.secondOutputSlot, Form.pointerSlot, Form.lengthSlot,
        Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at member
    all_goals rcases member with rfl | rfl | rfl | rfl
    all_goals rcases destination with rfl | rfl <;> decide
  · intro h
    cases h
  · intro _
    left
    exact result.abi.1 _ (by cases v <;> simp)

end Sha2.Proofs.Wrapper512.Finish.Copy
namespace Sha2.Proofs.Wrapper512.Finish.Copy

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

set_option maxHeartbeats 1000000 in
theorem second_clone [Bindings] {v : Variant} {initial s : RamState}
    {inputs : Array Input} {message : ByteArray} {form : Form}
    (ctx : Context v initial inputs form) (input : Buffered v initial s message form)
    (eligible : form = .finalizeIntoReset true ∨ form = .traitFinalizeIntoReset true)
    (rip : s.RIP = v.pc (v.dispatchOffset form) form) :
    ∃ t, StackResult v initial s t 208 form.bufferedMemory.buffer form.finalMemory.buffer
        (v.pc (v.dispatchOffset form + 24) form) form ∧
      Buffered v initial t message form form.finalMemory := by
  obtain ⟨fuel, u, run, ready, _, effect⟩ := secondSetupTriple v form eligible
    (returnBoundary initial) (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2
    s (supportedMachine_readyToStep input.machine) (secondSetupCode input.loaded eligible) rip
  have noMem : ∀ c ∈ (cloneSetupEffect (v.pc (v.dispatchOffset form) form)
      (form == .finalizeIntoReset true) true s).components, ∀ a, ¬ c.Covers a := by
    simp [cloneSetupEffect, Effect.components, Component.Covers]
  have preservedU := Absorb.preserved_of_agrees ctx input.toPreserved run ready effect.agrees
    (fun c hc a ha => (noMem c hc a ha).elim)
    (by simp [cloneSetupEffect, Effect.components])
    (by simp [cloneSetupEffect, Effect.components])
    (by simp [cloneSetupEffect, Effect.components])
    (by rcases eligible with rfl | rfl <;> simp)
  let layout : Wrapper.StackCallLayout form.stackBytes 208 208 0 :=
    ⟨form.frameBytes + 8, form.bufferedMemory.buffer, form.finalMemory.buffer,
      by rcases eligible with rfl | rfl <;> decide,
      by rcases eligible with rfl | rfl <;> decide,
      by rcases eligible with rfl | rfl <;> decide,
      by rcases eligible with rfl | rfl <;> decide,
      by rcases eligible with rfl | rfl <;> decide,
      by rcases eligible with rfl | rfl <;> decide,
      by rcases eligible with rfl | rfl <;> decide⟩
  have dest : u.regValue .rdi = stackPtr initial - BitVec.ofNat 64 layout.outputOffset := by
    have h := effect.writes.1
    change u.regValue .rdi = stackPtr s + (if form == .finalizeIntoReset true then 240 else 32) at h
    rw [h, input.rsp]
    rcases eligible with rfl | rfl <;>
      simp [layout, Form.frameBytes, ResetLayout.finalizeMemory,
        BitVec.sub_eq_add_neg, BitVec.add_assoc]
  have source : u.regValue .rsi = stackPtr initial - BitVec.ofNat 64 layout.inputOffset := by
    have h := effect.writes.2.1
    change u.regValue .rsi = stackPtr s + (if form == .finalizeIntoReset true then 16 else 256) at h
    rw [h, input.rsp]
    rcases eligible with rfl | rfl <;>
      simp [layout, Form.frameBytes, ResetLayout.finalizeMemory,
        BitVec.sub_eq_add_neg, BitVec.add_assoc]
  let relative := v.dispatchOffset form + 18
  let displacement := BitVec.ofNat 32 (0x200280 - (0x100000 + v.textOffset form + relative + 6))
  obtain ⟨t, result⟩ := copy_m64_at ctx preservedU.toState layout rfl
    (by dsimp only [layout]; rcases eligible with rfl | rfl <;> decide)
    (by dsimp only [layout]; rcases eligible with rfl | rfl <;> decide) (by decide)
    (by dsimp only [layout]; rcases eligible with rfl | rfl <;> unfold OffsetsApart <;> decide +kernel)
    relative displacement
    (by rcases eligible with rfl | rfl <;> cases v <;> decide +kernel)
    (by rcases eligible with rfl | rfl <;> cases v <;> decide +kernel)
    (by rcases eligible with rfl | rfl <;> cases v <;> decide +kernel)
    (by apply inProgram_of_textOffset
        rcases eligible with rfl | rfl <;> cases v <;> decide +kernel)
    (by simpa only [cloneSetupEffect, relative, Variant.pc, BitVec.ofNat_add, BitVec.add_assoc, Nat.add_assoc, BitVec.ofNat_eq_ofNat] using effect.rip)
    dest source effect.writes.2.2
  have memory : u.external = s.external := effect.agrees.external noMem
  have abiSU : PreservesABI s u := by
    apply preservesABI_of_agrees effect.agrees input.directionFlag
    · intro r member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl
      · exact effect.agrees.read (n := 64) (r := 3)
          (by simp [cloneSetupEffect, Effect.components])
      · exact effect.agrees.read (n := 64) (r := 5)
          (by simp [cloneSetupEffect, Effect.components])
      · exact effect.agrees.read (n := 64) (r := 12)
          (by simp [cloneSetupEffect, Effect.components])
      · exact effect.agrees.read (n := 64) (r := 13)
          (by simp [cloneSetupEffect, Effect.components])
      · exact effect.agrees.read (n := 64) (r := 14)
          (by simp [cloneSetupEffect, Effect.components])
      · exact effect.agrees.read (n := 64) (r := 15)
          (by simp [cloneSetupEffect, Effect.components])
    all_goals simp [cloneSetupEffect, Effect.components]
  have combined : StackResult v initial s t 208 form.bufferedMemory.buffer form.finalMemory.buffer
      (v.pc (v.dispatchOffset form + 24) form) form := by
    obtain ⟨copyFuel, copyRun⟩ := result.execution
    refine ⟨⟨fuel + copyFuel, run.trans copyRun⟩, ?_, result.state, ?_, ?_, ?_, ?_, ?_⟩
    · intro a outside
      rw [result.stackFrame a outside, memory]
    · exact result.rip
    · exact ⟨fun r hr => (result.abi.1 r hr).trans (abiSU.1 r hr),
        result.abi.2.1, result.abi.2.2.1.trans abiSU.2.2.1,
        result.abi.2.2.2.trans abiSU.2.2.2⟩
    · exact result.rbx.trans (abiSU.1 .rbx (by simp))
    · intro a outside
      rw [result.frame a outside, memory]
    · intro i hi
      rw [result.bytes i hi, memory]
  have preservedT : Preserved v initial t form := by
    refine Absorb.preserved_of_bytes input.toPreserved combined.state ?_
      (by rcases eligible with rfl | rfl <;> simp)
      (by rcases eligible with rfl | rfl <;> simp)
    rcases eligible with rfl | rfl
    all_goals intro offset member a covers
    all_goals obtain ⟨j, hj, rfl⟩ := covers
    all_goals apply combined.kept_bytes ctx (by decide) (by decide) ?_ ?_ ?_ j hj
    all_goals simp only [Form.outputSlot, Form.secondOutputSlot, Form.pointerSlot, Form.lengthSlot,
      ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at member
    all_goals rcases member with rfl | rfl | rfl | rfl <;> decide
  refine ⟨t, combined, combined.buffered ?_ ?_ ?_ ?_ input preservedT⟩
  all_goals rcases eligible with rfl | rfl <;> first | rfl | decide

end Sha2.Proofs.Wrapper512.Finish.Copy
