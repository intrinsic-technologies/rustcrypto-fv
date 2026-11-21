import Sha2.Proofs.Wrapper512.Call
import Sha2.Proofs.Common.Memory.Fill

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Hash.Finalize.Pad

open Sha2.Spec Sha2.Proofs.Program Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

def fillOffset (v : Variant) : Form → Nat
  | .slices => 0x26b
  | .digest => 0x18d
  | .reset stage => if stage.val = 2 then
      match v with
      | .sha384 => 0x75d
      | .sha512 => 0x77d
      | .sha512_224 | .sha512_256 => 0x73d
    else 0x416
  | .finalizeIntoReset second => if second then
      match v with
      | .sha384 => 0x5c3
      | .sha512 => 0x5e3
      | .sha512_224 | .sha512_256 => 0x5a5
    else 0x24a
  | .traitFinalizeIntoReset second => if second then
      match v with
      | .sha384 => 0x685
      | .sha512 => 0x6a5
      | .sha512_224 | .sha512_256 => 0x665
    else 0x2b5

theorem fill_local [Bindings] {v : Variant} {form : Form} {initial s : RamState} {inputs : Array Input}
    {count : Nat} (ctx : Context v initial inputs form) (state : State v initial s form)
    (rip : s.RIP = (v.pc (fillOffset v form) form)) (rsp : stackPtr s = stackPtr initial - BitVec.ofNat 64 form.frameBytes)
    (destination : s.regValue .rdi = stackPtr initial - BitVec.ofNat 64 (form.finalMemory.hash + count))
    (zero : s.regValue .rsi = 0) (length : s.regValue .rdx = BitVec.ofNat 64 count)
    (countBound : count ≤ 127)
 :
    ∃ t, (∃ fuel, Advances (returnBoundary initial) fuel s t) ∧ State v initial t form ∧ t.RIP = (v.pc (fillOffset v form + 6) form) ∧ stackPtr t = stackPtr initial - BitVec.ofNat 64 form.frameBytes ∧
      (∀ i < count, t.external[stackPtr initial - BitVec.ofNat 64 (form.finalMemory.hash + count) + BitVec.ofNat 64 i]? = some 0) ∧
      PreservesABI s t ∧ MemoryWriteFrame s t
        #v[(⟨(stackPtr initial - BitVec.ofNat 64 (form.finalMemory.hash + count)).toNat, count⟩ : MemoryRegion),
          (⟨(stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8)).toNat, 8⟩ : MemoryRegion)] := by
  have pointer := Wrapper.memset_pointer state.loaded
  let offset := v.textOffset form + (fillOffset v form)
  let displacement := BitVec.ofNat 32 (0x200288 - (0x100000 + offset + 6))
  have pointerAddress : Extracted.textAddress + BitVec.ofNat 64 offset + 6 + displacement.signExtend 64 =
      0x200288 := by cases form <;> cases v <;> dsimp only [offset, displacement, fillOffset, Variant.textOffset] <;> (try split) <;> decide +kernel
  obtain ⟨u, stateU, effect, rspU, returnU, callRun⟩ := call_m64_local ctx state offset displacement
    0x10dd10 (by cases form <;> cases v <;> dsimp only [offset, fillOffset, Variant.textOffset, Variant.routine, Form.frameBytes, Form.stackBytes] <;> (try split) <;> decide +kernel) (by cases form <;> cases v <;> dsimp only [offset, displacement, fillOffset, Variant.textOffset] <;> (try split) <;> decide +kernel) (by decide +kernel)
    (inProgram_of_textOffset 0xdd10 (by decide +kernel))
    (by change MemReadable s (Extracted.textAddress + BitVec.ofNat 64 offset + 6 + displacement.signExtend 64) 8
        rw [pointerAddress]; exact pointer.1)
    (by change (Operand.mem (Extracted.textAddress + BitVec.ofNat 64 offset + 6 + displacement.signExtend 64) : Operand 64).read s = _
        rw [pointerAddress]; exact pointer.2) rip rsp
  have push : pushAddr s = stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8) := by
    rw [pushAddr, rsp, BitVec.sub_sub]
    cases form <;> rfl
  have callFrame : AgreesExcept [.reg 4, .mem (stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8)) 8, .rip] s u := by
    simpa only [callEffect, pushEffect_components, push] using effect.agrees
  have destinationU : u.regValue .rdi = stackPtr initial - BitVec.ofNat 64 (form.finalMemory.hash + count) :=
    (callFrame.read (n := 64) (r := 7) (by simp)).trans destination
  have zeroU : u.regValue .rsi = 0 :=
    (callFrame.read (n := 64) (r := 6) (by simp)).trans zero
  have lengthU : u.regValue .rdx = BitVec.ofNat 64 count :=
    (callFrame.read (n := 64) (r := 2) (by simp)).trans length
  have returnInProgram : InProgram (returnBoundary u).rip := by
    rw [returnU]
    change InProgram (v.pc (fillOffset v form) form + BitVec.ofNat 64 6)
    rw [Variant.pc_add (form := form)]
    apply inProgram_of_textOffset
    change v.textOffset form + (fillOffset v form + 6) < 71757
    cases form <;> cases v <;> dsimp only [Variant.textOffset, fillOffset] <;> (try split) <;> decide +kernel
  have pre := callee_pre (inputBytes := 0) (outputBytes := count)
    (outputOffset := form.finalMemory.hash + count) (reserve := 0) ctx stateU effect.rip rspU destinationU
    (by cases form <;> dsimp only [Form.frameBytes, Form.finalMemory, ResetLayout.resetMemory, ResetLayout.finalizeMemory, ResetLayout.cloneMemory] <;> (try split) <;> (try dsimp) <;> omega) (by cases form <;> dsimp only [Form.frameBytes, Form.finalMemory, ResetLayout.resetMemory, ResetLayout.finalizeMemory, ResetLayout.cloneMemory] <;> (try split) <;> (try dsimp) <;> omega) (by decide +kernel)
    (by simp [registerRegion, MemoryRegion.Bounded, zeroU, userAddressLimit])
    (by intro a ha; have := ha.1; have := ha.2; simp only [registerRegion, MemoryRegion.Contains] at *; omega)
    (by intro a ha; have := ha.1; have := ha.2; simp only [registerRegion, MemoryRegion.Contains] at *; omega)
    returnInProgram
  obtain ⟨t, result, filled, fillFrame⟩ := Common.Memory.memset_zero_correct pre
    (by rw [zeroU]; rfl) lengthU (by omega)
    returnInProgram
  have stateT := stateU.of_callee (outputOffset := form.finalMemory.hash + count) ctx result rspU destinationU
    (by cases form <;> dsimp only [Form.frameBytes, Form.finalMemory, ResetLayout.resetMemory, ResetLayout.finalizeMemory, ResetLayout.cloneMemory] <;> (try split) <;> (try dsimp) <;> omega) (by cases form <;> dsimp only [Form.frameBytes, Form.finalMemory, ResetLayout.resetMemory, ResetLayout.finalizeMemory, ResetLayout.cloneMemory] <;> (try split) <;> (try dsimp) <;> omega) (by decide +kernel)
  have rspT : stackPtr t = stackPtr initial - BitVec.ofNat 64 form.frameBytes := by
    change t.regValue .rsp = _
    rw [result.rsp]
    change stackPtr u + 8 = _
    rw [rspU]
    rw [BitVec.ofNat_add, ← BitVec.sub_sub, BitVec.ofNat_eq_ofNat, BitVec.sub_add_cancel]
  have abi : PreservesABI s t := by
    apply preservesABI_of_agrees (callFrame.trans fillFrame) state.directionFlag
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (callFrame.trans fillFrame).read (n := 64) (r := 3)
        (by simp [Common.Memory.Fill.fillComponents, Common.Memory.Fill.registerComponents])
    · exact (callFrame.trans fillFrame).read (n := 64) (r := 5)
        (by simp [Common.Memory.Fill.fillComponents, Common.Memory.Fill.registerComponents])
    · exact (callFrame.trans fillFrame).read (n := 64) (r := 12)
        (by simp [Common.Memory.Fill.fillComponents, Common.Memory.Fill.registerComponents])
    · exact (callFrame.trans fillFrame).read (n := 64) (r := 13)
        (by simp [Common.Memory.Fill.fillComponents, Common.Memory.Fill.registerComponents])
    · exact (callFrame.trans fillFrame).read (n := 64) (r := 14)
        (by simp [Common.Memory.Fill.fillComponents, Common.Memory.Fill.registerComponents])
    · exact (callFrame.trans fillFrame).read (n := 64) (r := 15)
        (by simp [Common.Memory.Fill.fillComponents, Common.Memory.Fill.registerComponents])
    all_goals simp [Common.Memory.Fill.fillComponents, Common.Memory.Fill.registerComponents]
  have outputRegion : registerRegion u .rdi count =
      (⟨(stackPtr initial - BitVec.ofNat 64 (form.finalMemory.hash + count)).toNat, count⟩ : MemoryRegion) := by
    simp only [registerRegion, destinationU]
  have stackRegion : Stack.region u 0 =
      (⟨(stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8)).toNat, 8⟩ : MemoryRegion) := by
    change (⟨(stackPtr u).toNat - 0,
      (stackPtr u).toNat + 8 - ((stackPtr u).toNat - 0)⟩ : MemoryRegion) = _
    simp only [Nat.sub_zero, Nat.add_sub_cancel_left, rspU]
  have bounds := Dispatch.stack_bounds512 ctx
  have slotBound : (⟨(stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8)).toNat, 8⟩ : MemoryRegion).Bounded := by
    change (stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8)).toNat + 8 < 2^32
    rw [Dispatch.stack_sub_toNat512 ctx (offset := form.frameBytes + 8) (by cases form <;> cases v <;> dsimp only [offset, fillOffset, Variant.textOffset, Variant.routine, Form.frameBytes, Form.stackBytes] <;> (try split) <;> decide +kernel)]
    omega
  have frame : MemoryWriteFrame s t
      #v[(⟨(stackPtr initial - BitVec.ofNat 64 (form.finalMemory.hash + count)).toNat, count⟩ : MemoryRegion),
        (⟨(stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8)).toNat, 8⟩ : MemoryRegion)] := by
    apply memoryWriteFrame_trans (callFrame.memoryWriteFrame ?_) ?_
    · intro c hc a covers
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact covers.elim
      · obtain ⟨i, hi, rfl⟩ := covers
        exact ⟨⟨(stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8)).toNat, 8⟩, by simp,
          memoryRegion_contains_add slotBound (Nat.le_refl _) (Nat.le_refl _) hi⟩
      · exact covers.elim
    · simpa only [outputRegion, stackRegion] using result.frame
  obtain ⟨fuel, fillRun⟩ := result.execution
  exact ⟨t, ⟨1 + fuel, callRun.trans fillRun⟩, stateT, (by
      simpa only [offset, Variant.pc, BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd]
        using result.rip.trans returnU), rspT,
    fun i hi => by simpa only [destinationU] using filled i hi, abi, frame⟩

theorem fill [Bindings] {v : Variant} {form : Form} {initial s : RamState} {inputs : Array Input}
    {count : Nat} (ctx : Context v initial inputs form) (state : State v initial s form)
    (rip : s.RIP = (v.pc (if form = .slices then 0x26b else 0x18d) form)) (rsp : stackPtr s = stackPtr initial - BitVec.ofNat 64 form.frameBytes)
    (destination : s.regValue .rdi = stackPtr initial - BitVec.ofNat 64 (472 + count))
    (zero : s.regValue .rsi = 0) (length : s.regValue .rdx = BitVec.ofNat 64 count)
    (countBound : count ≤ 127)
    (eligible : form = .slices ∨ form = .digest := by first | assumption | simp) :
    ∃ t, State v initial t form ∧ t.RIP = (v.pc (if form = .slices then 0x271 else 0x193) form) ∧ stackPtr t = stackPtr initial - BitVec.ofNat 64 form.frameBytes ∧
      (∀ i < count, t.external[stackPtr initial - BitVec.ofNat 64 (472 + count) + BitVec.ofNat 64 i]? = some 0) ∧
      PreservesABI s t ∧ MemoryWriteFrame s t
        #v[(⟨(stackPtr initial - BitVec.ofNat 64 (472 + count)).toNat, count⟩ : MemoryRegion),
          (⟨(stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8)).toNat, 8⟩ : MemoryRegion)] := by
  rcases eligible with rfl | rfl
  all_goals
    obtain ⟨t, _, h⟩ := fill_local ctx state rip rsp destination zero length countBound
    exact ⟨t, h⟩

end Sha2.Proofs.Wrapper512.Hash.Finalize.Pad
