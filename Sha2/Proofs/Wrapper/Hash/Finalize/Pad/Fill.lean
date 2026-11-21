import Sha2.Proofs.Wrapper.Call
import Sha2.Proofs.Common.Memory.Fill

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper.Hash.Finalize.Pad

open Sha2.Spec Sha2.Proofs.Program Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

theorem fill [Bindings] {v : Variant} {initial s : RamState} {inputs : Array Input}
    {count : Nat} (ctx : Context initial inputs v) (state : State initial s v)
    (rip : s.RIP = (v.pc 0x1f6)) (rsp : stackPtr s = stackPtr initial - 344)
    (destination : s.regValue .rdi = stackPtr initial - BitVec.ofNat 64 (280 + count))
    (zero : s.regValue .rsi = 0) (length : s.regValue .rdx = BitVec.ofNat 64 count)
    (countBound : count ≤ 63) :
    ∃ t, State initial t v ∧ t.RIP = (v.pc 0x1fc) ∧ stackPtr t = stackPtr initial - 344 ∧
      (∀ i < count, t.external[stackPtr initial - BitVec.ofNat 64 (280 + count) + BitVec.ofNat 64 i]? = some 0) ∧
      PreservesABI s t ∧ MemoryWriteFrame s t
        #v[(⟨(stackPtr initial - BitVec.ofNat 64 (280 + count)).toNat, count⟩ : MemoryRegion),
          (⟨(stackPtr initial - 352).toNat, 8⟩ : MemoryRegion)] := by
  have pointer := memset_pointer state.loaded
  let offset := v.textOffset + 0x1f6
  let displacement := BitVec.ofNat 32 (0x200288 - (0x100000 + offset + 6))
  have pointerAddress : Extracted.textAddress + BitVec.ofNat 64 offset + 6 + displacement.signExtend 64 =
      0x200288 := by cases v <;> decide +kernel
  obtain ⟨u, stateU, effect, rspU, returnU⟩ := call_m64 ctx state offset displacement
    0x10dd10 (by cases v <;> decide) (by cases v <;> decide +kernel) (by decide)
    (inProgram_of_textOffset 0xdd10 (by decide))
    (by change MemReadable s (Extracted.textAddress + BitVec.ofNat 64 offset + 6 + displacement.signExtend 64) 8
        rw [pointerAddress]; exact pointer.1)
    (by change (Operand.mem (Extracted.textAddress + BitVec.ofNat 64 offset + 6 + displacement.signExtend 64) : Operand 64).read s = _
        rw [pointerAddress]; exact pointer.2) rip rsp
  have returnPc : (returnBoundary u).rip = v.pc 0x1fc := by
    rw [returnU]
    simp only [Variant.pc, offset, BitVec.ofNat_add, BitVec.add_assoc,
      BitVec.ofNat_eq_ofNat, BitVec.reduceAdd]
  have push : pushAddr s = stackPtr initial - 352 := by
    rw [pushAddr, rsp, BitVec.sub_sub]
    rfl
  have callFrame : AgreesExcept [.reg 4, .mem (stackPtr initial - 352) 8, .rip] s u := by
    simpa only [callEffect, pushEffect_components, push] using effect.agrees
  have destinationU : u.regValue .rdi = stackPtr initial - BitVec.ofNat 64 (280 + count) :=
    (callFrame.read (n := 64) (r := 7) (by simp)).trans destination
  have zeroU : u.regValue .rsi = 0 :=
    (callFrame.read (n := 64) (r := 6) (by simp)).trans zero
  have lengthU : u.regValue .rdx = BitVec.ofNat 64 count :=
    (callFrame.read (n := 64) (r := 2) (by simp)).trans length
  have pre := Wrapper.callee_pre (inputBytes := 0) (outputBytes := count)
    (outputOffset := 280 + count) (reserve := 0) ctx stateU effect.rip rspU destinationU
    (by omega) (by omega) (by decide)
    (by simp [registerRegion, MemoryRegion.Bounded, zeroU, userAddressLimit])
    (by intro a ha; have := ha.1; have := ha.2; simp only [registerRegion, MemoryRegion.Contains] at *; omega)
    (by intro a ha; have := ha.1; have := ha.2; simp only [registerRegion, MemoryRegion.Contains] at *; omega)
    (by rw [returnPc]; exact v.pc_inProgram (by decide))
  obtain ⟨t, result, filled, fillFrame⟩ := Common.Memory.memset_zero_correct pre
    (by rw [zeroU]; rfl) lengthU (by omega)
    (by rw [returnPc]; exact v.pc_inProgram (by decide))
  have stateT := stateU.of_callee (outputOffset := 280 + count) ctx result rspU destinationU
    (by omega) (by omega) (by decide)
  have rspT : stackPtr t = stackPtr initial - 344 := by
    change t.regValue .rsp = _
    rw [result.rsp]
    change stackPtr u + 8 = _
    rw [rspU]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd]
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
      (⟨(stackPtr initial - BitVec.ofNat 64 (280 + count)).toNat, count⟩ : MemoryRegion) := by
    simp only [registerRegion, destinationU]
  have stackRegion : Stack.region u 0 =
      (⟨(stackPtr initial - 352).toNat, 8⟩ : MemoryRegion) := by
    change (⟨(stackPtr u).toNat - 0,
      (stackPtr u).toNat + 8 - ((stackPtr u).toNat - 0)⟩ : MemoryRegion) = _
    simp only [Nat.sub_zero, Nat.add_sub_cancel_left, rspU]
  have bounds := validCall_stack_bounds ctx.call
  have slotBound : (⟨(stackPtr initial - 352).toNat, 8⟩ : MemoryRegion).Bounded := by
    change (stackPtr initial - BitVec.ofNat 64 352).toNat + 8 < 2^32
    rw [validCall_stack_sub_toNat ctx.call (offset := 352) (by decide)]
    omega
  have frame : MemoryWriteFrame s t
      #v[(⟨(stackPtr initial - BitVec.ofNat 64 (280 + count)).toNat, count⟩ : MemoryRegion),
        (⟨(stackPtr initial - 352).toNat, 8⟩ : MemoryRegion)] := by
    apply memoryWriteFrame_trans (callFrame.memoryWriteFrame ?_) ?_
    · intro c hc a covers
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact covers.elim
      · obtain ⟨i, hi, rfl⟩ := covers
        exact ⟨⟨(stackPtr initial - 352).toNat, 8⟩, by simp,
          memoryRegion_contains_add slotBound (Nat.le_refl _) (Nat.le_refl _) hi⟩
      · exact covers.elim
    · simpa only [outputRegion, stackRegion] using result.frame
  exact ⟨t, stateT, result.rip.trans returnPc, rspT,
    fun i hi => by simpa only [destinationU] using filled i hi, abi, frame⟩

end Sha2.Proofs.Wrapper.Hash.Finalize.Pad
