import Hkdf.Proofs.NewExpand.Extract.State
import Hkdf.Proofs.Common.CallFrame.Stack

namespace Hkdf.Proofs.NewExpand.Extract

open Hkdf.Spec Hkdf.Spec.Program Hkdf.Proofs.Common Hkdf.Proofs.Common.Machine
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure FinalizeCall [Bindings] (initial s : RamState) (boundary : ReturnBoundary)
    (salt : Option ByteArray) (ikm : ByteArray) : Prop extends
    CallFrame.Running initial boundary #v[Stack.region initial 2264] s, Saved initial s where
  rsp : stackPtr s = stackPtr initial - 464
  inputPtr : s.regValue .rsi = base initial + 264
  outputPtr : s.regValue .rdi = initial.regValue .rdi
  ret : returnBoundary s = ⟨0x10fcf6, base initial⟩
  rip : s.RIP = 0x10dd90
  hmac : HmacAt s (s.regValue .rsi) (salt.getD (RFC5869.defaultSalt .sha256)) ikm

variable [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
  {salt : Option ByteArray} {ikm : ByteArray}

theorem finalize_regions (pre : ExtractPre initial boundary salt ikm)
    (call : FinalizeCall initial s boundary salt ikm) :
    CalleePre s boundary 0x10dd90 144 176 1264 ∧
    (∀ a, (Stack.region s 1264).Contains a → (Stack.region initial 2264).Contains a) ∧
    (⟨(stackPtr initial - 48).toNat, 56⟩ : MemoryRegion).Disjoint (Stack.region s 1264) := by
  let input := registerRegion s .rsi 144
  let output := registerRegion initial .rdi 176
  let outer := Stack.region initial 2264
  let inner := Stack.region s 1264
  have low : 2264 ≤ (stackPtr initial).toNat := pre.call.stack.2.2.1
  have high := pre.call.stack.1
  change outer.start + outer.size < 2^32 at high
  have outerEnd : outer.start + outer.size = (stackPtr initial).toNat + 8 := stack_region_end initial 2264
  have outerStart : outer.start = (stackPtr initial).toNat - 2264 := rfl
  have sp : (stackPtr s).toNat = (stackPtr initial).toNat - 464 := by
    rw [call.rsp]
    exact CallFrame.stack_sub_toNat pre.call.stack (offset := 464) (by decide)
  have ip : input.start = (stackPtr initial).toNat - 192 := by
    change (s.regValue .rsi).toNat = _
    rw [call.inputPtr, base]
    have eq (p : BitVec 64) : p - 456 + 264 = p - 192 := by
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd]
    rw [eq]
    exact CallFrame.stack_sub_toNat pre.call.stack (offset := 192) (by decide)
  have innerStart : inner.start = (stackPtr initial).toNat - 1728 := by
    change (stackPtr s).toNat - 1264 = _
    rw [sp]
    omega
  have innerEnd : inner.start + inner.size = (stackPtr initial).toNat - 464 + 8 := by
    exact (stack_region_end s 1264).trans (congrArg (· + 8) sp)
  have sz : input.size = 144 := rfl
  have within {region : MemoryRegion} (start : outer.start ≤ region.start)
      (stop : region.start + region.size ≤ outer.start + outer.size) :
      ∀ a, region.Contains a → outer.Contains a := by
    intro a ⟨left, right⟩
    exact ⟨Nat.le_trans start left, Nat.lt_of_lt_of_le right stop⟩
  have inStack : ∀ a, inner.Contains a → outer.Contains a := within (by omega) (by omega)
  have inData : ∀ a, input.Contains a → outer.Contains a := within (by omega) (by omega)
  have allocated {region : MemoryRegion} (h : ∀ a, region.Contains a → outer.Contains a) :
      region.Allocated s.external := fun a ha ↦ Option.isSome_iff_exists.mp
    (call.allocated a (Option.isSome_iff_exists.mpr (pre.call.stack.2.1 a (h _ ha))))
  have away : output.Disjoint outer := pre.call.writesStackDisjoint 0
  have out : registerRegion s .rdi 176 = output := by
    simp only [registerRegion, call.outputPtr, output]
  have before : input.Disjoint inner := by
    intro a ha hb
    have left : input.start ≤ a := ha.1
    have right : a < inner.start + inner.size := hb.2
    omega
  refine ⟨?_, inStack, ?_⟩
  · refine { stride := pre.call.stride, machine := call.machine, loaded := call.loaded,
             rip := call.rip, directionFlag := call.directionFlag,
             inputBounded := ?_, inputAllocated := allocated inData,
             outputBounded := out ▸ pre.call.writesBounded output (by simp [output]),
             outputAllocated := ?_, stack := ?_, separation := ?_, avoids := ?_,
             outerBoundary := pre.call.outerBoundary, returnInProgram := ?_ }
    · change input.start + 144 < 2^32
      omega
    · rw [out]
      intro a ha
      exact Option.isSome_iff_exists.mp (call.allocated a (Option.isSome_iff_exists.mpr
        (pre.call.writesAllocated output (by simp [output]) a ha)))
    · refine ⟨?_, allocated inStack, ?_, ?_⟩
      · change inner.start + inner.size < 2^32
        omega
      · change 1264 ≤ (stackPtr s).toNat
        omega
      · have align : (stackPtr initial).toNat % 16 = 8 := pre.call.stack.2.2.2
        change (stackPtr s).toNat % 16 = 8
        omega
    · rw [out]
      intro i j h
      have cases : (i.val = 0 ∧ j.val = 1) ∨ (i.val = 0 ∧ j.val = 2) ∨
          (i.val = 1 ∧ j.val = 2) := by have := i.isLt; have := j.isLt; change i.val < j.val at h; omega
      rcases cases with ⟨hi,hj⟩ | ⟨hi,hj⟩ | ⟨hi,hj⟩
      all_goals have ei : i = ⟨_, hi ▸ i.isLt⟩ := Fin.ext hi
      all_goals have ej : j = ⟨_, hj ▸ j.isLt⟩ := Fin.ext hj
      all_goals rw [ei, ej]
      · exact fun a ha hb ↦ away a hb (inData a ha)
      · exact before
      · exact fun a ha hb ↦ away a ha (inStack a hb)
    · rw [out]
      intro region hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact pre.call.writesAvoid _ (by simp [output])
      · exact fun a ha ↦ pre.call.stackAvoid a (inStack a.toNat ha)
    · rw [call.ret]
      exact inProgram_of_textOffset 0xfcf6 (by decide)
  · have slot := CallFrame.stack_sub_toNat pre.call.stack (offset := 48) (by decide)
    intro a ha hb
    have left : (stackPtr initial - 48).toNat ≤ a := ha.1
    have right : a < inner.start + inner.size := hb.2
    change (stackPtr initial - 48).toNat = _ at slot
    omega

end Hkdf.Proofs.NewExpand.Extract
