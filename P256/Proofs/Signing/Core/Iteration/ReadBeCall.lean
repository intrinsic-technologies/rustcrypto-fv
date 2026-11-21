import P256.Proofs.Signing.Core.Iteration.Memory
import P256.Proofs.Program.ScalarFrame.Call
import P256.Proofs.ReadBe.Interface

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.ReadBeCall

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame

theorem readBe_pre [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : SignPre s boundary) (state : ScalarFrame.FrameState s t 65 4584 2288)
    (rip : t.RIP = 0x119090) (destination : t.regValue .rdx = frameBase s + 1328)
    (count : t.regValue .rsi = 32) (limbs : t.regValue .rcx = 4)
    (bits : t.regValue .r8 = 256) (ret : InProgram (returnBoundary t).rip)
    (sourceBounded : (registerRegion t .rdi 32).Bounded)
    (sourceAllocated : (registerRegion t .rdi 32).Allocated t.external)
    (sourceOutput : (registerRegion t .rdi 32).Disjoint (registerRegion t .rdx 32))
    (sourceStack : (registerRegion t .rdi 32).Disjoint (Stack.region t 128)) :
    ReadBe.Pre t boundary := by
  have bounds := stack_bounds pre.stack
  have sp : (stackPtr t).toNat = (stackPtr s).toNat - 2288 := by
    rw [state.rsp]
    exact stack_sub_toNat pre.stack (by decide)
  have dst : (t.regValue .rdx).toNat = (stackPtr s).toNat - 952 := by
    rw [destination]
    change (frameBase s + 1328#64).toNat = _
    rw [NextNonce.base_add s (offset := 1328) (by decide)]
    exact stack_sub_toNat pre.stack (by decide)
  have stackStart : (Stack.region t 128).start = (stackPtr s).toNat - 2416 := by
    change (stackPtr t).toNat - 128 = _
    rw [sp]
    omega
  have stackEnd : (Stack.region t 128).start + (Stack.region t 128).size =
      (stackPtr s).toNat - 2280 := by
    rw [stack_region_end]
    change (stackPtr t).toNat + 8 = _
    rw [sp]
    omega
  have sub (region : MemoryRegion)
      (lo : (stackPtr s).toNat - 2416 ≤ region.start)
      (hi : region.start + region.size ≤ (stackPtr s).toNat + 8) :
      ∀ a, region.Contains a → (Stack.region s 4584).Contains a := by
    intro a ha
    change region.start ≤ a ∧ a < region.start + region.size at ha
    change (stackPtr s).toNat - 4584 ≤ a ∧
      a < (Stack.region s 4584).start + (Stack.region s 4584).size
    rw [stack_region_end]
    exact ⟨Nat.le_trans (Nat.sub_le_sub_left (by decide : 2416 ≤ 4584) _)
      (Nat.le_trans lo ha.1), Nat.lt_of_lt_of_le ha.2 hi⟩
  have stackSub := sub (Stack.region t 128) (by rw [stackStart]; omega)
    (by rw [stackEnd]; omega)
  have outputSub := sub (registerRegion t .rdx 32)
    (by change _ ≤ (t.regValue .rdx).toNat; rw [dst]; omega)
    (by change (t.regValue .rdx).toNat + 32 ≤ _; rw [dst]; omega)
  have allocated (region : MemoryRegion)
      (hs : ∀ a, region.Contains a → (Stack.region s 4584).Contains a) :
      region.Allocated t.external := by
    intro a ha
    exact Option.isSome_iff_exists.mp (state.allocated a
      (Option.isSome_iff_exists.mpr (pre.stack.2.1 a (hs a.toNat ha))))
  refine ⟨state.bindingsSupported, state.machine, state.directionFlag, state.loaded, rip, count, limbs, bits,
    sourceBounded, sourceAllocated, ?_, allocated _ outputSub, ?_, ?_, ?_,
    pre.outerBoundary, ret⟩
  · change (t.regValue .rdx).toNat + 32 < 2^32
    rw [dst]
    omega
  · refine ⟨?_, allocated _ stackSub, ?_, ?_⟩
    · change (Stack.region t 128).start + (Stack.region t 128).size < 2^32
      rw [stackEnd]
      omega
    · change 128 ≤ (stackPtr t).toNat
      rw [sp]
      omega
    · change (stackPtr t).toNat % 16 = 8
      rw [sp]
      have hm : (stackPtr s).toNat % 16 = 8 := pre.stack.2.2.2
      omega
  · intro i j hij
    have hi := i.isLt
    have hj := j.isLt
    have pairs : (i.val = 0 ∧ j.val = 1) ∨ (i.val = 0 ∧ j.val = 2) ∨
        (i.val = 1 ∧ j.val = 2) := by change i.val < j.val at hij; omega
    rcases pairs with ⟨hi,hj⟩ | ⟨hi,hj⟩ | ⟨hi,hj⟩
    all_goals have ei : i = ⟨_, hi ▸ i.isLt⟩ := Fin.ext hi
    all_goals have ej : j = ⟨_, hj ▸ j.isLt⟩ := Fin.ext hj
    all_goals rw [ei, ej]
    · exact sourceOutput
    · exact sourceStack
    · intro a ha hb
      change (t.regValue .rdx).toNat ≤ a ∧ a < (t.regValue .rdx).toNat + 32 at ha
      change (Stack.region t 128).start ≤ a ∧
        a < (Stack.region t 128).start + (Stack.region t 128).size at hb
      rw [dst] at ha
      rw [stackEnd] at hb
      omega
  · intro region hr a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact pre.avoids (Stack.region s 4584) (by simp) a (outputSub a.toNat ha)
    · exact pre.avoids (Stack.region s 4584) (by simp) a (stackSub a.toNat ha)

theorem readBe_result_frame [Bindings] {s entry t : RamState} {boundary : ReturnBoundary}
    {input : ByteArray} (pre : SignPre s boundary)
    (state : ScalarFrame.FrameState s entry 65 4584 2288) (result : ReadBe.Result entry t boundary input)
    (destination : entry.regValue .rdx = frameBase s + 1328) : Frame s t := by
  have bounds := stack_bounds pre.stack
  have sp : (stackPtr entry).toNat = (stackPtr s).toNat - 2288 := by
    rw [state.rsp]
    exact stack_sub_toNat pre.stack (by decide)
  have dst : (entry.regValue .rdx).toNat = (stackPtr s).toNat - 952 := by
    rw [destination]
    change (frameBase s + 1328#64).toNat = _
    rw [NextNonce.base_add s (offset := 1328) (by decide)]
    exact stack_sub_toNat pre.stack (by decide)
  have memory : MemoryWriteFrame entry t #v[registerRegion s .rdi 65, workRegion s 4584] := by
    intro a ha
    apply result.frame a
    intro region hr hin
    apply ha (workRegion s 4584) (by simp)
    have hr' : region = registerRegion entry .rdx 32 ∨ region = Stack.region entry 128 := by
      simpa using hr
    change (stackPtr s).toNat - 4584 ≤ a.toNat ∧ a.toNat < (stackPtr s).toNat - 4584 + 4536
    rcases hr' with rfl | rfl
    · change (entry.regValue .rdx).toNat ≤ a.toNat ∧
        a.toNat < (entry.regValue .rdx).toNat + 32 at hin
      rw [dst] at hin
      constructor <;> omega
    · change (stackPtr entry).toNat - 128 ≤ a.toNat ∧
        a.toNat < (Stack.region entry 128).start + (Stack.region entry 128).size at hin
      rw [stack_region_end] at hin
      change (stackPtr entry).toNat - 128 ≤ a.toNat ∧ a.toNat < (stackPtr entry).toNat + 8 at hin
      rw [sp] at hin
      constructor <;> omega
  refine ⟨result.machine, result.bindingsSupported, result.loaded, result.directionFlag,
    fun a ha => result.allocated a (state.allocated a ha),
    memoryWriteFrame_trans state.frame (output_work_frame pre.toCalleePre memory), ?_, ?_, ?_,
    result.mxcsr.trans state.mxcsr, result.fp87.trans state.fp87⟩
  · have hr : stackPtr t = stackPtr entry + 8 := result.rsp
    rw [hr, state.rsp]
    simp only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  · intro e he
    have bound : e.2 ≤ 48 := by
      simp only [Core.savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (output_work_read pre.toCalleePre (by decide) memory bound (by omega)).trans (state.saved e he)
  · have h := output_work_read pre.toCalleePre (by decide) memory (offset := 0) (n := 64) (by decide) (by decide)
    simp only [BitVec.sub_zero] at h
    exact h.trans state.returnAddress


theorem result_byte [Bindings] {s entry t : RamState} {boundary : ReturnBoundary}
    {input : ByteArray} (pre : SignPre s boundary)
    (state : FrameState s entry 65 4584 2288) (result : ReadBe.Result entry t boundary input)
    (destination : entry.regValue .rdx = frameBase s + 1328) {offset : Nat}
    (bound : offset < 2280) (apart : offset < 1328 ∨ 1360 ≤ offset) :
    t.external[frameBase s + BitVec.ofNat 64 offset]? =
      entry.external[frameBase s + BitVec.ofNat 64 offset]? := by
  have bounds := stack_bounds pre.stack
  have sp : (stackPtr entry).toNat = (stackPtr s).toNat - 2288 := by
    rw [state.rsp]
    exact stack_sub_toNat pre.stack (by decide)
  have dst : (entry.regValue .rdx).toNat = (stackPtr s).toNat - 2280 + 1328 := by
    rw [destination]
    exact NextNonce.base_nat pre (offset := 1328) (by decide)
  have addr := NextNonce.base_nat pre (offset := offset) (by omega)
  apply result.frame
  intro region hr hin
  have regions : region = registerRegion entry .rdx 32 ∨ region = Stack.region entry 128 :=
    by simpa using hr
  rcases regions with rfl | rfl
  · change (entry.regValue .rdx).toNat ≤ _ ∧
      _ < (entry.regValue .rdx).toNat + 32 at hin
    rw [dst, addr] at hin
    omega
  · change (stackPtr entry).toNat - 128 ≤ _ ∧
      _ < (Stack.region entry 128).start + (Stack.region entry 128).size at hin
    rw [stack_region_end] at hin
    change (stackPtr entry).toNat - 128 ≤ _ ∧ _ < (stackPtr entry).toNat + 8 at hin
    rw [sp, addr] at hin
    omega

theorem digest_bytes [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {digest : ByteArray} (pre : SignPre s boundary)
    (memory : MemoryWriteFrame s t #v[registerRegion s .rdi 65, Stack.region s 4584])
    (bytes : (registerRegion s .rdx 32).HasBytes s.external digest) :
    (registerRegion s .rdx 32).HasBytes t.external digest := by
  refine ⟨bytes.1,fun i => ?_⟩
  rw [memory]
  · exact bytes.2 i
  · intro region hr hin
    have member : region = registerRegion s .rdi 65 ∨ region = Stack.region s 4584 := by
      simpa using hr
    have contains : (registerRegion s .rdx 32).Contains
        (BitVec.ofNat 64 ((s.regValue .rdx).toNat+i.val)).toNat := by
      rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      apply memoryRegion_contains_add pre.digestBounded (len := 32) (Nat.le_refl _) (Nat.le_refl _)
      have hi := i.isLt
      have size : digest.size = 32 := bytes.1
      omega
    rcases member with rfl | rfl
    · exact pre.digestOutput _ contains hin
    · exact pre.digestStack _ contains hin

end P256.Proofs.Signing.Core.Iteration.ReadBeCall
