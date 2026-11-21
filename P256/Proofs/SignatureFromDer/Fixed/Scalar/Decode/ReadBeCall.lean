import P256.Proofs.SignatureFromDer.Fixed.Scalar.State
import P256.Proofs.ReadBe.Interface

set_option autoImplicit false

open P256.Proofs.Program (CalleePre stack_region_end)

namespace P256.Proofs.SignatureFromDer.Fixed.Scalar

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem readBe_pre [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10fa20 32 40 288) (state : FrameState s t 160)
    (rip : t.RIP = 0x119090) (source : t.regValue .rdi = stackPtr s - 80)
    (destination : t.regValue .rdx = stackPtr s - 112)
    (count : t.regValue .rsi = 32) (limbs : t.regValue .rcx = 4)
    (bits : t.regValue .r8 = 256) (ret : InProgram (returnBoundary t).rip) :
    P256.Proofs.ReadBe.Pre t boundary := by
  have bounds := P256.Proofs.Program.stack_bounds pre.stack
  have sp : (stackPtr t).toNat = (stackPtr s).toNat - 160 := by
    rw [state.rsp]
    exact P256.Proofs.Program.stack_sub_toNat pre.stack (by decide)
  have src : (t.regValue .rdi).toNat = (stackPtr s).toNat - 80 := by
    rw [source]
    exact P256.Proofs.Program.stack_sub_toNat pre.stack (by decide)
  have dst : (t.regValue .rdx).toNat = (stackPtr s).toNat - 112 := by
    rw [destination]
    exact P256.Proofs.Program.stack_sub_toNat pre.stack (by decide)
  have stackStart : (Stack.region t 128).start = (stackPtr s).toNat - 288 := by
    change (stackPtr t).toNat - 128 = _
    rw [sp]
    omega
  have stackEnd : (Stack.region t 128).start + (Stack.region t 128).size =
      (stackPtr s).toNat - 152 := by
    rw [stack_region_end]
    change (stackPtr t).toNat + 8 = _
    rw [sp]
    omega
  have sub (region : MemoryRegion)
      (lo : (stackPtr s).toNat - 288 ≤ region.start)
      (hi : region.start + region.size ≤ (stackPtr s).toNat + 8) :
      ∀ a, region.Contains a → (Stack.region s 288).Contains a := by
    intro a ha
    change region.start ≤ a ∧ a < region.start + region.size at ha
    change (stackPtr s).toNat - 288 ≤ a ∧
      a < (Stack.region s 288).start + (Stack.region s 288).size
    rw [stack_region_end]
    constructor <;> omega
  have stackSub := sub (Stack.region t 128) (by rw [stackStart]; omega)
    (by rw [stackEnd]; omega)
  have inputSub := sub (registerRegion t .rdi 32)
    (by change _ ≤ (t.regValue .rdi).toNat; rw [src]; omega)
    (by change (t.regValue .rdi).toNat + 32 ≤ _; rw [src]; omega)
  have outputSub := sub (registerRegion t .rdx 32)
    (by change _ ≤ (t.regValue .rdx).toNat; rw [dst]; omega)
    (by change (t.regValue .rdx).toNat + 32 ≤ _; rw [dst]; omega)
  have allocated (region : MemoryRegion)
      (hs : ∀ a, region.Contains a → (Stack.region s 288).Contains a) :
      region.Allocated t.external := by
    intro a ha
    exact Option.isSome_iff_exists.mp (state.allocated a
      (Option.isSome_iff_exists.mpr (pre.stack.2.1 a (hs a.toNat ha))))
  refine ⟨state.bindingsSupported, state.machine, state.directionFlag, state.loaded, rip, count, limbs, bits,
    ?_, allocated _ inputSub, ?_, allocated _ outputSub, ?_, ?_, ?_, pre.outerBoundary, ret⟩
  · change (t.regValue .rdi).toNat + 32 < 2^32
    rw [src]
    omega
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
    · intro a ha hb
      change (t.regValue .rdi).toNat ≤ a ∧ a < (t.regValue .rdi).toNat + 32 at ha
      change (t.regValue .rdx).toNat ≤ a ∧ a < (t.regValue .rdx).toNat + 32 at hb
      rw [src] at ha
      rw [dst] at hb
      omega
    · intro a ha hb
      change (t.regValue .rdi).toNat ≤ a ∧ a < (t.regValue .rdi).toNat + 32 at ha
      change (Stack.region t 128).start ≤ a ∧
        a < (Stack.region t 128).start + (Stack.region t 128).size at hb
      rw [src] at ha
      rw [stackEnd] at hb
      omega
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
    · exact pre.avoids (Stack.region s 288) (by simp) a (outputSub a.toNat ha)
    · exact pre.avoids (Stack.region s 288) (by simp) a (stackSub a.toNat ha)

theorem readBe_result_frame [Bindings] {s entry t : RamState} {boundary : ReturnBoundary}
    {input : ByteArray} (pre : CalleePre s boundary 0x10fa20 32 40 288)
    (state : FrameState s entry 160) (result : P256.Proofs.ReadBe.Result entry t boundary input)
    (destination : entry.regValue .rdx = stackPtr s - 112) : FrameState s t := by
  have bounds := P256.Proofs.Program.stack_bounds pre.stack
  have sp : (stackPtr entry).toNat = (stackPtr s).toNat - 160 := by
    rw [state.rsp]
    exact P256.Proofs.Program.stack_sub_toNat pre.stack (by decide)
  have dst : (entry.regValue .rdx).toNat = (stackPtr s).toNat - 112 := by
    rw [destination]
    exact P256.Proofs.Program.stack_sub_toNat pre.stack (by decide)
  have memory : MemoryWriteFrame entry t #v[registerRegion s .rdi 40, Program.ScalarFrame.workRegion s 288] := by
    intro a ha
    apply result.frame a
    intro region hr hin
    apply ha (Program.ScalarFrame.workRegion s 288) (by simp)
    have hr' : region = registerRegion entry .rdx 32 ∨ region = Stack.region entry 128 := by
      simpa using hr
    change (stackPtr s).toNat - 288 ≤ a.toNat ∧ a.toNat < (stackPtr s).toNat - 288 + 240
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
  refine ⟨result.bindingsSupported, result.machine, result.loaded, result.directionFlag,
    fun a ha => result.allocated a (state.allocated a ha),
    memoryWriteFrame_trans state.frame (Program.ScalarFrame.output_work_frame pre memory), ?_, ?_, ?_,
    result.mxcsr.trans state.mxcsr, result.fp87.trans state.fp87⟩
  · have hr : stackPtr t = stackPtr entry + 8 := result.rsp
    rw [hr, state.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  · intro e he
    have bound : e.2 ≤ 48 := by
      simp only [P256.Proofs.Program.savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (Program.ScalarFrame.output_work_read pre (by decide) memory bound (by omega)).trans (state.saved e he)
  · have h := Program.ScalarFrame.output_work_read pre (by decide) memory (offset := 0) (n := 64) (by decide) (by decide)
    simp only [BitVec.sub_zero] at h
    exact h.trans state.returnAddress

end P256.Proofs.SignatureFromDer.Fixed.Scalar
