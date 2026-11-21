import P256.Proofs.Verifying.Core.Memory
import P256.Proofs.Program.ScalarFrame.Call
import P256.Proofs.ReadBe.Interface

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Digest

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame

theorem readBe_pre [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Core.Pre s boundary) (state : ScalarFrame.FrameState s t 24 9992 1184)
    (rip : t.RIP = 0x119090) (source : t.regValue .rdi = frameBase s+424)
    (destination : t.regValue .rdx = stackPtr s - 1176)
    (count : t.regValue .rsi = 32) (limbs : t.regValue .rcx = 4)
    (bits : t.regValue .r8 = 256) (ret : InProgram (returnBoundary t).rip) :
    ReadBe.Pre t boundary := by
  have bounds := stack_bounds pre.stack
  have sp : (stackPtr t).toNat = (stackPtr s).toNat - 1184 := by
    rw [state.rsp]
    exact stack_sub_toNat pre.stack (by decide)
  have dst : (t.regValue .rdx).toNat = (stackPtr s).toNat - 1176 := by
    rw [destination]
    exact stack_sub_toNat pre.stack (by decide)
  have stackStart : (Stack.region t 128).start = (stackPtr s).toNat - 1312 := by
    change (stackPtr t).toNat - 128 = _
    rw [sp]
    omega
  have stackEnd : (Stack.region t 128).start + (Stack.region t 128).size =
      (stackPtr s).toNat - 1176 := by
    rw [stack_region_end]
    change (stackPtr t).toNat + 8 = _
    rw [sp]
    omega
  have sub (region : MemoryRegion)
      (lo : (stackPtr s).toNat - 1312 ≤ region.start)
      (hi : region.start + region.size ≤ (stackPtr s).toNat + 8) :
      ∀ a, region.Contains a → (Stack.region s 9992).Contains a := by
    intro a ha
    change region.start ≤ a ∧ a < region.start + region.size at ha
    change (stackPtr s).toNat - 9992 ≤ a ∧
      a < (Stack.region s 9992).start + (Stack.region s 9992).size
    rw [stack_region_end]
    exact ⟨Nat.le_trans (Nat.sub_le_sub_left (by decide : 1312 ≤ 9992) _)
      (Nat.le_trans lo ha.1), Nat.lt_of_lt_of_le ha.2 hi⟩
  have stackSub := sub (Stack.region t 128) (by rw [stackStart]; omega)
    (by rw [stackEnd]; omega)
  have outputSub := sub (registerRegion t .rdx 32)
    (by change _ ≤ (t.regValue .rdx).toNat; rw [dst]; omega)
    (by change (t.regValue .rdx).toNat + 32 ≤ _; rw [dst]; omega)
  have allocated (region : MemoryRegion)
      (hs : ∀ a, region.Contains a → (Stack.region s 9992).Contains a) :
      region.Allocated t.external := by
    intro a ha
    exact Option.isSome_iff_exists.mp (state.allocated a
      (Option.isSome_iff_exists.mpr (pre.stack.2.1 a (hs a.toNat ha))))
  have src : (t.regValue .rdi).toNat = (stackPtr s).toNat-752 := by
    have addr : frameBase s+424 = stackPtr s-752 := by
      simp only [frameBase,BitVec.sub_eq_add_neg,BitVec.add_assoc]
      rfl
    rw [source,addr]
    exact stack_sub_toNat pre.stack (by decide)
  have inputSub := sub (registerRegion t .rdi 32)
    (by change _ ≤ (t.regValue .rdi).toNat; rw [src]; omega)
    (by change (t.regValue .rdi).toNat + 32 ≤ _; rw [src]; omega)
  refine ⟨state.bindingsSupported, state.machine, state.directionFlag, state.loaded, rip, count, limbs, bits,
    ?_, allocated _ inputSub, ?_, allocated _ outputSub, ?_, ?_, ?_,
    pre.outerBoundary, ret⟩
  · change (t.regValue .rdi).toNat+32 < 2^32
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
      change (t.regValue .rdi).toNat ≤ a ∧ a < (t.regValue .rdi).toNat+32 at ha
      change (t.regValue .rdx).toNat ≤ a ∧ a < (t.regValue .rdx).toNat+32 at hb
      rw [src] at ha
      rw [dst] at hb
      omega
    · intro a ha hb
      change (t.regValue .rdi).toNat ≤ a ∧ a < (t.regValue .rdi).toNat+32 at ha
      change (Stack.region t 128).start ≤ a ∧
        a < (Stack.region t 128).start+(Stack.region t 128).size at hb
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
    · exact pre.avoids (Stack.region s 9992) (by simp) a (outputSub a.toNat ha)
    · exact pre.avoids (Stack.region s 9992) (by simp) a (stackSub a.toNat ha)

end P256.Proofs.Verifying.Core.Digest
