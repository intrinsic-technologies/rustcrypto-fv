import P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar.Result

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar

open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Proofs.Verifying.Combination.Naf

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Program (stack_bounds stack_sub_toNat)

theorem stack_buffer_sub [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {cursor point : BitVec 64} (pre : ScalarPre s boundary cursor point)
    {r : Syntax.Reg} {offset len : Nat} (ho : offset ≤ 536) (hl : len ≤ offset+8)
    (value : t.regValue r = stackPtr s - BitVec.ofNat 64 offset) :
    ∀ a, (registerRegion t r len).Contains a → (Stack.region s 536).Contains a := by
  have bounds := stack_bounds pre.stack
  have low : (t.regValue r).toNat = (stackPtr s).toNat - offset := by
    rw [value, stack_sub_toNat pre.stack ho]
  intro a ha
  change (t.regValue r).toNat ≤ a ∧ a < (t.regValue r).toNat + len at ha
  rw [low] at ha
  change (stackPtr s).toNat - 536 ≤ a ∧
    a < (Stack.region s 536).start + (Stack.region s 536).size
  rw [stack_region_end]
  constructor <;> omega

theorem stack_buffer_bound [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {cursor point : BitVec 64} (pre : ScalarPre s boundary cursor point)
    {r : Syntax.Reg} {offset len : Nat} (ho : offset ≤ 536) (hl : len ≤ offset+8)
    (value : t.regValue r = stackPtr s - BitVec.ofNat 64 offset) :
    (registerRegion t r len).Bounded := by
  have bounds := stack_bounds pre.stack
  change (t.regValue r).toNat + len < 2^32
  rw [value, stack_sub_toNat pre.stack ho]
  omega

theorem stack_buffer_allocated [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {cursor point : BitVec 64} {so : BitVec 64} (pre : ScalarPre s boundary cursor point)
    (state : FrameState s t cursor so) {r : Syntax.Reg} {offset len : Nat}
    (ho : offset ≤ 536) (hl : len ≤ offset+8)
    (value : t.regValue r = stackPtr s - BitVec.ofNat 64 offset) :
    (registerRegion t r len).Allocated t.external := by
  intro a ha
  exact Option.isSome_iff_exists.mp (state.allocated a
    (Option.isSome_iff_exists.mpr (pre.stack.2.1 a (stack_buffer_sub pre ho hl value a.toNat ha))))

theorem stack_buffer_stack [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {cursor point : BitVec 64} (pre : ScalarPre s boundary cursor point)
    (state : FrameState s t cursor 368) {r : Syntax.Reg} {offset len reserve : Nat}
    (ho : offset ≤ 360) (value : t.regValue r = stackPtr s - BitVec.ofNat 64 offset) :
    (registerRegion t r len).Disjoint (Stack.region t reserve) := by
  have bounds := stack_bounds pre.stack
  have low : (t.regValue r).toNat = (stackPtr s).toNat - offset := by
    rw [value, stack_sub_toNat pre.stack (by omega)]
  have sp : (stackPtr t).toNat = (stackPtr s).toNat - 368 := by
    rw [state.rsp]
    exact stack_sub_toNat pre.stack (offset := 368) (by decide)
  intro a ha hb
  change (t.regValue r).toNat ≤ a ∧ a < (t.regValue r).toNat + len at ha
  change (stackPtr t).toNat - reserve ≤ a ∧
    a < (Stack.region t reserve).start + (Stack.region t reserve).size at hb
  rw [low] at ha
  rw [stack_region_end, sp] at hb
  omega

theorem empty_input_pre [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {cursor point entry : BitVec 64} {offset len reserve : Nat}
    (pre : ScalarPre s boundary cursor point) (state : FrameState s t cursor 368)
    (rip : t.RIP = entry) (value : t.regValue .rdi = stackPtr s - BitVec.ofNat 64 offset)
    (ho : offset ≤ 360) (hl : len ≤ offset+8) (reserved : reserve + 368 ≤ 536)
    (inputLow : (t.regValue .rsi).toNat < 2^32)
    (ret : InProgram (returnBoundary t).rip) : CalleePre t boundary entry 0 len reserve := by
  have bounds := stack_bounds pre.stack
  have sp : (stackPtr t).toNat = (stackPtr s).toNat - 368 := by
    rw [state.rsp]
    exact stack_sub_toNat pre.stack (offset := 368) (by decide)
  have sub : ∀ a, (Stack.region t reserve).Contains a → (Stack.region s 536).Contains a := by
    intro a ha
    change (stackPtr t).toNat - reserve ≤ a ∧
      a < (Stack.region t reserve).start + (Stack.region t reserve).size at ha
    rw [stack_region_end, sp] at ha
    change (stackPtr s).toNat - 536 ≤ a ∧
      a < (Stack.region s 536).start + (Stack.region s 536).size
    rw [stack_region_end]
    constructor <;> omega
  refine {
    bindingsSupported := state.bindingsSupported
    machine := state.machine
    directionFlag := state.directionFlag
    loaded := state.loaded
    rip := rip
    inputBounded := by simpa only [registerRegion, MemoryRegion.Bounded, userAddressLimit, Nat.add_zero] using inputLow
    inputAllocated := ?_
    outputBounded := stack_buffer_bound pre (by omega) hl value
    outputAllocated := stack_buffer_allocated pre state (by omega) hl value
    stack := ?_
    separation := ?_
    avoids := ?_
    outerBoundary := pre.outerBoundary
    returnInProgram := ret
  }
  · intro a ha
    have ha' : (t.regValue .rsi).toNat ≤ a.toNat ∧ a.toNat < (t.regValue .rsi).toNat + 0 := ha
    omega
  · refine ⟨?_, ?_, ?_, ?_⟩
    · change (Stack.region t reserve).start + (Stack.region t reserve).size < 2^32
      rw [stack_region_end, sp]
      omega
    · intro a ha
      exact Option.isSome_iff_exists.mp (state.allocated a
        (Option.isSome_iff_exists.mpr (pre.stack.2.1 a (sub a.toNat ha))))
    · change reserve ≤ (stackPtr t).toNat
      rw [sp]
      omega
    · change (stackPtr t).toNat % 16 = 8
      rw [sp]
      have h : (stackPtr s).toNat % 16 = 8 := pre.stack.2.2.2
      omega
  · intro i j hij
    have hi := i.isLt
    have hj := j.isLt
    have cases : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2) := by omega
    rcases cases with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · intro a ha hb
      change (t.regValue .rsi).toNat ≤ a ∧ a < (t.regValue .rsi).toNat + 0 at ha
      omega
    · intro a ha hb
      change (t.regValue .rsi).toNat ≤ a ∧ a < (t.regValue .rsi).toNat + 0 at ha
      omega
    · exact stack_buffer_stack pre state ho value
  · intro region hr a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact pre.avoids _ (by simp) a (stack_buffer_sub pre (by omega) hl value a.toNat ha)
    · exact pre.avoids _ (by simp) a (sub a.toNat ha)

end P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar
