import P256.Proofs.Nonce.Update.Frame
import P256.Proofs.Program.ScalarFrame.Call

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Finish

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem nested_pre [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {outerEntry entry : BitVec 64} {reserve depth callReserve : Nat} {original state : State}
    (pre : DrbgCalleePre initial boundary outerEntry reserve original)
    (frame : ScalarFrame.FrameState initial s 64 reserve (BitVec.ofNat 64 depth))
    (capacity : depth + callReserve ≤ reserve) (aligned : depth % 16 = 0)
    (rip : s.RIP = entry) (pointer : s.regValue .rdi = initial.regValue .rdi)
    (ret : InProgram (returnBoundary s).rip)
    (drbg : DrbgAt s (initial.regValue .rdi) state) :
    DrbgCalleePre s boundary entry callReserve state := by
  have bounds := stack_bounds pre.stack
  have sp : (stackPtr s).toNat = (stackPtr initial).toNat - depth := by
    rw [frame.rsp, stack_sub_toNat pre.stack (by omega)]
  have regionEq : registerRegion s .rdi 64 = registerRegion initial .rdi 64 := by
    simp only [registerRegion, pointer]
  have stackSub : ∀ a, (Stack.region s callReserve).Contains a →
      (Stack.region initial reserve).Contains a := by
    intro a ha
    change (stackPtr s).toNat - callReserve ≤ a ∧
      a < (Stack.region s callReserve).start + (Stack.region s callReserve).size at ha
    rw [stack_region_end, sp] at ha
    change (stackPtr initial).toNat - reserve ≤ a ∧
      a < (Stack.region initial reserve).start + (Stack.region initial reserve).size
    rw [stack_region_end]
    constructor <;> omega
  have grow (a : BitVec 64) (ha : ∃ b, initial.external[a]? = some b) :
      ∃ b, s.external[a]? = some b :=
    Option.isSome_iff_exists.mp (frame.allocated a (Option.isSome_iff_exists.mpr ha))
  refine {
    bindingsSupported := frame.bindingsSupported
    machine := frame.machine
    directionFlag := frame.directionFlag
    loaded := frame.loaded
    rip := rip
    stateBounded := by rw [regionEq]; exact pre.stateBounded
    stateAllocated := by rw [regionEq]; exact fun a ha => grow a (pre.stateAllocated a ha)
    stack := ?_
    separation := ?_
    avoids := ?_
    outerBoundary := pre.outerBoundary
    returnInProgram := ret
    stateBytes := by rw [pointer]; exact drbg
  }
  · refine ⟨?_, fun a ha => grow a (pre.stack.2.1 a (stackSub a.toNat ha)), ?_, ?_⟩
    · change (Stack.region s callReserve).start + (Stack.region s callReserve).size < 2^32
      rw [stack_region_end, sp]
      omega
    · change callReserve ≤ (stackPtr s).toNat
      rw [sp]
      omega
    · change (stackPtr s).toNat % 16 = 8
      rw [sp]
      have alignment : (stackPtr initial).toNat % 16 = 8 := pre.stack.2.2.2
      omega
  · rw [regionEq]
    exact fun a ha hb => pre.separation a ha (stackSub a hb)
  · intro region member a inside
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · rw [regionEq] at inside
      exact pre.avoids _ (by simp) a inside
    · exact pre.avoids _ (by simp) a (stackSub a.toNat inside)

end P256.Proofs.Nonce.Update.Finish
