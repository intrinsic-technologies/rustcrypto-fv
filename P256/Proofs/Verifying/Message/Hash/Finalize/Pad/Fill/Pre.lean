import P256.Proofs.Verifying.Message.Hash.Finalize.Pad.Interface
import P256.Proofs.Program.ScalarFrame.Call
import P256.Proofs.Program.FieldCall.Result
import P256.Proofs.Program.CalleeStackFrame
import P256.Proofs.Program.Fill
import P256.Proofs.HMAC.Finalize.Padding.Fill.Call

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Hash.Finalize.Pad.Fill

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem callee_pre [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {message : ByteArray}
    (pre : Message.Pre initial boundary message)
    (state : ScalarFrame.FrameState initial s 24 9992 1184) (rip : s.RIP = 0x11c810)
    (destination : s.regValue .rdi = stackPtr initial - 1176#64 + BitVec.ofNat 64 (128 + (message.size % 64 + 1)))
    (zero : s.regValue .rsi = 0) (ret : InProgram (returnBoundary s).rip) :
    CalleePre s boundary 0x11c810 0 (63 - message.size % 64) 0 := by
  have bounds := stack_bounds pre.stack
  have rem : message.size % 64 < 64 := Nat.mod_lt _ (by decide)
  have sp : (stackPtr s).toNat = (stackPtr initial).toNat - 1184 := by
    rw [state.rsp]
    exact stack_sub_toNat pre.stack (by decide)
  have dst : (s.regValue .rdi).toNat = (stackPtr initial).toNat - 1176 + (128 + (message.size % 64 + 1)) := by
    rw [destination, toNat_add_ofNat _ _ (by rw [stack_sub_toNat pre.stack (by decide : 1176 ≤ 9992)]; omega),
      stack_sub_toNat pre.stack (by decide : 1176 ≤ 9992)]
  have sub (region : MemoryRegion)
      (lo : (stackPtr initial).toNat - 9992 ≤ region.start)
      (hi : region.start + region.size ≤ (stackPtr initial).toNat + 8) :
      ∀ a, region.Contains a → (Stack.region initial 9992).Contains a := by
    intro a ha
    change region.start ≤ a ∧ a < region.start + region.size at ha
    change (stackPtr initial).toNat - 9992 ≤ a ∧
      a < (Stack.region initial 9992).start + (Stack.region initial 9992).size
    rw [stack_region_end]
    constructor <;> omega
  have stackSub := sub (Stack.region s 0)
    (by change _ ≤ (stackPtr s).toNat - 0; rw [sp]; omega)
    (by rw [stack_region_end, sp]; omega)
  have outputSub := sub (registerRegion s .rdi (63 - message.size % 64))
    (by change _ ≤ (s.regValue .rdi).toNat; rw [dst]; omega)
    (by change (s.regValue .rdi).toNat + (63 - message.size % 64) ≤ _; rw [dst]; omega)
  have grow (a : BitVec 64) (ha : ∃ b, initial.external[a]? = some b) :
      ∃ b, s.external[a]? = some b :=
    Option.isSome_iff_exists.mp (state.allocated a (Option.isSome_iff_exists.mpr ha))
  refine {
    bindingsSupported := state.bindingsSupported
    machine := state.machine
    directionFlag := state.directionFlag
    loaded := state.loaded
    rip := rip
    inputBounded := by change (s.regValue .rsi).toNat + 0 < 2^32; rw [zero]; decide
    inputAllocated := ?_
    outputBounded := by change (s.regValue .rdi).toNat + (63 - message.size % 64) < 2^32; rw [dst]; omega
    outputAllocated := fun a ha => grow a (pre.stack.2.1 a (outputSub a.toNat ha))
    stack := ?_
    separation := ?_
    avoids := ?_
    outerBoundary := pre.outerBoundary
    returnInProgram := ret
  }
  · intro a ha
    change (s.regValue .rsi).toNat ≤ a.toNat ∧ a.toNat < (s.regValue .rsi).toNat + 0 at ha
    omega
  · refine ⟨?_, fun a ha => grow a (pre.stack.2.1 a (stackSub a.toNat ha)), Nat.zero_le _, ?_⟩
    · change (Stack.region s 0).start + (Stack.region s 0).size < 2^32
      rw [stack_region_end, sp]
      omega
    · change (stackPtr s).toNat % 16 = 8
      rw [sp]
      have align := pre.stack.2.2.2
      change (stackPtr initial).toNat % 16 = 8 at align
      omega
  · intro i j hij
    have pairs : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2) := by omega
    rcases pairs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · intro a ha _
      change (s.regValue .rsi).toNat ≤ a ∧ a < (s.regValue .rsi).toNat + 0 at ha
      omega
    · intro a ha _
      change (s.regValue .rsi).toNat ≤ a ∧ a < (s.regValue .rsi).toNat + 0 at ha
      omega
    · intro a ha hb
      change (s.regValue .rdi).toNat ≤ a ∧ a < (s.regValue .rdi).toNat + (63 - message.size % 64) at ha
      change (stackPtr s).toNat - 0 ≤ a ∧ a < (Stack.region s 0).start + (Stack.region s 0).size at hb
      rw [dst] at ha
      rw [stack_region_end, sp] at hb
      omega
  · intro region member a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact pre.avoids _ (by simp) a (outputSub a.toNat ha)
    · exact pre.avoids _ (by simp) a (stackSub a.toNat ha)


end P256.Proofs.Verifying.Message.Hash.Finalize.Pad.Fill
