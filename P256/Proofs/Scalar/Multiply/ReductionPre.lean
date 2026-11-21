import P256.Proofs.Field.Montgomery.Wrapper.State
import P256.Proofs.Scalar.Multiply.Interface

set_option autoImplicit false

open P256.Proofs.Program

namespace P256.Proofs.Scalar.Multiply

open P256.Spec.Program.Routines
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

open P256.Proofs.Field P256.Proofs.Field.Montgomery.Wrapper

theorem reduction_pre [Bindings] {s t : RamState} {boundary : ReturnBoundary} {entryPC : BitVec 64}
    (pre : CalleePre s boundary entryPC 32 32 280) (state : SavedState s t)
    (rsp : stackPtr t = stackPtr s - 144)
    (source : t.regValue .rsi = stackPtr s - 136)
    (right : t.regValue .rdx = stackPtr s - 104)
    (destination : t.regValue .rdi = s.regValue .rdi)
    (entry : t.RIP = 0x112840 ∧ InProgram (returnBoundary t).rip) :
    BinaryFieldPre t boundary 0x112840 112 := by
  have bounds := stack_bounds pre.stack
  have hspn : (stackPtr t).toNat = (stackPtr s).toNat - 144 := by
    rw [rsp]
    exact stack_sub_toNat pre.stack (by decide)
  have hleftn : (t.regValue .rsi).toNat = (stackPtr s).toNat - 136 := by
    rw [source]
    exact stack_sub_toNat pre.stack (by decide)
  have hrightn : (t.regValue .rdx).toNat = (stackPtr s).toNat - 104 := by
    rw [right]
    exact stack_sub_toNat pre.stack (by decide)
  have outputEq : registerRegion t .rdi 32 = registerRegion s .rdi 32 := by
    simp only [registerRegion, destination]
  have hstackstart : (Stack.region t 112).start = (stackPtr s).toNat - 256 := by
    change (stackPtr t).toNat - 112 = _
    rw [hspn]
    omega
  have hstackend : (Stack.region t 112).start + (Stack.region t 112).size = (stackPtr s).toNat - 136 := by
    rw [stack_region_end, hspn]
    omega
  have stackSub : ∀ a, (Stack.region t 112).Contains a → (Stack.region s 280).Contains a := by
    intro a ha
    change (Stack.region t 112).start ≤ a ∧ a < (Stack.region t 112).start + (Stack.region t 112).size at ha
    rw [hstackend, hstackstart] at ha
    change (stackPtr s).toNat - 280 ≤ a ∧ a < (Stack.region s 280).start + (Stack.region s 280).size
    rw [stack_region_end]
    change (stackPtr s).toNat - 280 ≤ a ∧ a < (stackPtr s).toNat + 8
    constructor <;> omega
  have leftSub : ∀ a, (registerRegion t .rsi 32).Contains a → (Stack.region s 280).Contains a := by
    intro a ha
    change (t.regValue .rsi).toNat ≤ a ∧ a < (t.regValue .rsi).toNat + 32 at ha
    rw [hleftn] at ha
    change (stackPtr s).toNat - 280 ≤ a ∧ a < (Stack.region s 280).start + (Stack.region s 280).size
    rw [stack_region_end]
    change (stackPtr s).toNat - 280 ≤ a ∧ a < (stackPtr s).toNat + 8
    constructor <;> omega
  have rightSub : ∀ a, (registerRegion t .rdx 32).Contains a → (Stack.region s 280).Contains a := by
    intro a ha
    change (t.regValue .rdx).toNat ≤ a ∧ a < (t.regValue .rdx).toNat + 32 at ha
    rw [hrightn] at ha
    change (stackPtr s).toNat - 280 ≤ a ∧ a < (Stack.region s 280).start + (Stack.region s 280).size
    rw [stack_region_end]
    change (stackPtr s).toNat - 280 ≤ a ∧ a < (stackPtr s).toNat + 8
    constructor <;> omega
  refine {
    bindingsSupported := state.bindingsSupported
    machine := state.machine
    directionFlag := state.directionFlag
    loaded := state.loaded
    rip := entry.1
    inputBounded := ?_
    inputAllocated := ?_
    outputBounded := outputEq ▸ pre.outputBounded
    outputAllocated := ?_
    stack := ?_
    separation := ?_
    avoids := ?_
    outerBoundary := pre.outerBoundary
    returnInProgram := ?_
    rightBounded := ?_
    rightAllocated := ?_
    rightOutput := ?_
    rightStack := ?_ }
  · change (t.regValue .rsi).toNat + 32 < 2^32
    rw [hleftn]
    omega
  · intro a ha
    exact Option.isSome_iff_exists.mp (state.allocated a
      (Option.isSome_iff_exists.mpr (pre.stack.2.1 a (leftSub _ ha))))
  · intro a ha
    exact Option.isSome_iff_exists.mp (state.allocated a
      (Option.isSome_iff_exists.mpr (pre.outputAllocated a (outputEq ▸ ha))))
  · refine ⟨?_, ?_, ?_, ?_⟩
    · change (Stack.region t 112).start + (Stack.region t 112).size < 2^32
      rw [hstackend]
      omega
    · intro a ha
      exact Option.isSome_iff_exists.mp (state.allocated a
        (Option.isSome_iff_exists.mpr (pre.stack.2.1 a (stackSub _ ha))))
    · change 112 ≤ (stackPtr t).toNat
      rw [hspn]
      omega
    · change (stackPtr t).toNat % 16 = 8
      rw [hspn]
      have hm : (stackPtr s).toNat % 16 = 8 := pre.stack.2.2.2
      omega
  · intro i j hij
    have cases : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2) := by omega
    rcases cases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · intro a hl ho
      change (registerRegion t .rsi 32).Contains a at hl
      change (registerRegion t .rdi 32).Contains a at ho
      rw [outputEq] at ho
      exact pre.separation (1 : Fin 3) (2 : Fin 3) (by decide) _ ho (leftSub _ hl)
    · intro a hl hs
      change (t.regValue .rsi).toNat ≤ a ∧ a < (t.regValue .rsi).toNat + 32 at hl
      change (Stack.region t 112).start ≤ a ∧ a < (Stack.region t 112).start + (Stack.region t 112).size at hs
      rw [hleftn] at hl
      rw [hstackend] at hs
      omega
    · intro a ho hs
      change (registerRegion t .rdi 32).Contains a at ho
      change (Stack.region t 112).Contains a at hs
      rw [outputEq] at ho
      exact pre.separation (1 : Fin 3) (2 : Fin 3) (by decide) _ ho (stackSub _ hs)
  · intro r hr a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact pre.avoids _ (by simp) _ (outputEq ▸ ha)
    · exact pre.avoids _ (by simp) _ (stackSub _ ha)
  · exact entry.2
  · change (t.regValue .rdx).toNat + 32 < 2^32
    rw [hrightn]
    omega
  · intro a ha
    exact Option.isSome_iff_exists.mp (state.allocated a
      (Option.isSome_iff_exists.mpr (pre.stack.2.1 a (rightSub _ ha))))
  · intro a hr ho
    exact pre.separation (1 : Fin 3) (2 : Fin 3) (by decide) _ (outputEq ▸ ho) (rightSub _ hr)
  · intro a hr hs
    change (t.regValue .rdx).toNat ≤ a ∧ a < (t.regValue .rdx).toNat + 32 at hr
    change (Stack.region t 112).start ≤ a ∧ a < (Stack.region t 112).start + (Stack.region t 112).size at hs
    rw [hrightn] at hr
    rw [hstackend] at hs
    omega

end P256.Proofs.Scalar.Multiply
