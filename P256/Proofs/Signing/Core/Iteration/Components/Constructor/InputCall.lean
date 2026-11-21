import P256.Proofs.Signing.Core.Iteration.Components.Constructor.Callee
import P256.Proofs.Signing.Core.Iteration.Components.Constructor.Input

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Components.Constructor

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

variable [Bindings] {s t u : RamState} {boundary : ReturnBoundary}

theorem input_pre {entry ret : BitVec 64} {output outputBytes reserve : Nat}
    (pre : CalleePre s boundary 0x109890 32 72 512) (state : Frame s t)
    (ready : ReadyToStep u) (effect : (callEffect (fun _ => entry) ret t).Holds t u)
    (source : t.regValue .rsi = s.regValue .rsi)
    (destination : t.regValue .rdi = stackPtr t + BitVec.ofNat 64 output)
    (retInProgram : InProgram ret)
    (outputBound : output + outputBytes ≤ 192) (reserveBound : reserve ≤ 288) :
    CalleePre u boundary entry 32 outputBytes reserve := by
  have bounds := Program.stack_bounds pre.stack
  have grow (a : BitVec 64) (ha : (s.external[a]?).isSome) : (u.external[a]?).isSome :=
    effect.agrees.grow a (state.allocated a ha)
  have hsp : stackPtr u = stackPtr s - 224 :=
    effect.writes.1.trans (constructor_call_address state)
  have hspn : (stackPtr u).toNat = (stackPtr s).toNat - 224 := by
    rw [hsp]
    exact Program.stack_sub_toNat pre.stack (by decide)
  have hsi : u.regValue .rsi = s.regValue .rsi :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans source
  have inputRegion : registerRegion u .rsi 32 = registerRegion s .rsi 32 := by
    simp only [registerRegion, hsi]
  have hdi : u.regValue .rdi = stackPtr s - BitVec.ofNat 64 (216-output) :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans
      (destination.trans (Program.ScalarFrame.scalar_stack_address (frameOffset := 216) state.rsp (by decide) (by omega)))
  have hdn : (u.regValue .rdi).toNat = (stackPtr s).toNat - (216-output) := by
    rw [hdi]
    exact Program.stack_sub_toNat pre.stack (by omega)
  have sub (region : MemoryRegion)
      (lower : (stackPtr s).toNat - 512 ≤ region.start)
      (upper : region.start + region.size ≤ (stackPtr s).toNat + 8) :
      ∀ a, region.Contains a → (Stack.region s 512).Contains a := by
    intro a ha
    change region.start ≤ a ∧ a < region.start + region.size at ha
    change (stackPtr s).toNat - 512 ≤ a ∧ a < (Stack.region s 512).start + (Stack.region s 512).size
    rw [stack_region_end]
    omega
  have outputSub := sub (registerRegion u .rdi outputBytes)
    (by change _ ≤ (u.regValue .rdi).toNat; rw [hdn]; omega)
    (by change (u.regValue .rdi).toNat + outputBytes ≤ _; rw [hdn]; omega)
  have stackSub := sub (Stack.region u reserve)
    (by change _ ≤ (stackPtr u).toNat - reserve; rw [hspn]; omega)
    (by rw [stack_region_end, hspn]; omega)
  have allocated (region : MemoryRegion)
      (subset : ∀ a, region.Contains a → (Stack.region s 512).Contains a) :
      region.Allocated u.external := by
    intro a ha
    exact Option.isSome_iff_exists.mp (grow a
      (Option.isSome_iff_exists.mpr (pre.stack.2.1 a (subset a.toNat ha))))
  refine {
    bindingsSupported := bindingsSupported_of_ready_agrees state.bindingsSupported ready effect.agrees
    machine := supportedMachine_of_ready_agrees state.machine ready effect.agrees
    directionFlag := effect.agrees.directionFlagClear (by simp) state.directionFlag
    loaded := constructor_call_loaded pre state effect
    rip := effect.rip
    inputBounded := inputRegion ▸ pre.inputBounded
    inputAllocated := ?_
    outputBounded := ?_
    outputAllocated := allocated _ outputSub
    stack := ?_
    separation := ?_
    avoids := ?_
    outerBoundary := pre.outerBoundary
    returnInProgram := ?_
  }
  · rw [inputRegion]
    intro a ha
    exact Option.isSome_iff_exists.mp (grow a (Option.isSome_iff_exists.mpr (pre.inputAllocated a ha)))
  · change (u.regValue .rdi).toNat + outputBytes < 2^32
    rw [hdn]
    omega
  · refine ⟨?_, allocated _ stackSub, ?_, ?_⟩
    · change (Stack.region u reserve).start + (Stack.region u reserve).size < 2^32
      rw [stack_region_end, hspn]
      omega
    · change reserve ≤ (stackPtr u).toNat
      rw [hspn]
      omega
    · change (stackPtr u).toNat % 16 = 8
      rw [hspn]
      have hm : (stackPtr s).toNat % 16 = 8 := pre.stack.2.2.2
      omega
  · intro i j hij
    have pairs : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2) := by omega
    rcases pairs with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · change (registerRegion u .rsi 32).Disjoint (registerRegion u .rdi outputBytes)
      rw [inputRegion]
      intro a hi ho
      exact pre.separation (0 : Fin 3) (2 : Fin 3) (by decide) a hi (outputSub a ho)
    · change (registerRegion u .rsi 32).Disjoint (Stack.region u reserve)
      rw [inputRegion]
      intro a hi hs
      exact pre.separation (0 : Fin 3) (2 : Fin 3) (by decide) a hi (stackSub a hs)
    · intro a ho hs
      change (u.regValue .rdi).toNat ≤ a ∧ a < (u.regValue .rdi).toNat + outputBytes at ho
      change (Stack.region u reserve).start ≤ a ∧ a < (Stack.region u reserve).start + (Stack.region u reserve).size at hs
      rw [hdn] at ho
      rw [stack_region_end, hspn] at hs
      omega
  · intro region hr a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact pre.avoids _ (by simp) a (outputSub a.toNat ha)
    · exact pre.avoids _ (by simp) a (stackSub a.toNat ha)
  · change InProgram (stackTop u)
    rw [(callEffect_stack effect).1]
    exact retInProgram

end P256.Proofs.Signing.Core.Iteration.Components.Constructor
