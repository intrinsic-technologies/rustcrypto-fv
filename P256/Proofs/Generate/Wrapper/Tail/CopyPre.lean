import P256.Proofs.Generate.Wrapper.Tail.ScalarCopy
import P256.Proofs.Program.Copy

set_option autoImplicit false

namespace P256.Proofs.Generate.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program

theorem copy_pre [Bindings] {initial s : RamState} {input : ByteArray} {slices : Array Input} {d : Nat}
    (call : ValidCallWithSlices signingKeyGenerateFromRng initial [input] slices)
    (draw : Ecdh.drawNonzeroScalar input = some d) (state : OutputState initial s input 272)
    (outside : ¬ InProgram (returnBoundary initial).rip)
    (rip : s.RIP = 0x11c930) (src : s.regValue .rsi = stackPtr initial - 256)
    (dst : s.regValue .rdi = initial.regValue .rcx + 40)
    (ret : InProgram (returnBoundary s).rip) :
    CalleePre s (returnBoundary initial) 0x11c930 65 65 0 := by
  have outputEq := output_region_eq (initial := initial) draw
  have outputBounded : (registerRegion initial .rcx 105).Bounded := by
    simpa only [ValidOutput,outputEq] using (call.outputInMemoryIfAccepted rfl).2.1
  have outputAllocated : (registerRegion initial .rcx 105).Allocated initial.external := by
    simpa only [ValidOutput,outputEq] using (call.outputInMemoryIfAccepted rfl).2.2
  have separated : (registerRegion initial .rcx 105).Disjoint (Stack.region initial 4024) :=
    outputEq ▸ output_stack_disjoint call
  have outputAvoids : (registerRegion initial .rcx 105).Avoids
      (fun a => InProgram a ∨ InPageTables a) := by
    rw [← outputEq]
    exact ((call.outputSeparationIfAccepted rfl).2 _ (by simp)).2
  have bounds := stack_bounds (show Stack.Valid initial 4024 from call.stackAvailable.1)
  have sp : (stackPtr s).toNat = (stackPtr initial).toNat - 272 := by
    rw [state.rsp]
    exact stack_sub_toNat call.stackAvailable.1 (by decide)
  have si : (s.regValue .rsi).toNat = (stackPtr initial).toNat - 256 := by
    rw [src]
    exact stack_sub_toNat call.stackAvailable.1 (by decide)
  have outputLow : (initial.regValue .rcx).toNat+105 < 2^32 := outputBounded
  have di : (s.regValue .rdi).toNat = (initial.regValue .rcx).toNat+40 := by
    rw [dst,BitVec.toNat_add]
    change ((initial.regValue .rcx).toNat+40)%2^64 = _
    omega
  have inputSub : ∀ a, (registerRegion s .rsi 65).Contains a →
      (Stack.region initial 4024).Contains a := by
    intro a ha
    change (s.regValue .rsi).toNat ≤ a ∧ a < (s.regValue .rsi).toNat+65 at ha
    rw [si] at ha
    change (stackPtr initial).toNat-4024 ≤ a ∧
      a < (Stack.region initial 4024).start+(Stack.region initial 4024).size
    rw [stack_region_end]
    constructor <;> omega
  have outputSub : ∀ a, (registerRegion s .rdi 65).Contains a →
      (registerRegion initial .rcx 105).Contains a := by
    intro a ha
    change (s.regValue .rdi).toNat ≤ a ∧ a < (s.regValue .rdi).toNat+65 at ha
    rw [di] at ha
    change (initial.regValue .rcx).toNat ≤ a ∧ a < (initial.regValue .rcx).toNat+105
    constructor <;> omega
  have stackSub : ∀ a, (Stack.region s 0).Contains a →
      (Stack.region initial 4024).Contains a := by
    intro a ha
    change (Stack.region s 0).start ≤ a ∧ a < (Stack.region s 0).start+(Stack.region s 0).size at ha
    rw [stack_region_end] at ha
    change (stackPtr s).toNat-0 ≤ a ∧ a < (stackPtr s).toNat+8 at ha
    rw [sp] at ha
    change (stackPtr initial).toNat-4024 ≤ a ∧
      a < (Stack.region initial 4024).start+(Stack.region initial 4024).size
    rw [stack_region_end]
    constructor <;> omega
  have alloc (r : MemoryRegion) (hr : ∀ a, r.Contains a → (Stack.region initial 4024).Contains a) :
      r.Allocated s.external := by
    intro a ha
    exact Option.isSome_iff_exists.mp (state.allocated a
      (Option.isSome_iff_exists.mpr (call.stackAvailable.1.2.1 a (hr a.toNat ha))))
  refine ⟨state.bindingsSupported,state.machine,state.directionFlag,state.loaded,rip,
    ?_,alloc _ inputSub,?_,?_,?_,?_,?_,outside,ret⟩
  · change (s.regValue .rsi).toNat+65 < 2^32
    rw [si]
    omega
  · change (s.regValue .rdi).toNat+65 < 2^32
    rw [di]
    omega
  · intro a ha
    exact Option.isSome_iff_exists.mp (state.allocated a
      (Option.isSome_iff_exists.mpr (outputAllocated a (outputSub a.toNat ha))))
  · refine ⟨?_,alloc _ stackSub,Nat.zero_le _,?_⟩
    · change (Stack.region s 0).start+(Stack.region s 0).size < 2^32
      rw [stack_region_end,sp]
      omega
    · change (stackPtr s).toNat%16 = 8
      rw [sp]
      have h : (stackPtr initial).toNat%16 = 8 := call.stackAvailable.1.2.2.2
      omega
  · intro i j hij
    have hi := i.isLt
    have hj := j.isLt
    have pairs : (i.val=0 ∧ j.val=1) ∨ (i.val=0 ∧ j.val=2) ∨ (i.val=1 ∧ j.val=2) := by
      change i.val < j.val at hij
      omega
    rcases pairs with ⟨hi,hj⟩ | ⟨hi,hj⟩ | ⟨hi,hj⟩
    all_goals have ei : i = ⟨_,hi ▸ i.isLt⟩ := Fin.ext hi
    all_goals have ej : j = ⟨_,hj ▸ j.isLt⟩ := Fin.ext hj
    all_goals rw [ei,ej]
    · intro a ha hb
      exact separated a (outputSub a hb) (inputSub a ha)
    · intro a ha hb
      change (s.regValue .rsi).toNat ≤ a ∧ a < (s.regValue .rsi).toNat+65 at ha
      change (Stack.region s 0).start ≤ a ∧ a < (Stack.region s 0).start+(Stack.region s 0).size at hb
      rw [si] at ha
      rw [stack_region_end,sp] at hb
      omega
    · intro a ha hb
      exact separated a (outputSub a ha) (stackSub a hb)
  · intro r hr a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact outputAvoids a (outputSub a.toNat ha)
    · exact call_stack_avoids call a (stackSub a.toNat ha)

end P256.Proofs.Generate.Wrapper
