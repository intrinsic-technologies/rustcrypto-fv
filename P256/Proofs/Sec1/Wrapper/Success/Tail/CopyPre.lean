import P256.Proofs.Sec1.Wrapper.Success.Tail.Memory
import P256.Proofs.Program.ScalarFrame.CallStep
import P256.Proofs.Program.Copy

set_option autoImplicit false

namespace P256.Proofs.Sec1.Wrapper.Success.Tail

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program

theorem copy_pre [Bindings] {initial s t : RamState} {input : ByteArray}
    {slices : Array Input} {x y : Nat}
    (call : ValidCallWithSlices publicKeyFromSec1Bytes initial [input] slices)
    (model : Points.decodePublicKey input = some (.affine x y))
    (state : ReturnState initial s) (ready : ReadyToStep t) (loaded : ProgramLoaded t)
    (effect : (callEffect (fun _ => 0x11c930) 0x1018d3 s).Holds s t)
    (outside : ¬ InProgram (returnBoundary initial).rip)
    (src : t.regValue .rsi = stackPtr initial - 232)
    (dst : t.regValue .rdi = initial.regValue .rcx + 8)
    (ret : InProgram (returnBoundary t).rip) :
    CalleePre t (returnBoundary initial) 0x11c930 65 65 0 := by
  have allocated : ∀ a : BitVec 64, (initial.external[a]?).isSome → (t.external[a]?).isSome :=
    fun a ha => effect.agrees.grow a (state.allocated a ha)
  have rsp : stackPtr t = stackPtr initial - 240 := by
    have eq := congrArg (fun x : BitVec 64 => x - 8) (callEffect_stack effect).2
    simp only [BitVec.add_sub_cancel] at eq
    rw [eq, state.rsp, BitVec.sub_sub]
    rfl
  have outputEq := output_region_eq (initial := initial) model
  have outputBounded : (registerRegion initial .rcx (8 + 65)).Bounded := by
    simpa only [ValidOutput,outputEq] using (call.outputInMemoryIfAccepted (accepted_of_model model)).2.1
  have outputAllocated : (registerRegion initial .rcx (8 + 65)).Allocated initial.external := by
    simpa only [ValidOutput,outputEq] using (call.outputInMemoryIfAccepted (accepted_of_model model)).2.2
  have separated : (registerRegion initial .rcx (8 + 65)).Disjoint (Stack.region initial 4048) :=
    outputEq ▸ output_stack_disjoint call model
  have outputAvoids : (registerRegion initial .rcx (8 + 65)).Avoids
      (fun a => InProgram a ∨ InPageTables a) := by
    rw [← outputEq]
    exact ((call.outputSeparationIfAccepted (accepted_of_model model)).2 _ (by simp)).2
  have bounds := stack_bounds (show Stack.Valid initial 4048 from call.stackAvailable.1)
  have sp : (stackPtr t).toNat = (stackPtr initial).toNat - 240 := by
    rw [rsp]
    exact stack_sub_toNat call.stackAvailable.1 (by decide)
  have si : (t.regValue .rsi).toNat = (stackPtr initial).toNat - 232 := by
    rw [src]
    exact stack_sub_toNat call.stackAvailable.1 (by decide)
  have outputLow : (initial.regValue .rcx).toNat+(8 + 65) < 2^32 := outputBounded
  have di : (t.regValue .rdi).toNat = (initial.regValue .rcx).toNat+8 := by
    rw [dst,BitVec.toNat_add]
    change ((initial.regValue .rcx).toNat+8)%2^64 = _
    omega
  have inputSub : ∀ a, (registerRegion t .rsi 65).Contains a →
      (Stack.region initial 4048).Contains a := by
    intro a ha
    change (t.regValue .rsi).toNat ≤ a ∧ a < (t.regValue .rsi).toNat+65 at ha
    rw [si] at ha
    change (stackPtr initial).toNat-4048 ≤ a ∧
      a < (Stack.region initial 4048).start+(Stack.region initial 4048).size
    rw [stack_region_end]
    constructor <;> omega
  have outputSub : ∀ a, (registerRegion t .rdi 65).Contains a →
      (registerRegion initial .rcx (8 + 65)).Contains a := by
    intro a ha
    change (t.regValue .rdi).toNat ≤ a ∧ a < (t.regValue .rdi).toNat+65 at ha
    rw [di] at ha
    change (initial.regValue .rcx).toNat ≤ a ∧ a < (initial.regValue .rcx).toNat+(8 + 65)
    constructor <;> omega
  have stackSub : ∀ a, (Stack.region t 0).Contains a →
      (Stack.region initial 4048).Contains a := by
    intro a ha
    change (Stack.region t 0).start ≤ a ∧ a < (Stack.region t 0).start+(Stack.region t 0).size at ha
    rw [stack_region_end] at ha
    change (stackPtr t).toNat-0 ≤ a ∧ a < (stackPtr t).toNat+8 at ha
    rw [sp] at ha
    change (stackPtr initial).toNat-4048 ≤ a ∧
      a < (Stack.region initial 4048).start+(Stack.region initial 4048).size
    rw [stack_region_end]
    constructor <;> omega
  have alloc (r : MemoryRegion) (hr : ∀ a, r.Contains a → (Stack.region initial 4048).Contains a) :
      r.Allocated t.external := by
    intro a ha
    exact Option.isSome_iff_exists.mp (allocated a
      (Option.isSome_iff_exists.mpr (call.stackAvailable.1.2.1 a (hr a.toNat ha))))
  refine ⟨bindingsSupported_of_ready_agrees state.bindingsSupported ready effect.agrees,
    supportedMachine_of_ready_agrees state.machine ready effect.agrees,
    effect.agrees.directionFlagClear (by simp [pushEffect_components]) state.directionFlag,
    loaded,effect.rip,
    ?_,alloc _ inputSub,?_,?_,?_,?_,?_,outside,ret⟩
  · change (t.regValue .rsi).toNat+65 < 2^32
    rw [si]
    omega
  · change (t.regValue .rdi).toNat+65 < 2^32
    rw [di]
    omega
  · intro a ha
    exact Option.isSome_iff_exists.mp (allocated a
      (Option.isSome_iff_exists.mpr (outputAllocated a (outputSub a.toNat ha))))
  · refine ⟨?_,alloc _ stackSub,Nat.zero_le _,?_⟩
    · change (Stack.region t 0).start+(Stack.region t 0).size < 2^32
      rw [stack_region_end,sp]
      omega
    · change (stackPtr t).toNat%16 = 8
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
      change (t.regValue .rsi).toNat ≤ a ∧ a < (t.regValue .rsi).toNat+65 at ha
      change (Stack.region t 0).start ≤ a ∧ a < (Stack.region t 0).start+(Stack.region t 0).size at hb
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

end P256.Proofs.Sec1.Wrapper.Success.Tail
