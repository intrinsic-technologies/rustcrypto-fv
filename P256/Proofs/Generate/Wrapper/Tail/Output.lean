import P256.Proofs.Generate.Wrapper.Tail.Registers
import P256.Proofs.Generate.Model.Value
import P256.Proofs.Program.Output

set_option autoImplicit false

namespace P256.Proofs.Generate.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program

abbrev outputRegions (initial : RamState) (input : ByteArray) :=
  #v[outputRegion signingKeyGenerateFromRng initial [input],allocatorStateRegion,
    randomSourceRegion,callStack signingKeyGenerateFromRng initial]

abbrev OutputState [Bindings] (initial s : RamState) (input : ByteArray) (offset : Nat := 264) :=
  State initial s offset (some (outputRegion signingKeyGenerateFromRng initial [input]))

theorem State.with_output [Bindings] {initial s : RamState} {offset : Nat}
    (state : State initial s offset) (input : ByteArray) : OutputState initial s input offset := by
  refine ⟨state.execution,state.bindingsSupported,state.machine,state.loaded,state.directionFlag,
    state.rsp,state.output,state.capacity,state.savedRbx,state.savedR14,state.savedR15,
    state.returnAddress,state.otherRegisters,state.allocated,?_⟩
  intro a ha
  apply state.frame a
  intro r hr hin
  apply ha r ?_ hin
  change r ∈ outputRegions initial input
  change r ∈ wrapperRegions signingKeyGenerateFromRng initial at hr
  simpa [outputRegions,wrapperRegions] using Or.inr hr

theorem output_stack_disjoint [Bindings] {initial : RamState} {input : ByteArray}
    {slices : Array Input}
    (call : ValidCallWithSlices signingKeyGenerateFromRng initial [input] slices) :
    (outputRegion signingKeyGenerateFromRng initial [input]).Disjoint
      (Stack.region initial 4024) := by
  have sep := (call.outputSeparationIfAccepted rfl).1 (0 : Fin 5) (4 : Fin 5) (by decide)
  intro a ha hb
  exact sep a ha (stack_contains_callStack hb)

theorem work_in_stack {initial : RamState} {a : Nat}
    (stack : Stack.Valid initial 4024) (ha : (workRegion initial).Contains a) :
    (Stack.region initial 4024).Contains a := by
  have bounds := stack_bounds stack
  change (stackPtr initial).toNat-4024 ≤ a ∧
    a < (stackPtr initial).toNat-4024+(4024-24) at ha
  change (stackPtr initial).toNat-4024 ≤ a ∧
    a < (Stack.region initial 4024).start+(Stack.region initial 4024).size
  rw [stack_region_end]
  constructor <;> omega

theorem output_work_frame {initial s t : RamState} {input : ByteArray}
    (stack : Stack.Valid initial 4024)
    (memory : MemoryWriteFrame s t
      #v[outputRegion signingKeyGenerateFromRng initial [input],workRegion initial]) :
    MemoryWriteFrame s t (outputRegions initial input) := by
  intro a ha
  apply memory a
  intro r hr hin
  have cases : r = outputRegion signingKeyGenerateFromRng initial [input] ∨
      r = workRegion initial := by simpa using hr
  rcases cases with rfl | rfl
  · exact ha _ (by simp [outputRegions]) hin
  · exact ha (callStack signingKeyGenerateFromRng initial) (by simp [outputRegions])
      (stack_contains_callStack (work_in_stack stack hin))

theorem output_work_read [Bindings] {initial s t : RamState} {input : ByteArray}
    {slices : Array Input} {offset : Nat}
    (call : ValidCallWithSlices signingKeyGenerateFromRng initial [input] slices)
    (memory : MemoryWriteFrame s t
      #v[outputRegion signingKeyGenerateFromRng initial [input],workRegion initial])
    (bound : offset ≤ 24) :
    memLoad t.external (stackPtr initial-BitVec.ofNat 64 offset) 64 =
      memLoad s.external (stackPtr initial-BitVec.ofNat 64 offset) 64 := by
  have bounds := stack_bounds (show Stack.Valid initial 4024 from call.stackAvailable.1)
  have low := stack_sub_toNat call.stackAvailable.1 (offset := offset) (by change offset ≤ 4024; omega)
  apply memLoad_congr
  intro i hi
  change (t.external[stackPtr initial-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]?).getD 0 =
    (s.external[stackPtr initial-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]?).getD 0
  rw [memory _]
  intro r hr hin
  have cases : r = outputRegion signingKeyGenerateFromRng initial [input] ∨
      r = workRegion initial := by simpa using hr
  rcases cases with rfl | rfl
  · apply output_stack_disjoint call _ hin
    apply memoryRegion_contains_add call.stackAvailable.1.1 (len := 8) _ _ hi
    · change (stackPtr initial).toNat-4024 ≤ _
      rw [low]
      omega
    · rw [stack_region_end,low]
      omega
  · change (stackPtr initial).toNat-4024 ≤ _ ∧
      (stackPtr initial-BitVec.ofNat 64 offset+BitVec.ofNat 64 i).toNat <
        (stackPtr initial).toNat-4024+(4024-24) at hin
    rw [BitVec.toNat_add,BitVec.toNat_ofNat,low] at hin
    have hb : i < 8 := hi
    omega

theorem output_loaded [Bindings] {initial s t : RamState} {input : ByteArray}
    {slices : Array Input}
    (call : ValidCallWithSlices signingKeyGenerateFromRng initial [input] slices)
    (loaded : ProgramLoaded s) (memory : MemoryWriteFrame s t (outputRegions initial input)) :
    ProgramLoaded t := by
  intro a b hb
  rw [memory a]
  · exact loaded a b hb
  · intro r hr hin
    have member : r ∈ #v[outputRegion signingKeyGenerateFromRng initial [input],
        heapRegion signingKeyGenerateFromRng initial,allocatorStateRegion,
        randomSourceRegion,callStack signingKeyGenerateFromRng initial] := by
      have cases : r = outputRegion signingKeyGenerateFromRng initial [input] ∨
          r = allocatorStateRegion ∨ r = randomSourceRegion ∨
          r = callStack signingKeyGenerateFromRng initial := by simpa [outputRegions] using hr
      rcases cases with rfl | rfl | rfl | rfl <;> simp
    exact ((call.outputSeparationIfAccepted rfl).2 r member).2 a hin (.inl ⟨b,hb⟩)

theorem after_output_effect [Bindings] {initial s t : RamState} {input : ByteArray}
    {slices : Array Input} {offset nextOffset fuel : Nat} {cs : List Component}
    (call : ValidCallWithSlices signingKeyGenerateFromRng initial [input] slices)
    (state : OutputState initial s input offset)
    (run : Advances (returnBoundary initial) fuel s t) (ready : ReadyToStep t)
    (agrees : AgreesExcept cs s t)
    (writes : WritesWithin cs
      #v[outputRegion signingKeyGenerateFromRng initial [input],workRegion initial])
    (rsp : stackPtr t = stackPtr initial-BitVec.ofNat 64 nextOffset)
    (kept : ∀ r ∈ [14,3,5,12,13], Component.reg r ∉ cs)
    (df : Component.df ∉ cs) : OutputState initial t input nextOffset := by
  have memory := agrees.memoryWriteFrame writes
  have stepFrame := output_work_frame call.stackAvailable.1 memory
  obtain ⟨n,previous⟩ := state.execution
  refine ⟨⟨n+fuel,previous.trans run⟩,
    bindingsSupported_of_ready_agrees state.bindingsSupported ready agrees,
    supportedMachine_of_ready_agrees state.machine ready agrees,
    output_loaded call state.loaded stepFrame,agrees.directionFlagClear df state.directionFlag,
    rsp,(agrees.read (n := 64) (kept 14 (by simp))).trans state.output,
    (agrees.read (n := 64) (kept 3 (by simp))).trans state.capacity,
    (output_work_read call memory (by decide)).trans state.savedRbx,
    (output_work_read call memory (by decide)).trans state.savedR14,
    (output_work_read call memory (by decide)).trans state.savedR15,?_,?_,
    fun a ha => agrees.grow a (state.allocated a ha),memoryWriteFrame_trans state.frame stepFrame⟩
  · have h := output_work_read call memory (offset := 0) (by decide)
    simp only [BitVec.sub_zero] at h
    exact h.trans state.returnAddress
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (agrees.read (n := 64) (kept 5 (by simp))).trans (state.otherRegisters .rbp (by simp))
    · exact (agrees.read (n := 64) (kept 12 (by simp))).trans (state.otherRegisters .r12 (by simp))
    · exact (agrees.read (n := 64) (kept 13 (by simp))).trans (state.otherRegisters .r13 (by simp))

end P256.Proofs.Generate.Wrapper
