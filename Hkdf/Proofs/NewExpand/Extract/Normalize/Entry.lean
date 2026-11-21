import Hkdf.Proofs.NewExpand.Extract.State
import Hkdf.Proofs.Common.CallFrame.Push

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Extract.Normalize

open Hkdf.Spec.Program Hkdf.Proofs.Program
open Hkdf.Proofs.Common Hkdf.Proofs.Common.CallFrame Hkdf.Proofs.Common.Machine
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

abbrev Running [Bindings] (initial s : RamState) (boundary : ReturnBoundary) :=
  CallFrame.Running initial boundary #v[Stack.region initial 2264] s

theorem step_text [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {P : RamState → Prop} {E : RamState → Effect} {offset next : Nat} {bytes : List UInt8}
    (running : Running initial s boundary)
    (avoid : (Stack.region initial 2264).Avoids (fun a ↦ InProgram a ∨ InPageTables a))
    (outside : ¬ InProgram boundary.rip)
    (step : StepEffect P (codeRange (Extracted.textAddress + BitVec.ofNat 64 offset) bytes) E)
    (codeBound : offset + bytes.length ≤ 115149)
    (code : Extracted.textBytes.toListFrom offset bytes.length = bytes)
    (pre : P s) (rip : (E s).rip = Extracted.textAddress + BitVec.ofNat 64 next)
    (nextBound : next < 115149)
    (writes : WritesWithin (E s).components #v[Stack.region initial 2264])
    (df : .df ∉ (E s).components) :
    ∃ t, Running initial t boundary ∧ (E s).Holds s t ∧
      t.RIP = Extracted.textAddress + BitVec.ofNat 64 next := by
  obtain ⟨t, run, ready, effect⟩ := step.advances
    (supportedMachine_readyToStep running.machine)
    (programText_slice (programLoaded_codeIn running.loaded) offset bytes codeBound code) pre
    (by rw [rip]; exact boundary_ne_program outside (inProgram_of_textOffset _ nextBound))
  exact ⟨t, running.of_agrees run ready effect.agrees writes (stack_avoids avoid) df,
    effect, effect.rip.trans rip⟩

theorem no_memory_writes {n : Nat} {regions : Vector MemoryRegion n} {components : List Component}
    (none : ∀ c ∈ components, ∀ a, ¬ c.Covers a) :
    WritesWithin components regions := fun c hc a ha ↦ (none c hc a ha).elim

theorem enter [Bindings] {initial : RamState} {boundary : ReturnBoundary}
    {salt : Option ByteArray} {ikm : ByteArray} (pre : ExtractPre initial boundary salt ikm) :
    ∃ s, Running initial s boundary ∧ s.RIP = 0x10fa91 ∧ stackPtr s = base initial ∧
      Saved initial s ∧ AgreesExcept (Encoding.Serialize.saveFrame initial ++ [.reg 4, .flags, .rip])
        initial s := by
  have code : Encoding.Serialize.SaveCode 0xfa80 := by
    constructor <;> decide +kernel
  obtain ⟨s, run, ready, _, rip, rsp, memory, frame⟩ :=
    Encoding.Serialize.save_registers_of_push (codeOffset := 0xfa80)
      (push_steps pre.call.stack (by decide) pre.call.stackAvoid pre.call.outerBoundary)
      (supportedMachine_readyToStep pre.call.machine) pre.call.loaded (show initial.RIP = _ from pre.call.rip) code
  have writes : WritesWithin (Encoding.Serialize.saveFrame initial)
      #v[Stack.region initial 2264] := by
    have within {offset : Nat} (lo : offset ≤ 2264) (hi : 8 ≤ offset) {a : BitVec 64}
        (ha : (Component.mem (stackPtr initial - BitVec.ofNat 64 offset) 8).Covers a) :
        ∃ region ∈ #v[Stack.region initial 2264], region.Contains a.toNat :=
      ⟨_, by simp, stackRegion_contains_sub pre.call.stack.2.2.1 lo hi ha⟩
    intro c hc a ha
    simp only [Encoding.Serialize.saveFrame, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact ha.elim | exact within (by decide) (by decide) ha
  have running := (CallFrame.Running.initial pre.call.machine pre.call.loaded pre.call.directionFlag)
    |>.of_agrees run ready frame writes (stack_avoids pre.call.stackAvoid)
      (by simp [Encoding.Serialize.saveFrame])
  have step := sub_r64_imm32_effect_step 0x10fa8a 0x48 0xec 408
    (by constructor <;> decide) (by decide) (by decide)
  obtain ⟨t, runningT, effect, ripT⟩ := step_text
    (offset := 0xfa8a) (next := 0xfa91) running pre.call.stackAvoid pre.call.outerBoundary step
    (by decide) (by decide +kernel) rip rfl (by decide)
    (no_memory_writes (by simp [Component.Covers])) (by simp)
  have agrees : AgreesExcept (Encoding.Serialize.saveFrame initial ++ [.reg 4, .flags, .rip])
    initial t := frame.trans effect.agrees
  have memoryT : t.external = Encoding.Serialize.saveMemory initial :=
    (effect.agrees.external (by simp [Component.Covers])).trans memory
  have rspT : stackPtr t = stackPtr s - 408 := effect.writes
  refine ⟨t, runningT, ripT, ?_, ?_, agrees⟩
  · rw [rspT, rsp, base, BitVec.sub_sub]
    rfl
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro slot member
      rw [memoryT]
      exact Encoding.Serialize.saveMemory_saved initial slot member
    · change memLoad initial.external (stackPtr initial) 64 = _
      rw [memoryT]
      simp only [Encoding.Serialize.saveMemory, BitVec.sub_eq_add_neg]
      repeat rw [memLoad_memStore_apart_right _ _ _ _ 64
        (by unfold OffsetsApart; decide +kernel) (by decide) (by decide)]
    · exact agrees.mxcsr (by simp [Encoding.Serialize.saveFrame])
    · exact agrees.fcw (by simp [Encoding.Serialize.saveFrame])

end Hkdf.Proofs.NewExpand.Extract.Normalize
