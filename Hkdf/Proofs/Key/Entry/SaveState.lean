import Hkdf.Proofs.Key.Entry.Save
import Hkdf.Proofs.Key.Memory
import Hkdf.Proofs.Common.Machine.CallReturn

set_option autoImplicit false

namespace Hkdf.Proofs.Key.Entry

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Spec.Program
open Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.Machine (supportedMachine_readyToStep supportedMachine_of_ready_agrees)

def saveFrame (initial : RamState) : List Component :=
  [.reg 4,.mem (stackPtr initial - 8) 8,.mem (stackPtr initial - 16) 8,
    .mem (stackPtr initial - 24) 8,.mem (stackPtr initial - 32) 8,
    .mem (stackPtr initial - 40) 8,.reg 3,.flags,.rip]

theorem save_pre [Bindings] {initial : RamState} {boundary : ReturnBoundary} {key : ByteArray}
    (ctx : Context initial boundary key) : Save.Pre initial := by
  refine ⟨ctx.rip, ?_, ?_⟩
  · intro offset ho
    have bound : offset ≤ 40 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl | rfl <;> decide
    have align : offset % 8 = 0 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl | rfl <;> decide
    exact Hkdf.Proofs.Key.stack_sub_writable8 ctx.toCalleePre (by change offset ≤ 720; omega) align
  · intro offset ho ip len hlo hhi
    have bound : 8 ≤ offset ∧ offset ≤ 40 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl | rfl <;> decide
    have code := stack_codeApart ctx (offset := offset) (len := 8)
      (codeOffset := ip - 0x100000) (codeLen := len) (by omega) bound.1 (by omega)
    have ipEq : Extracted.textAddress + BitVec.ofNat 64 (ip - 0x100000) =
        BitVec.ofNat 64 ip := by
      change BitVec.ofNat 64 0x100000 + _ = _
      rw [← BitVec.ofNat_add]
      exact congrArg (BitVec.ofNat 64) (show 0x100000 + (ip - 0x100000) = ip by omega)
    rw [ipEq] at code
    exact code

theorem save [Bindings] {initial : RamState} {boundary : ReturnBoundary} {key : ByteArray}
    (ctx : Context initial boundary key) :
    ∃ s, State initial boundary s ∧ s.RIP = 0x116333 ∧
      stackPtr s = blockAddress initial ∧ s.regValue .rbx = initial.regValue .rdi ∧
      s.regValue .rsi = initial.regValue .rsi ∧ s.regValue .rdx = initial.regValue .rdx := by
  obtain ⟨fuel,s,run,ready,_,effect⟩ := Save.run boundary (by
    intro ip hlo hhi
    have ipEq : (BitVec.ofNat 64 ip) = Extracted.textAddress +
        BitVec.ofNat 64 (ip - 0x100000) := by
      change _ = BitVec.ofNat 64 0x100000 + _
      rw [← BitVec.ofNat_add]
      exact congrArg (BitVec.ofNat 64) (show ip = 0x100000 + (ip - 0x100000) by omega)
    rw [ipEq]
    exact boundary_ne_program ctx.outerBoundary
      (inProgram_of_textOffset (ip-0x100000) (by omega))) initial
    (supportedMachine_readyToStep ctx.machine)
    (programText_slice (programLoaded_codeIn ctx.loaded) 0x16320 Save.bytes
      (by decide +kernel) (by decide +kernel)) (save_pre ctx)
  have initialRsp : rspOf initial = stackPtr initial := Operand.read_reg64 initial 4
  have frame : AgreesExcept (saveFrame initial) initial s := by
    simpa only [saveFrame, Save.effect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.cons_append, List.nil_append,
      initialRsp, Nat.reduceDiv] using effect.agrees
  have writes : WritesWithin (saveFrame initial) (writeRegions initial) := by
    intro c hc a ha
    simp only [saveFrame, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals refine ⟨Stack.region initial stackBytes, by simp [writeRegions], ?_⟩
    all_goals
      exact Hkdf.Proofs.Common.Machine.stackRegion_contains_sub
        ctx.stack.2.2.1 (by decide) (by decide) ha
  have started : Hkdf.Proofs.Common.CallFrame.Running initial boundary (writeRegions initial) initial :=
    Hkdf.Proofs.Common.CallFrame.Running.initial ctx.machine ctx.loaded ctx.directionFlag
  have running := started.of_agrees run ready frame writes (by
    intro region member address contains inside
    exact ctx.avoids region (by simpa [writeRegions] using member)
      address contains (.inl inside)) (by simp [saveFrame])
  have stores := effect.writes
  simp only [Save.effect, Write.AllHold, initialRsp, Operand.read_reg64] at stores
  have saved : SavedStackAt initial s := by
    constructor
    · intro slot hs
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl
      · exact stores.2.1
      · exact stores.2.2.1
      · exact stores.2.2.2.1
      · exact stores.2.2.2.2.1
      · exact stores.2.2.2.2.2.1
    · apply memLoad_congr
      intro i hi
      change (s.external[_]?).getD 0 = (initial.external[_]?).getD 0
      rw [frame.memory _]
      intro c hc cover
      simp only [saveFrame,List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals try exact cover.elim
      all_goals obtain ⟨j,hj,he⟩ := cover
      · exact OffsetsApart.ne (c₁ := 0) (len₁ := 8) (c₂ := -8) (len₂ := 8)
          (by unfold OffsetsApart; decide +kernel) (stackPtr initial) hi hj (by decide)
          (by
            rw [BitVec.sub_eq_add_neg] at he
            exact (congrArg (fun x : BitVec 64 ↦ x + BitVec.ofNat 64 i)
              (BitVec.add_zero (stackPtr initial))).trans he)
      · exact OffsetsApart.ne (c₁ := 0) (len₁ := 8) (c₂ := -16) (len₂ := 8)
          (by unfold OffsetsApart; decide +kernel) (stackPtr initial) hi hj (by decide)
          (by
            rw [BitVec.sub_eq_add_neg] at he
            exact (congrArg (fun x : BitVec 64 ↦ x + BitVec.ofNat 64 i)
              (BitVec.add_zero (stackPtr initial))).trans he)
      · exact OffsetsApart.ne (c₁ := 0) (len₁ := 8) (c₂ := -24) (len₂ := 8)
          (by unfold OffsetsApart; decide +kernel) (stackPtr initial) hi hj (by decide)
          (by
            rw [BitVec.sub_eq_add_neg] at he
            exact (congrArg (fun x : BitVec 64 ↦ x + BitVec.ofNat 64 i)
              (BitVec.add_zero (stackPtr initial))).trans he)
      · exact OffsetsApart.ne (c₁ := 0) (len₁ := 8) (c₂ := -32) (len₂ := 8)
          (by unfold OffsetsApart; decide +kernel) (stackPtr initial) hi hj (by decide)
          (by
            rw [BitVec.sub_eq_add_neg] at he
            exact (congrArg (fun x : BitVec 64 ↦ x + BitVec.ofNat 64 i)
              (BitVec.add_zero (stackPtr initial))).trans he)
      · exact OffsetsApart.ne (c₁ := 0) (len₁ := 8) (c₂ := -40) (len₂ := 8)
          (by unfold OffsetsApart; decide +kernel) (stackPtr initial) hi hj (by decide)
          (by
            rw [BitVec.sub_eq_add_neg] at he
            exact (congrArg (fun x : BitVec 64 ↦ x + BitVec.ofNat 64 i)
              (BitVec.add_zero (stackPtr initial))).trans he)
  refine ⟨s, ⟨running, saved, frame.read (n := 64) (r := 5) (by simp [saveFrame]),
    frame.mxcsr (by simp [saveFrame]),frame.fcw (by simp [saveFrame])⟩,
    effect.rip,stores.1,stores.2.2.2.2.2.2,
    frame.read (n := 64) (r := 6) (by simp [saveFrame]),
    frame.read (n := 64) (r := 2) (by simp [saveFrame])⟩

end Hkdf.Proofs.Key.Entry
