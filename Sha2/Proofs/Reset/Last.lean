import Sha2.Proofs.Reset.Second
import Sha2.Proofs.Reset.Return
import Sha2.Proofs.Reset.Absorb
import Sha2.Proofs.Reset.NormalizeState
import Sha2.Proofs.Reset.Serialize
import Sha2.Proofs.Common.SHA256.Absorb.TraversalProof.Geometry
import Sha2.Proofs.Common.SHA256.Finalize.Proof.Geometry

set_option autoImplicit false

namespace Sha2.Proofs.Reset.Last

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.SHA256
open Sha2.Proofs.Common.SHA256.Absorb Sha2.Proofs.Common.SHA256.Instances
open Sha2.Proofs.Common.SHA256.Instances.Absorption

private theorem table_below (v : Wrapper.Variant) {initial : RamState}
    (stack : Stack.Valid initial 720) :
    ∀ region ∈ Table.footprint (resetSecond v) ((resetSecond v).chunk.sp initial),
      ∀ a, region.Contains a → a < (stackPtr initial).toNat - 80 := by
  intro region member a ha
  change region ∈ #v[⟨(stackPtr initial - 248#64 + 0#64).toNat,104⟩,
    ⟨(stackPtr initial - 248#64 + 0#64).toNat,104⟩,
    ⟨(stackPtr initial - 248#64 - 344#64).toNat,344⟩] at member
  simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at member
  have bounds := stack_valid_bounds stack
  rcases member with rfl | rfl | rfl
  all_goals change _ ≤ a ∧ a < _ at ha
  all_goals dsimp only at ha
  · rw [BitVec.add_zero, stack_valid_sub_toNat stack (by decide)] at ha
    omega
  · rw [BitVec.add_zero, stack_valid_sub_toNat stack (by decide)] at ha
    omega
  · have eq : stackPtr initial - 248#64 - 344#64 = stackPtr initial - 592#64 := by
      rw [BitVec.sub_sub]; rfl
    rw [eq, stack_valid_sub_toNat stack (by decide)] at ha
    omega

private theorem finalize_below (v : Wrapper.Variant) {initial : RamState}
    (stack : Stack.Valid initial 720) :
    ∀ region ∈ Finalize.footprint (Finalization.resetLast.layout v)
      ((Finalization.resetLast.layout v).sp initial),
      ∀ a, region.Contains a → a < (stackPtr initial).toNat - 80 := by
  intro region member a ha
  change region ∈ #v[⟨(stackPtr initial - 248#64 + 0#64).toNat,64⟩,
    ⟨(stackPtr initial - 248#64 + 0#64 + 64#64).toNat,32⟩,
    ⟨(stackPtr initial - 248#64 + 104#64).toNat,64⟩,
    ⟨(stackPtr initial - 248#64 - 344#64).toNat,344⟩] at member
  simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at member
  have bounds := stack_valid_bounds stack
  rcases member with rfl | rfl | rfl | rfl
  all_goals change _ ≤ a ∧ a < _ at ha
  all_goals dsimp only at ha
  · rw [BitVec.add_zero, stack_valid_sub_toNat stack (by decide)] at ha
    omega
  · rw [BitVec.add_zero, stack_frame_toNat stack (by decide) (by decide)] at ha
    omega
  · rw [stack_frame_toNat stack (by decide) (by decide)] at ha
    omega
  · have eq : stackPtr initial - 248#64 - 344#64 = stackPtr initial - 592#64 := by
      rw [BitVec.sub_sub]; rfl
    rw [eq, stack_valid_sub_toNat stack (by decide)] at ha
    omega

theorem frame_preserves_output {initial s t : RamState} {n : Nat}
    {written : Vector MemoryRegion n} {routine : Routine} {inputs : Array Input} {first : ByteArray}
    (call : TwoOutputs.ValidCall routine initial inputs)
    (frame : MemoryWriteFrame s t written)
    (within : ∀ region ∈ written, ∀ a, region.Contains a →
      (Stack.region initial routine.minStackBytes).Contains a)
    (bytes : (TwoOutputs.outputRegion routine initial).HasBytes s.external first) :
    (TwoOutputs.outputRegion routine initial).HasBytes t.external first := by
  apply Common.Memory.hasBytes_of_frame bytes (call.outputInMemory _ (by simp)).2.1 frame
  intro region member address contains covered
  have pairs := call.separation.1
  simp only [List.pairwise_cons] at pairs
  exact pairs.1 (Stack.region initial routine.minStackBytes) (by simp) address contains
    (within region member address covered)

theorem frame_preserves {initial s t : RamState} {n cutoff : Nat}
    {written : Vector MemoryRegion n} {routine : Routine} {inputs : Array Input} {first : ByteArray}
    (call : TwoOutputs.ValidCall routine initial inputs)
    (frame : MemoryWriteFrame s t written)
    (within : ∀ region ∈ written, ∀ a, region.Contains a →
      (Stack.region initial routine.minStackBytes).Contains a)
    (below : ∀ region ∈ written, ∀ a, region.Contains a → a < (stackPtr initial).toNat - cutoff)
    (bytes : (TwoOutputs.outputRegion routine initial).HasBytes s.external first) :
    (TwoOutputs.outputRegion routine initial).HasBytes t.external first ∧
    (∀ a : BitVec 64, (stackPtr initial).toNat - cutoff ≤ a.toNat →
      t.external[a]? = s.external[a]?) := by
  refine ⟨frame_preserves_output call frame within bytes, ?_⟩
  intro a ha
  apply frame
  intro region member contains
  have := below region member a.toNat contains
  omega

theorem high_word {initial s t : RamState} {reserve depth cutoff : Nat}
    (stack : Stack.Valid initial reserve) (capacity : depth ≤ reserve)
    (same : ∀ a : BitVec 64, (stackPtr initial).toNat - cutoff ≤ a.toNat →
      t.external[a]? = s.external[a]?)
    (offset : Nat) (lower : depth ≤ cutoff + offset) (upper : offset ≤ depth) :
    memLoad t.external (stackPtr initial - BitVec.ofNat 64 depth + BitVec.ofNat 64 offset) 64 =
      memLoad s.external (stackPtr initial - BitVec.ofNat 64 depth + BitVec.ofNat 64 offset) 64 := by
  apply memLoad_congr
  intro i hi
  change (t.external[_]?).getD 0 = (s.external[_]?).getD 0
  rw [same]
  have bounds := stack_valid_bounds stack
  rw [BitVec.toNat_add, stack_frame_toNat stack capacity upper, BitVec.toNat_ofNat]
  omega

theorem output_word {initial s t : RamState} {routine : Routine} {inputs : Array Input}
    {output : MemoryRegion}
    (call : TwoOutputs.ValidCall routine initial inputs)
    (member : output ∈ [TwoOutputs.outputRegion routine initial,
      TwoOutputs.secondOutputRegion routine initial])
    (frame : MemoryWriteFrame s t #v[output])
    {depth : Nat} (capacity : depth ≤ routine.minStackBytes)
    (offset : Nat) (upper : offset ≤ depth) :
    memLoad t.external (stackPtr initial - BitVec.ofNat 64 depth + BitVec.ofNat 64 offset) 64 =
      memLoad s.external (stackPtr initial - BitVec.ofNat 64 depth + BitVec.ofNat 64 offset) 64 := by
  have stack := call.stack
  have bounds := stack_valid_bounds stack
  apply memLoad_congr
  intro i hi
  change (t.external[_]?).getD 0 = (s.external[_]?).getD 0
  rw [frame]
  intro region written contains
  simp only [Vector.mem_mk, List.mem_toArray, List.mem_singleton] at written
  subst region
  have address : (stackPtr initial - BitVec.ofNat 64 depth +
      BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat =
      (stackPtr initial).toNat - depth + offset + i := by
    rw [BitVec.toNat_add, stack_frame_toNat stack capacity upper, BitVec.toNat_ofNat]
    omega
  have stackContains : (Stack.region initial routine.minStackBytes).Contains
      (stackPtr initial - BitVec.ofNat 64 depth + BitVec.ofNat 64 offset +
        BitVec.ofNat 64 i).toNat := by
    rw [address]
    change (stackPtr initial).toNat - routine.minStackBytes ≤ _ ∧
      _ < (stackPtr initial).toNat - routine.minStackBytes +
        ((stackPtr initial).toNat + 8 - ((stackPtr initial).toNat - routine.minStackBytes))
    omega
  have pairs := call.separation.1
  simp only [List.pairwise_cons] at pairs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact pairs.1 _ (by simp) _ contains stackContains
  · exact pairs.2.1 _ (by simp) _ contains stackContains

theorem finalized_second [bindings : Bindings] (v : Wrapper.Variant)
    {initial s : RamState} {inputs : Array Input} {first : ByteArray}
    (stride : UnitStringStride bindings) (machine : SupportedMachine bindings initial)
    (call : TwoOutputs.ValidCall (resetRoutine v) initial inputs)
    (blocks : Absorb.BlockContracts (resetSecond v).chunk (returnBoundary initial))
    (state : ExecutionState initial s (regions (resetRoutine v) initial))
    (firstBytes : (TwoOutputs.outputRegion (resetRoutine v) initial).HasBytes s.external first)
    (branch : (Table.LoopState (resetSecond v) ((resetSecond v).chunk.sp initial) inputs 0 s ∧
        Table.InputData (resetSecond v) ((resetSecond v).chunk.sp initial) inputs s ∧
        Table.Separation (resetSecond v) initial s 720 inputs) ∨
       (inputs.size = 0 ∧ Finalize.Prepared (Finalization.resetLast.layout v)
         ((Finalization.resetLast.layout v).sp initial) ByteArray.empty s)) :
    ∃ n t, Finalize.Finalized (Finalization.resetLast.layout v) initial n t
      (regions (resetRoutine v) initial) (message inputs) ∧
      (TwoOutputs.outputRegion (resetRoutine v) initial).HasBytes t.external first ∧
      (∀ a : BitVec 64, (stackPtr initial).toNat - 80 ≤ a.toNat → t.external[a]? = s.external[a]?) := by
  have stack : Stack.Valid initial 720 := by simpa only [resetRoutine_stack] using call.stack
  have finalizeWithin := Finalize.footprint_subset_stack
    (Finalization.resetLast.wellFormed (v := v)) stack
  rcases branch with ⟨loop, data, separation⟩ | ⟨empty, prepared⟩
  · have avoid : (Stack.region initial 720).Avoids (fun a => InProgram a ∨ InPageTables a) := by
      simpa only [resetRoutine_stack, InPageTables] using
        (call.separation.2 _ (by simp [resetRoutine_stack])).2
    have count : Table.CountAt (resetSecond v) ((resetSecond v).chunk.sp initial) s := by
      constructor; intro offset impossible; cases impossible
    have within : ∀ region ∈ Table.footprint (resetSecond v) ((resetSecond v).chunk.sp initial),
        ∀ a, region.Contains a → ∃ outer ∈ regions (resetRoutine v) initial, outer.Contains a := by
      intro region member address inside
      refine ⟨Stack.region initial 720, by simp [regions, resetRoutine_stack], ?_⟩
      exact Table.footprint_subset_stack (resetSecond_wellFormed v) stack region member address inside
    obtain ⟨u, finished⟩ := Table.correct (resetSecond v)
      (resetSecond_wellFormed v) (resetSecond_flow v) (resetSecond_chunkCodeFacts v)
      (resetSecond_callTargets v) blocks (Absorb.correct _) (resetSecond_tableCodeFacts v)
      (resetSecond_tableBlocks v _ stride
        (valid_return_boundary machine stack call.returnAddress).2.2)
      stride machine stack avoid call.returnAddress state loop count data separation within
    obtain ⟨firstU, sameU⟩ := frame_preserves call finished.memory
      (by simpa only [resetRoutine_stack] using
        Table.footprint_subset_stack (resetSecond_wellFormed v) stack)
      (table_below v stack) firstBytes
    have rspU : rspOf u = stackPtr initial - 248#64 := finished.rsp
    have hashU : HasherAt u (rspOf u) (message inputs) v.initialHash := by
      rw [rspU]
      have h := finished.hasher
      change HasherAt u (stackPtr initial - 248#64 + 0#64) (message inputs) v.initialHash at h
      simpa only [BitVec.add_zero] using h
    have ripU : u.RIP = Normalize.entry false v := by
      rw [finished.rip]; cases v <;> rfl
    obtain ⟨n, t, _, effect, _, finalized⟩ :=
      normalized_finalized v false (form := .reset) stride machine call
        finished.state rspU ripU hashU
    have noMem : ∀ c ∈ (Normalize.effect (Normalize.entry false v) false u).components,
        ∀ a, ¬ c.Covers a := by
      simp [Normalize.effect, Effect.components, Component.Covers]
    have memN := effect.agrees.external noMem
    obtain ⟨firstT, sameT⟩ := frame_preserves call finalized.frame.memory
      (by simpa only [resetRoutine_stack, Finalization.reserve, Normalize.finalization] using finalizeWithin)
      (finalize_below v stack) (by rw [memN]; exact firstU)
    exact ⟨n, t, finalized, firstT, fun a ha => (sameT a ha).trans
      (by rw [memN]; exact sameU a ha)⟩
  · have emptyInputs : inputs = #[] := Array.eq_empty_iff_size_eq_zero.mpr empty
    have msg : message inputs = ByteArray.empty := by simp [emptyInputs, message]
    obtain ⟨t, result⟩ := finalized (message := message inputs) v .resetLast (by rw [resetRoutine_stack]; rfl)
      stride machine call state (by rw [msg]; exact prepared)
    obtain ⟨firstT, sameT⟩ := frame_preserves call result.frame.memory
      (by simpa only [resetRoutine_stack, Finalization.reserve, Normalize.finalization] using finalizeWithin)
      (finalize_below v stack) firstBytes
    exact ⟨s, t, result, firstT, sameT⟩

theorem completed [bindings : Bindings] (v : Wrapper.Variant)
    {initial s : RamState} {inputs : Array Input}
    (stride : UnitStringStride bindings) (machine : SupportedMachine bindings initial)
    (call : TwoOutputs.ValidCall (resetRoutine v) initial inputs)
    (blocks : Absorb.BlockContracts (resetSecond v).chunk (returnBoundary initial))
    (state : ExecutionState initial s (regions (resetRoutine v) initial))
    (rsp : rspOf s = stackPtr initial - 248#64)
    (rip : s.RIP = Second.entry v)
    (hasher : HasherAt s (rspOf s) ByteArray.empty v.initialHash)
    (count : s.regValue .r12 = BitVec.ofNat 64 inputs.size)
    (pointer : memLoad s.external (rspOf s + 168#64) 64 = initial.regValue .rdi)
    (length : memLoad s.external (rspOf s + 176#64) 64 = initial.regValue .rdx)
    (secondOutput : memLoad s.external (rspOf s + 192#64) 64 = initial.regValue .r8)
    (firstBytes : (TwoOutputs.outputRegion (resetRoutine v) initial).HasBytes s.external
      (v.hash (message inputs)))
    (saved : ∀ (r : BitVec 5) (offset : Nat),
      (r, offset) ∈ [(3,0),(12,8),(13,16),(14,24),(15,32)] →
      memLoad s.external (rspOf s + BitVec.ofNat 64 (200 + offset)) 64 =
        (Operand.reg r : Operand 64).read initial)
    (savedRbp : memLoad s.external (rspOf s + 240#64) 64 = (Operand.reg 5 : Operand 64).read initial)
    (returnWord : memLoad s.external (stackPtr initial) 64 = (returnBoundary initial).rip) :
    ∃ fuel final, UniqueExecution initial fuel final ∧ SupportedMachine bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧ DirectionFlagUnset final ∧
      MemoryWriteFrame initial final (regions (resetRoutine v) initial) ∧
      (TwoOutputs.outputRegion (resetRoutine v) initial).HasBytes final.external (v.hash (message inputs)) ∧
      (TwoOutputs.secondOutputRegion (resetRoutine v) initial).HasBytes final.external (v.hash (message inputs)) := by
  have stack : Stack.Valid initial 720 := by simpa only [resetRoutine_stack] using call.stack
  obtain ⟨q, stateQ, firstQ, memQ, branch⟩ := Second.dispatched v machine call state rsp rip
    hasher count pointer length firstBytes
  obtain ⟨n, c, finalC, firstC, sameC⟩ := finalized_second v stride machine call blocks stateQ firstQ branch
  have same : ∀ a : BitVec 64, (stackPtr initial).toNat - 80 ≤ a.toNat →
      c.external[a]? = s.external[a]? := by
    intro a ha
    rw [sameC a ha, memQ]
  have rspC : rspOf c = stackPtr initial - 248#64 := finalC.rsp
  have secondC : memLoad c.external (rspOf c + 192#64) 64 = initial.regValue .r8 := by
    rw [rspC, high_word stack (by decide) same 192 (by decide) (by decide), ← rsp]
    exact secondOutput
  obtain ⟨hash, wordsC, equal⟩ := finalC.digest
  have words : HashStateAt c (rspOf c + 64#64) hash := by
    rw [rspC]
    change HashStateAt c (stackPtr initial - 248#64 + 0#64 + 64#64) hash at wordsC
    simpa only [BitVec.add_zero] using wordsC
  have hashEqual : (if v == .sha224 then (serializeHash hash).extract 0 28 else serializeHash hash) =
      v.hash (message inputs) := by cases v <;> exact equal
  obtain ⟨w, stateW, ripW, firstW, secondW, rspW, frameW⟩ := serialized_last v machine call
    finalC.state rspC finalC.rip words secondC firstC
  have rspFinal : rspOf w = stackPtr initial - 248#64 := rspW.trans rspC
  have slot (offset : Nat) (lower : 168 ≤ offset) (upper : offset ≤ 248) :
      memLoad w.external (rspOf w + BitVec.ofNat 64 offset) 64 =
        memLoad s.external (rspOf s + BitVec.ofNat 64 offset) 64 := by
    rw [rspFinal, output_word call (by simp) frameW (by cases v <;> decide) offset upper,
      high_word stack (by decide) same offset (by omega) upper, ← rsp]
  have savedW : ∀ (r : BitVec 5) (offset : Nat),
      (r, offset) ∈ [(3,0),(12,8),(13,16),(14,24),(15,32)] →
      memLoad w.external (rspOf w + BitVec.ofNat 64 (200 + offset)) 64 =
        (Operand.reg r : Operand 64).read initial := by
    intro r offset member
    have bound : offset ≤ 32 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
      rcases member with h | h | h | h | h <;> omega
    rw [slot (200+offset) (by omega) (by omega)]
    exact saved r offset member
  have rbpW : memLoad w.external (rspOf w + 240#64) 64 = (Operand.reg 5 : Operand 64).read initial :=
    (slot 240 (by decide) (by decide)).trans savedRbp
  have returnW : memLoad w.external (stackPtr initial) 64 = (returnBoundary initial).rip := by
    have h := slot 248 (by decide) (by decide)
    rw [rspFinal, rsp, BitVec.sub_add_cancel] at h
    exact h.trans returnWord
  have entryW : w.RIP = resetReturnPC v := by
    rw [ripW]
    cases v <;> decide +kernel
  obtain ⟨fuel, final, execution, machineFinal, abi, df, frame, memory⟩ := Reset.returned v
    machine call stateW rspFinal entryW savedW rbpW returnW
  refine ⟨fuel, final, execution, machineFinal, abi, df, frame, ?_, ?_⟩
  · rw [memory]; exact firstW
  · rw [memory]; exact hashEqual ▸ secondW

end Sha2.Proofs.Reset.Last
