import P256.Proofs.Verifying.Message.Hash.Serialize.Payload
import P256.Proofs.Verifying.Message.Hash.Serialize.Frame
import P256.Proofs.Verifying.Message.Hash.Finalize.Interface
import P256.Proofs.Verifying.Message.Hash.Interface

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Hash.Serialize

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem pre [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} (input : Message.Pre initial boundary message)
    (state : Finalize.Result initial s boundary message) : Pre s := by
  refine ⟨state.rip, ?_, ?_, ?_⟩
  · intro i hi
    have bound : i.toNat + 4 ≤ 1176 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, rspOf, stackPtr, Operand.read_reg64] using
      ScalarFrame.stack_readable input.toCalleePre state.toFrameState
        (offset := i.toNat) (by decide) bound
  · intro i hi
    have bound : i.toNat + 4 ≤ 1176 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, rspOf, stackPtr, Operand.read_reg64] using
      ScalarFrame.stack_writable input.toCalleePre state.toFrameState
        (offset := i.toNat) (by decide) bound (by decide)
  · intro i hi offset len hcode
    have bound : i.toNat + 4 ≤ 1176 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, rspOf, stackPtr, Operand.read_reg64] using
      ScalarFrame.stack_code input.toCalleePre state.toFrameState
        (offset := i.toNat) (by decide) bound hcode

theorem correct [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} (input : Message.Pre initial boundary message)
    (state : Finalize.Result initial s boundary message) :
    ∃ t, Hash.Result initial t boundary message := by
  obtain ⟨fuel, t, execution, ready, _, result⟩ := run boundary input.outerBoundary s
    (readyToStep state.machine state.bindingsSupported) (code state.loaded) (pre input state)
  have address : rspOf s + 424 = stackPtr initial - 752 := by
    exact ScalarFrame.scalar_stack_address state.rsp (by decide) (by decide)
  have bounds := stack_bounds input.stack
  have destination : (rspOf s + 424).toNat = (stackPtr initial).toNat - 752 := by
    rw [address]
    exact stack_sub_toNat input.stack (by decide)
  have writes : WritesWithin (effect s).components
      #v[ScalarFrame.Work.region initial 9992 720] := by
    apply writesWithin
    · change (stackPtr initial).toNat - 9992 + (9992 - 720) < 2^32
      omega
    · rw [destination]
      change (stackPtr initial).toNat - 9992 ≤ (stackPtr initial).toNat - 752
      omega
    · rw [destination]
      change (stackPtr initial).toNat - 752 + 32 ≤
        (stackPtr initial).toNat - 9992 + (9992 - 720)
      omega
  have memory := result.agrees.memoryWriteFrame writes
  have wide : WritesWithin (effect s).components
      #v[ScalarFrame.workRegion initial 9992] := by
    intro c hc a covered
    obtain ⟨region, member, inside⟩ := writes c hc a covered
    have eq : region = ScalarFrame.Work.region initial 9992 720 := by simpa using member
    subst region
    refine ⟨ScalarFrame.workRegion initial 9992, by simp, ?_⟩
    change (stackPtr initial).toNat - 9992 ≤ a.toNat ∧
      a.toNat < (stackPtr initial).toNat - 9992 + (9992 - 720) at inside
    change (stackPtr initial).toNat - 9992 ≤ a.toNat ∧
      a.toNat < (stackPtr initial).toNat - 9992 + (9992 - 48)
    constructor <;> omega
  have frame := state.toFrameState.after_effect input.toCalleePre (by decide) ready
    result.agrees (by
      intro c hc a covered
      obtain ⟨region, member, inside⟩ := wide c hc a covered
      exact ⟨region, by simpa using Or.inr member, inside⟩)
    (by simp [effect, Effect.components, Write.component, Operand.component])
    (by simp [effect, Effect.components, Write.component, Operand.component])
    (by simp [effect, Effect.components, Write.component, Operand.component])
    (by simp [effect, Effect.components, Write.component, Operand.component])
  have saved (offset : Nat) (apart : offset + 8 ≤ 424 ∨ 456 ≤ offset)
      (upper : offset ≤ 1176) :
      memLoad t.external (frameBase initial + BitVec.ofNat 64 offset) 64 =
        memLoad s.external (frameBase initial + BitVec.ofNat 64 offset) 64 := by
    apply memLoad_congr
    intro i hi
    change (t.external[_]?).getD 0 = (s.external[_]?).getD 0
    rw [result.agrees.byte]
    intro c hc covered
    simp only [effect, Effect.components, Write.component, Operand.component,
      List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.append_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact covered.elim
    all_goals
      obtain ⟨j, hj, eq⟩ := covered
      have sp : rspOf s = frameBase initial := state.rsp
      rw [sp, BitVec.add_assoc, BitVec.add_assoc] at eq
      have en := congrArg BitVec.toNat ((BitVec.add_right_inj (frameBase initial)).mp eq)
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat] at en
      omega
  refine ⟨t, {
    toFrameState := frame
    execution := ?_
    rip := result.rip
    digest := ?_
    savedKey := (saved 456 (by decide) (by decide)).trans state.savedKey
    savedOutput := (saved 384 (by decide) (by decide)).trans state.savedOutput
    savedSignature := (saved 464 (by decide) (by decide)).trans state.savedSignature
    stackFrame := memoryWriteFrame_trans state.stackFrame
      (work_frame_stack input.toCalleePre (result.agrees.memoryWriteFrame wide))
  }⟩
  · obtain ⟨before, runBefore⟩ := state.execution
    exact ⟨before + fuel, runBefore.trans execution⟩
  · obtain ⟨hash, hashAt, digest⟩ := state.hash
    have sp : rspOf s = frameBase initial := state.rsp
    rw [← sp] at hashAt
    have bytes := payload (pre input state) hashAt result
    simpa only [sp, digest] using bytes

end P256.Proofs.Verifying.Message.Hash.Serialize
