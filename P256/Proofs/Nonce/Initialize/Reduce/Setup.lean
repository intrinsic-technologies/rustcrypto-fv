import P256.Proofs.Nonce.Initialize.Reduce.Blocks.Trace
import P256.Proofs.Nonce.Initialize.Reduce.Interface
import P256.Proofs.Common.Lift.Lemma.Read

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Reduce

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar

private theorem trace_copied {s t : RamState} (effect : (Blocks.traceEffect s).Holds s t)
    {offset count : Nat} (low : 168 ≤ offset) (bound : offset + count ≤ 232) :
    ∀ i < count, t.external[stackPtr s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      s.external[stackPtr s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  intro i hi
  apply effect.agrees.memory
  intro c hc ha
  simp only [Blocks.traceEffect, Effect.components, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, Write.component_reg, Write.component_mem,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ha.elim | skip
  · obtain ⟨j, hj, he⟩ := ha
    apply RangeApart.offsets (stackPtr s) (a := 8) (len := 8) (b := offset) (count := count)
      (by decide) (by omega) (by omega) j hj i hi
    exact he.symm
  · obtain ⟨j, hj, he⟩ := ha
    apply RangeApart.offsets (stackPtr s) (a := 16) (len := 8) (b := offset) (count := count)
      (by decide) (by omega) (by omega) j hj i hi
    exact he.symm
  · obtain ⟨j, hj, he⟩ := ha
    apply RangeApart.offsets (stackPtr s) (a := 24) (len := 8) (b := offset) (count := count)
      (by decide) (by omega) (by omega) j hj i hi
    exact he.symm
  · obtain ⟨j, hj, he⟩ := ha
    apply RangeApart.offsets (stackPtr s) (a := 32) (len := 8) (b := offset) (count := count)
      (by decide) (by omega) (by omega) j hj i hi
    exact he.symm
  · obtain ⟨j, hj, he⟩ := ha
    apply RangeApart.offsets (stackPtr s) (a := 72) (len := 8) (b := offset) (count := count)
      (by decide) (by omega) (by omega) j hj i hi
    exact he.symm
  · obtain ⟨j, hj, he⟩ := ha
    apply RangeApart.offsets (stackPtr s) (a := 96) (len := 8) (b := offset) (count := count)
      (by decide) (by omega) (by omega) j hj i hi
    exact he.symm
  · obtain ⟨j, hj, he⟩ := ha
    apply RangeApart.offsets (stackPtr s) (a := 104) (len := 8) (b := offset) (count := count)
      (by decide) (by omega) (by omega) j hj i hi
    exact he.symm
  · obtain ⟨j, hj, he⟩ := ha
    apply RangeApart.offsets (stackPtr s) (a := 112) (len := 8) (b := offset) (count := count)
      (by decide) (by omega) (by omega) j hj i hi
    exact he.symm
  · obtain ⟨j, hj, he⟩ := ha
    apply RangeApart.offsets (stackPtr s) (a := 120) (len := 8) (b := offset) (count := count)
      (by decide) (by omega) (by omega) j hj i hi
    exact he.symm
  · obtain ⟨j, hj, he⟩ := ha
    apply RangeApart.offsets (stackPtr s) (a := 128) (len := 8) (b := offset) (count := count)
      (by decide) (by omega) (by omega) j hj i hi
    exact he.symm
  · obtain ⟨j, hj, he⟩ := ha
    apply RangeApart.offsets (stackPtr s) (a := 160) (len := 8) (b := offset) (count := count)
      (by decide) (by omega) (by omega) j hj i hi
    exact he.symm

set_option maxHeartbeats 800000 in

theorem setup [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} {digest : ByteArray}
    (pre : InitializePre initial boundary orderAddress)
    (prepared : Shift.ReducedInput initial s boundary digest) (rip : s.RIP = 0x10799e) :
    ∃ t, SelectionReady initial t boundary (Field.readLimbs s (stackPtr s + 8)).toNat
      (subtractOrder (Field.readLimbs s (stackPtr s + 8))).1.toNat
      (decide ((subtractOrder (Field.readLimbs s (stackPtr s + 8))).2 ≠ 0)) := by
  obtain ⟨t, stage, effect⟩ := Blocks.trace_run pre prepared.stage rip
  let a := Field.readLimbs s (stackPtr s + 8)
  have o0 : (Operand.reg 15 : Operand 64).read s = 0xf3b9cac2fc632551 := prepared.order0
  have o1 : (Operand.reg 14 : Operand 64).read s = 0xbce6faada7179e84 := prepared.order1
  have o2 : (Operand.reg 13 : Operand 64).read s = 0xffffffffffffffff := prepared.order2
  have o3 : (Operand.reg 3 : Operand 64).read s = 0xffffffff00000000 := prepared.order3
  simp only [BitVec.ofNat_eq_ofNat] at o0 o1 o2 o3
  have sp : stackPtr t = stackPtr s := by rw [stage.rsp, prepared.stage.rsp]
  have word {offset : Nat} (low : 168 ≤ offset) (bound : offset + 8 ≤ 232) :
      memLoad t.external (stackPtr t + BitVec.ofNat 64 offset) 64 =
        memLoad s.external (stackPtr s + BitVec.ofNat 64 offset) 64 := by
    rw [sp]
    apply memLoad_congr
    intro i hi
    exact congrArg (fun x : Option UInt8 => x.getD 0) (trace_copied effect low bound i hi)
  have difference : Field.readLimbs t (stackPtr t + 8) = (subtractOrder a).1 := by
    dsimp only [Field.readLimbs, subtractOrder]
    congr 1
    · have h := effect.writes.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      simpa only [P256.Proofs.Lift.Operand.read_mem_external, Blocks.traceEffect, o0, o1, o2, o3,
        Field.readLimbs, sp, a, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using h
    · have h := effect.writes.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      simpa only [P256.Proofs.Lift.Operand.read_mem_external, Blocks.traceEffect, o0, o1, o2, o3,
        Field.readLimbs, sp, a, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using h
    · have h := effect.writes.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      simpa only [P256.Proofs.Lift.Operand.read_mem_external, Blocks.traceEffect, o0, o1, o2, o3,
        Field.readLimbs, sp, a, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using h
    · have h := effect.writes.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      simpa only [P256.Proofs.Lift.Operand.read_mem_external, Blocks.traceEffect, o0, o1, o2, o3,
        Field.readLimbs, sp, a, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using h
  have original : Field.readLimbs t (stackPtr t + 104) = a := by
    dsimp only [Field.readLimbs, a]
    congr 1
    · have h := effect.writes.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      simpa only [P256.Proofs.Lift.Operand.read_mem_external, Blocks.traceEffect, sp, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using h
    · have h := effect.writes.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      simpa only [P256.Proofs.Lift.Operand.read_mem_external, Blocks.traceEffect, sp, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using h
    · have h := effect.writes.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      simpa only [P256.Proofs.Lift.Operand.read_mem_external, Blocks.traceEffect, sp, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using h
    · have h := effect.writes.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      simpa only [P256.Proofs.Lift.Operand.read_mem_external, Blocks.traceEffect, sp, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using h
  refine ⟨t, {
    stage := stage
    rip := effect.rip
    secret := (word (offset := 184) (by decide) (by decide)).trans prepared.secret
    output := (word (offset := 192) (by decide) (by decide)).trans prepared.output
    length := (word (offset := 176) (by decide) (by decide)).trans prepared.length
    entropy := (word (offset := 168) (by decide) (by decide)).trans prepared.entropy
    outputPointer := effect.writes.2.2.2.2.2.2.2.2.2.2.2.2.2.1.trans prepared.output
    buffer := by
      have h : t.regValue .rbp = stackPtr s + 8 := effect.writes.2.2.2.2.1
      simpa only [sp] using h
    destination := by
      have h : t.regValue .rdi = stackPtr s + 8 := effect.writes.2.2.2.2.2.2.1
      simpa only [sp] using h
    source := by
      have h : t.regValue .rdx = stackPtr s + 104 := effect.writes.2.2.1
      simpa only [sp] using h
    leftCount := effect.writes.2.2.2.2.2.1
    rightCount := effect.writes.2.1
    choice := ?_
    difference := ?_
    original := ?_
  }⟩
  · have h := effect.writes.2.2.2.2.2.2.2.1
    change (Operand.reg 8 : Operand 64).read t = _
    rw [← subtractOrder_choice a]
    simpa only [P256.Proofs.Lift.Operand.read_mem_external, Blocks.traceEffect, o0, o1, o2, o3,
      subtractOrder, a, Field.readLimbs, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using h
  · rw [← difference]
    exact Field.nat256At_readLimbs (ScalarFrame.stack_readable pre.toCalleePre stage.toFrameState
      (offset := 8) (len := 32) (by decide) (by decide)).mem
  · change Nat256At t (stackPtr t + 104) a.toNat
    rw [← original]
    exact Field.nat256At_readLimbs (ScalarFrame.stack_readable pre.toCalleePre stage.toFrameState
      (offset := 104) (len := 32) (by decide) (by decide)).mem

end P256.Proofs.Nonce.Initialize.Reduce
