import P256.Proofs.Nonce.Initialize.Reduce.Blocks.Compose

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Reduce.Blocks

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Field.FieldNeg.Instructions (or_r64_r64_effect_step)
open P256.Proofs.Common.Field.Instructions (sub_r64_m64_effect_step)
open P256.Proofs.Common.Instructions (sar_r64_imm8_effect_step)
open P256.Proofs.Common.Instructions.MovzxByte
open P256.Proofs.Common.Instructions.ByteOps.ByteOps

attribute [local x86_compose] andAlImm8Effect

def traceEffect (s : RamState) : Effect :=
  let sp := stackPtr s
  let a0 := (Operand.mem (sp + 8) : Operand 64).read s
  let a1 := (Operand.mem (sp + 16) : Operand 64).read s
  let a2 := (Operand.mem (sp + 24) : Operand 64).read s
  let a3 := (Operand.mem (sp + 32) : Operand 64).read s
  let o0 := (Operand.reg 15 : Operand 64).read s
  let o1 := (Operand.reg 14 : Operand 64).read s
  let o2 := (Operand.reg 13 : Operand 64).read s
  let o3 := (Operand.reg 3 : Operand 64).read s
  let r0 := a0 - o0
  let q0 := borrowWord a0 o0 r0
  let r1 := (-q0).sshiftRight 63 + (a1 - o1)
  let q1 := borrowWord a1 o1 r1
  let r2 := (-q1).sshiftRight 63 + (a2 - o2)
  let q2 := borrowWord a2 o2 r2
  let r3 := (-q2).sshiftRight 63 + (a3 - o3)
  let q3 := borrowWord a3 o3 r3
  let byte := q3.setWidth 8
  { rip := 0x107b57
    writes := [
      ⟨(.reg 0 : Operand 64), mergeGPR 8 (byte &&& 1) (byte.setWidth 64)⟩,
      ⟨(.reg 1 : Operand 64), 4⟩,
      ⟨(.reg 2 : Operand 64), sp + 104⟩,
      ⟨(.reg 3 : Operand 64), r0⟩,
      ⟨(.reg 5 : Operand 64), sp + 8⟩,
      ⟨(.reg 6 : Operand 64), 4⟩,
      ⟨(.reg 7 : Operand 64), sp + 8⟩,
      ⟨(.reg 8 : Operand 64), (byte &&& 1).setWidth 64⟩,
      ⟨(.reg 9 : Operand 64), ~~~a2 ||| o2⟩,
      ⟨(.reg 10 : Operand 64), r1⟩,
      ⟨(.reg 11 : Operand 64), a2 - o2⟩,
      ⟨(.reg 12 : Operand 64), r2⟩,
      ⟨(.reg 13 : Operand 64), a3 - o3⟩,
      ⟨(.reg 14 : Operand 64), (Operand.mem (sp + 192) : Operand 64).read s⟩,
      ⟨(.reg 15 : Operand 64), ~~~a3 ||| o3⟩,
      ⟨(.mem (sp + 8) : Operand 64), r0⟩,
      ⟨(.mem (sp + 16) : Operand 64), r1⟩,
      ⟨(.mem (sp + 24) : Operand 64), r2⟩,
      ⟨(.mem (sp + 32) : Operand 64), r3⟩,
      ⟨(.mem (sp + 72) : Operand 64), q3⟩,
      ⟨(.mem (sp + 96) : Operand 64), a3⟩,
      ⟨(.mem (sp + 104) : Operand 64), a0⟩,
      ⟨(.mem (sp + 112) : Operand 64), a1⟩,
      ⟨(.mem (sp + 120) : Operand 64), a2⟩,
      ⟨(.mem (sp + 128) : Operand 64), a3⟩,
      ⟨(.mem (sp + 160) : Operand 64), r0⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

set_option maxHeartbeats 2000000 in
theorem trace_run [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} (pre : InitializePre initial boundary orderAddress)
    (stage : Stage initial s boundary) (rip : s.RIP = 0x10799e) :
    ∃ t, Stage initial t boundary ∧ (traceEffect s).Holds s t := by
  have readSP (v : RamState) : stackPtr v = (Operand.reg 4 : Operand 64).read v := rfl
  obtain ⟨n0, t0, run0, ready0, _, effect0⟩ := copy_run boundary pre.outerBoundary s
    (readyToStep stage.machine stage.bindingsSupported)
    (programText_slice (programLoaded_codeIn stage.loaded) 0x799e copyBytes
      (by decide) (by decide +kernel)) (block_pre pre stage rip)
  have stage0 := Stage.of_local pre stage run0 ready0 effect0.agrees (copy_writes s)
    (by simp [copyEffect, Effect.components]) (by simp [copyEffect, Effect.components])
    (by simp [copyEffect, Effect.components]) (by simp [copyEffect, Effect.components])
  obtain ⟨n1, t1, run1, ready1, _, effect1⟩ := low_run boundary pre.outerBoundary t0
    (readyToStep stage0.machine stage0.bindingsSupported)
    (programText_slice (programLoaded_codeIn stage0.loaded) 0x79d3 lowBytes
      (by decide) (by decide +kernel)) (block_pre pre stage0 effect0.rip)
  have stage1 := Stage.of_local pre stage0 run1 ready1 effect1.agrees (low_writes t0)
    (by simp [lowEffect, Effect.components]) (by simp [lowEffect, Effect.components])
    (by simp [lowEffect, Effect.components]) (by simp [lowEffect, Effect.components])
  have combined1 := effect0.seq (e₁ := copyEffect) low_local (copy_local.full s) effect1
  obtain ⟨n2, t2, run2, ready2, _, effect2⟩ := second_run boundary pre.outerBoundary t1
    (readyToStep stage1.machine stage1.bindingsSupported)
    (programText_slice (programLoaded_codeIn stage1.loaded) 0x7a09 secondBytes
      (by decide) (by decide +kernel)) (block_pre pre stage1 effect1.rip)
  have stage2 := Stage.of_local pre stage1 run2 ready2 effect2.agrees (second_writes t1)
    (by simp [secondEffect, Effect.components]) (by simp [secondEffect, Effect.components])
    (by simp [secondEffect, Effect.components]) (by simp [secondEffect, Effect.components])
  have combined2 := combined1.seq (e₁ := (Effect.seq copyEffect lowEffect)) second_local ((copy_local.seq low_local).full s) effect2
  obtain ⟨n3, t3, run3, ready3, _, effect3⟩ := third_run boundary pre.outerBoundary t2
    (readyToStep stage2.machine stage2.bindingsSupported)
    (programText_slice (programLoaded_codeIn stage2.loaded) 0x7a41 thirdBytes
      (by decide) (by decide +kernel)) (block_pre pre stage2 effect2.rip)
  have stage3 := Stage.of_local pre stage2 run3 ready3 effect3.agrees (third_writes t2)
    (by simp [thirdEffect, Effect.components]) (by simp [thirdEffect, Effect.components])
    (by simp [thirdEffect, Effect.components]) (by simp [thirdEffect, Effect.components])
  have combined3 := combined2.seq (e₁ := (Effect.seq (Effect.seq copyEffect lowEffect) secondEffect)) third_local (((copy_local.seq low_local).seq second_local).full s) effect3
  obtain ⟨n4, t4, run4, ready4, _, effect4⟩ := high_run boundary pre.outerBoundary t3
    (readyToStep stage3.machine stage3.bindingsSupported)
    (programText_slice (programLoaded_codeIn stage3.loaded) 0x7a71 highBytes
      (by decide) (by decide +kernel)) (block_pre pre stage3 effect3.rip)
  have stage4 := Stage.of_local pre stage3 run4 ready4 effect4.agrees (high_writes t3)
    (by simp [highEffect, Effect.components]) (by simp [highEffect, Effect.components])
    (by simp [highEffect, Effect.components]) (by simp [highEffect, Effect.components])
  have combined4 := combined3.seq (e₁ := (Effect.seq (Effect.seq (Effect.seq copyEffect lowEffect) secondEffect) thirdEffect)) high_local ((((copy_local.seq low_local).seq second_local).seq third_local).full s) effect4
  obtain ⟨n5, t5, run5, ready5, _, effect5⟩ := store_run boundary pre.outerBoundary t4
    (readyToStep stage4.machine stage4.bindingsSupported)
    (programText_slice (programLoaded_codeIn stage4.loaded) 0x7ab8 storeBytes
      (by decide) (by decide +kernel)) (block_pre pre stage4 effect4.rip)
  have stage5 := Stage.of_local pre stage4 run5 ready5 effect5.agrees (store_writes t4)
    (by simp [storeEffect, Effect.components]) (by simp [storeEffect, Effect.components])
    (by simp [storeEffect, Effect.components]) (by simp [storeEffect, Effect.components])
  have combined5 := combined4.seq (e₁ := (Effect.seq (Effect.seq (Effect.seq (Effect.seq copyEffect lowEffect) secondEffect) thirdEffect) highEffect)) store_local (((((copy_local.seq low_local).seq second_local).seq third_local).seq high_local).full s) effect5
  obtain ⟨n6, t6, run6, ready6, _, effect6⟩ := choiceMiddle_run boundary pre.outerBoundary t5
    (readyToStep stage5.machine stage5.bindingsSupported)
    (programText_slice (programLoaded_codeIn stage5.loaded) 0x7ade choiceMiddleBytes
      (by decide) (by decide +kernel)) (block_pre pre stage5 effect5.rip)
  have stage6 := Stage.of_local pre stage5 run6 ready6 effect6.agrees (choiceMiddle_writes t5)
    (by simp [choiceMiddleEffect, Effect.components]) (by simp [choiceMiddleEffect, Effect.components])
    (by simp [choiceMiddleEffect, Effect.components]) (by simp [choiceMiddleEffect, Effect.components])
  have combined6 := combined5.seq (e₁ := (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq copyEffect lowEffect) secondEffect) thirdEffect) highEffect) storeEffect)) choiceMiddle_local ((((((copy_local.seq low_local).seq second_local).seq third_local).seq high_local).seq store_local).full s) effect6
  obtain ⟨n7, t7, run7, ready7, _, effect7⟩ := choiceHigh_run boundary pre.outerBoundary t6
    (readyToStep stage6.machine stage6.bindingsSupported)
    (programText_slice (programLoaded_codeIn stage6.loaded) 0x7b18 choiceHighBytes
      (by decide) (by decide +kernel)) (block_pre pre stage6 effect6.rip)
  have stage7 := Stage.of_local pre stage6 run7 ready7 effect7.agrees (choiceHigh_writes t6)
    (by simp [choiceHighEffect, Effect.components]) (by simp [choiceHighEffect, Effect.components])
    (by simp [choiceHighEffect, Effect.components]) (by simp [choiceHighEffect, Effect.components])
  have combined7 := combined6.seq (e₁ := (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq copyEffect lowEffect) secondEffect) thirdEffect) highEffect) storeEffect) choiceMiddleEffect)) choiceHigh_local (((((((copy_local.seq low_local).seq second_local).seq third_local).seq high_local).seq store_local).seq choiceMiddle_local).full s) effect7
  obtain ⟨n8, t8, run8, ready8, _, effect8⟩ := arguments_run boundary pre.outerBoundary t7
    (readyToStep stage7.machine stage7.bindingsSupported)
    (programText_slice (programLoaded_codeIn stage7.loaded) 0x7b35 argumentsBytes
      (by decide) (by decide +kernel)) (block_pre pre stage7 effect7.rip)
  have stage8 := Stage.of_local pre stage7 run8 ready8 effect8.agrees (arguments_writes t7)
    (by simp [argumentsEffect, Effect.components]) (by simp [argumentsEffect, Effect.components])
    (by simp [argumentsEffect, Effect.components]) (by simp [argumentsEffect, Effect.components])
  have combined8 := combined7.seq (e₁ := (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq copyEffect lowEffect) secondEffect) thirdEffect) highEffect) storeEffect) choiceMiddleEffect) choiceHighEffect)) arguments_local ((((((((copy_local.seq low_local).seq second_local).seq third_local).seq high_local).seq store_local).seq choiceMiddle_local).seq choiceHigh_local).full s) effect8
  refine ⟨t8, stage8, ?_⟩
  x86_norm [copyEffect, lowEffect, secondEffect, thirdEffect, highEffect, storeEffect, choiceMiddleEffect, choiceHighEffect, argumentsEffect, readSP, BitVec.zero_sub, Bool.or_eq_false_iff] at combined8
  apply combined8.weaken
  · rfl
  · x86_norm [traceEffect, borrowWord, readSP, mergeGPR_low8,
      BitVec.and_comm, BitVec.or_comm, BitVec.zero_sub]
    all_goals simp [Operand.read_reg64]
  · intro i
    cases i <;> x86_norm [traceEffect]
  · x86_norm [traceEffect, readSP]

end P256.Proofs.Nonce.Initialize.Reduce.Blocks
