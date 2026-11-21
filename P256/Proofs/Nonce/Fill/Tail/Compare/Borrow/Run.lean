import P256.Proofs.Nonce.Fill.Tail.Compare.Blocks.Low
import P256.Proofs.Nonce.Fill.Tail.Compare.Blocks.Second
import P256.Proofs.Nonce.Fill.Tail.Compare.Blocks.Third
import P256.Proofs.Nonce.Fill.Tail.Compare.Blocks.High
import P256.Proofs.Nonce.Fill.Tail.Compare.Borrow.Frame
import P256.Proofs.Nonce.Fill.Tail.Compare.Borrow.Arithmetic
import P256.Proofs.Common.Instructions.ByteLogic.Unary
import P256.Proofs.Common.Instructions.ByteOps.Effects

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill.Tail.Compare.Borrow

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Signing.Search
open P256.Proofs.SecretKeyFromBytes.Scalar (Limbs)
open Blocks
open Nonce.Initialize.Reduce (borrowWord)
open P256.Proofs.Common.Instructions.ByteLogic
open P256.Proofs.Common.Instructions.ByteOps.ByteOps (mergeGPR_low8)

set_option maxHeartbeats 800000 in
open Classical in
theorem run [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} {original state : Nonce.State}
    (pre : Fill.Pre initial boundary orderAddress original)
    (input : Compared initial s orderAddress state) (rip : s.RIP = 0x1075e5)
    (zero : (s.regValue .rax).setWidth 8 = if (nextCandidate state).1 = 0 then 1 else 0) :
    ∃ fuel t, Advances boundary fuel s t ∧ Compared initial t orderAddress state ∧
      t.RIP = 0x1076b2 ∧
      (t.regValue .rax).setWidth 8 = ~~~(if (nextCandidate state).1 = 0 then 1 else 0) ∧
      memLoad t.external (stackPtr t + 8) 64 =
        if (nextCandidate state).1 < P256.Spec.Operations.domain.n then 1 else 0 := by
  obtain ⟨n0, t0, run0, ready0, _, effect0⟩ := low_run boundary pre.outerBoundary s
    (readyToStep input.machine input.bindingsSupported)
    (programText_slice (programLoaded_codeIn input.loaded) 0x75e5 lowBytes
      (by decide) (by decide +kernel))
    (Blocks.block_pre pre input.toContext rip)
  have frame0 : AgreesExcept (blockFrame s) s t0 := by
    simpa [lowEffect, Effect.components, blockFrame] using effect0.agrees
  have input0 := after_block pre input ready0 frame0
  obtain ⟨u, runNot, readyU, effectNot⟩ := (not_al_effect_step 0x107615).advances ready0
    (programText_slice (programLoaded_codeIn input0.loaded) 0x7615 _
      (by decide) (by decide +kernel)) effect0.rip
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7617 (by decide)))
  have frameNot : AgreesExcept [.reg 0, .rip] t0 u := effectNot.agrees
  have inputU := input0.after_registers readyU frameNot
    (by simp [Component.Covers]) (by simp) (by simp) (by simp)
  obtain ⟨n1, t1, run1, ready1, _, effect1⟩ := second_run boundary pre.outerBoundary u readyU
    (programText_slice (programLoaded_codeIn inputU.loaded) 0x7617 secondBytes
      (by decide) (by decide +kernel))
    (Blocks.block_pre pre inputU.toContext effectNot.rip)
  have frame1 : AgreesExcept (blockFrame u) u t1 := by
    simpa [secondEffect, Effect.components, blockFrame] using effect1.agrees
  have input1 := after_block pre inputU ready1 frame1
  obtain ⟨n2, t2, run2, ready2, _, effect2⟩ := third_run boundary pre.outerBoundary t1 ready1
    (programText_slice (programLoaded_codeIn input1.loaded) 0x764c thirdBytes
      (by decide) (by decide +kernel))
    (Blocks.block_pre pre input1.toContext effect1.rip)
  have frame2 : AgreesExcept (blockFrame t1) t1 t2 := by
    simpa [thirdEffect, Effect.components, blockFrame] using effect2.agrees
  have input2 := after_block pre input1 ready2 frame2
  obtain ⟨n3, t3, run3, ready3, _, effect3⟩ := high_run boundary pre.outerBoundary t2 ready2
    (programText_slice (programLoaded_codeIn input2.loaded) 0x7684 highBytes
      (by decide) (by decide +kernel))
    (Blocks.block_pre pre input2.toContext effect2.rip)
  have frame3 : AgreesExcept (blockFrame t2) t2 t3 := by
    simpa [highEffect, Effect.components, blockFrame] using effect3.agrees
  have input3 := after_block pre input2 ready3 frame3
  have nonzero : (t3.regValue .rax).setWidth 8 =
      ~~~(if (nextCandidate state).1 = 0 then 1 else 0) := by
    have notValue := congrArg (BitVec.setWidth 8) effectNot.writes
    change (u.regValue .rax).setWidth 8 =
      (mergeGPR 8 (~~~(t0.regValue .rax).setWidth 8) (t0.regValue .rax)).setWidth 8 at notValue
    have al0 : (t0.regValue .rax).setWidth 8 = (s.regValue .rax).setWidth 8 :=
      frame0.read (n := 8) (r := 0) (by simp [blockFrame])
    rw [mergeGPR_low8, al0, zero] at notValue
    exact ((frame1.trans frame2 |>.trans frame3).read (n := 8) (r := 0)
      (by simp [blockFrame])).trans notValue
  let a := P256.Proofs.Field.readLimbs s (frameBase initial + 72)
  have l0 : memLoad s.external (stackPtr s + 72) 64 = a.l0 := by
    rw [input.rsp]
    rfl
  have l1 : memLoad u.external (stackPtr u + 80) 64 = a.l1 := by
    have h : memLoad u.external (stackPtr u + 80) 64 =
        memLoad s.external (stackPtr s + 80) 64 := left_eq input inputU 1 (by decide)
    rw [h, input.rsp]
    change memLoad s.external (frameBase initial + 80) 64 =
      memLoad s.external (frameBase initial + 72 + 8) 64
    rw [BitVec.add_assoc]
    rfl
  have l2 : memLoad t1.external (stackPtr t1 + 88) 64 = a.l2 := by
    have h : memLoad t1.external (stackPtr t1 + 88) 64 =
        memLoad s.external (stackPtr s + 88) 64 := left_eq input input1 2 (by decide)
    rw [h, input.rsp]
    change memLoad s.external (frameBase initial + 88) 64 =
      memLoad s.external (frameBase initial + 72 + 16) 64
    rw [BitVec.add_assoc]
    rfl
  have l3 : memLoad t2.external (stackPtr t2 + 96) 64 = a.l3 := by
    have h : memLoad t2.external (stackPtr t2 + 96) 64 =
        memLoad s.external (stackPtr s + 96) 64 := left_eq input input2 3 (by decide)
    rw [h, input.rsp]
    change memLoad s.external (frameBase initial + 96) 64 =
      memLoad s.external (frameBase initial + 72 + 24) 64
    rw [BitVec.add_assoc]
    rfl
  have o0 : memLoad s.external (s.regValue .r15 + 0) 64 = 0xf3b9cac2fc632551 :=
    order_eq input 0 (by decide)
  have o1 : memLoad u.external (u.regValue .r15 + 8) 64 = 0xbce6faada7179e84 :=
    order_eq inputU 1 (by decide)
  have o2 : memLoad t1.external (t1.regValue .r15 + 16) 64 = 0xffffffffffffffff :=
    order_eq input1 2 (by decide)
  have o3 : memLoad t2.external (t2.regValue .r15 + 24) 64 = 0xffffffff00000000 :=
    order_eq input2 3 (by decide)
  let q0 := borrowWord a.l0 0xf3b9cac2fc632551 (a.l0 - 0xf3b9cac2fc632551)
  let q1 := borrowWord a.l1 0xbce6faada7179e84 ((-q0).sshiftRight 63 + a.l1 - 0xbce6faada7179e84)
  let q2 := borrowWord a.l2 0xffffffffffffffff ((-q1).sshiftRight 63 + a.l2 - 0xffffffffffffffff)
  have c0 : u.regValue .rcx = -q0 := by
    have reg : u.regValue .rcx = t0.regValue .rcx := frameNot.read (n := 64) (r := 1) (by simp)
    rw [reg]
    have h : t0.regValue .rcx = -borrowWord
        (memLoad s.external (stackPtr s + 72) 64)
        (memLoad s.external (s.regValue .r15 + 0) 64)
        (memLoad s.external (stackPtr s + 72) 64 - memLoad s.external (s.regValue .r15 + 0) 64) := by
      have hw := effect0.writes.1
      simp only [borrowWord_form] at hw
      change _ = (0#64 - _) at hw
      rw [BitVec.zero_sub] at hw
      exact hw
    rw [l0, o0] at h
    exact h
  have c1 : t1.regValue .rcx = -q1 := by
    have h : t1.regValue .rcx = -borrowWord
        (memLoad u.external (stackPtr u + 80) 64)
        (memLoad u.external (u.regValue .r15 + 8) 64)
        ((u.regValue .rcx).sshiftRight 63 + memLoad u.external (stackPtr u + 80) 64 -
          memLoad u.external (u.regValue .r15 + 8) 64) := by
      have hw := effect1.writes.1
      simp only [borrowWord_form] at hw
      change _ = (0#64 - _) at hw
      rw [BitVec.zero_sub] at hw
      exact hw
    rw [l1, o1, c0] at h
    exact h
  have c2 : t2.regValue .rdx = -q2 := by
    have h : t2.regValue .rdx = -borrowWord
        (memLoad t1.external (stackPtr t1 + 88) 64)
        (memLoad t1.external (t1.regValue .r15 + 16) 64)
        ((t1.regValue .rcx).sshiftRight 63 + memLoad t1.external (stackPtr t1 + 88) 64 -
          memLoad t1.external (t1.regValue .r15 + 16) 64) := by
      have hw := effect2.writes.2.1
      simp only [borrowWord_form] at hw
      change _ = (0#64 - _) at hw
      rw [BitVec.zero_sub] at hw
      exact hw
    rw [l2, o2, c1] at h
    exact h
  have finalBorrow : memLoad t3.external (stackPtr t3 + 8) 64 = borrowChain a := by
    have h : memLoad t3.external (stackPtr t2 + 8) 64 = borrowWord
        (memLoad t2.external (stackPtr t2 + 96) 64)
        (memLoad t2.external (t2.regValue .r15 + 24) 64)
        ((t2.regValue .rdx).sshiftRight 63 + memLoad t2.external (stackPtr t2 + 96) 64 -
          memLoad t2.external (t2.regValue .r15 + 24) 64) := by
      have hw := effect3.writes.2.2.2.2
      simp only [borrowWord_form] at hw
      exact hw
    rw [l3, o3, c2, input2.rsp, ← input3.rsp] at h
    exact h
  rw [borrowChain_eq, show a.toNat = (nextCandidate state).1 from P256.Proofs.Field.readLimbs_toNat input.integer] at finalBorrow
  exact ⟨n0+1+n1+n2+n3, t3, (((run0.trans runNot).trans run1).trans run2).trans run3,
    input3, effect3.rip, nonzero, finalBorrow⟩

end P256.Proofs.Nonce.Fill.Tail.Compare.Borrow
