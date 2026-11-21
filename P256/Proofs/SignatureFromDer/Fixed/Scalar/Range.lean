import P256.Proofs.SignatureFromDer.Fixed.Scalar.Decode
import P256.Proofs.SignatureFromDer.Fixed.Scalar.Status
import P256.Proofs.SignatureFromDer.Fixed.Scalar.Load
import P256.Proofs.SignatureFromDer.Fixed.Scalar.Compare.Run
import P256.Proofs.SignatureFromDer.Fixed.Scalar.RangeState

set_option autoImplicit false

open P256.Proofs.Program (CalleePre programLoaded_codeIn programText_slice readyToStep)

namespace P256.Proofs.SignatureFromDer.Fixed.Scalar

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem scalar_range [Bindings] {s u : RamState} {boundary : ReturnBoundary}
    {input : ByteArray} (pre : CalleePre s boundary 0x10fa20 32 40 288)
    (state : DecodedState s u boundary input) :
    ∃ t, ComparedState s t boundary input := by
  obtain ⟨v, runV, readyV, ripV, agreesV⟩ := scalar_status
    (readyToStep state.machine state.bindingsSupported) state.loaded state.rip state.status pre.outerBoundary
  have stateV := state.toFrameState.after_registers readyV agreesV
    (by simp [Component.Covers]) (by simp)
  have memoryV : v.external = u.external := agreesV.external (by simp [Component.Covers])
  have valueV : P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At v (stackPtr s - 112) (Arith.uint input) := by
    exact ⟨state.value.1, fun i hi => by rw [memoryV]; exact state.value.2 i hi⟩
  have preV : LoadPre v := by
    refine ⟨ripV, ?_⟩
    intro off ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl
    all_goals exact Program.ScalarFrame.stack_readable (frameOffset := 152) pre stateV (by decide) (by decide)
  obtain ⟨m, w, runW, readyW, _, effectW⟩ := scalar_load boundary pre.outerBoundary v readyV
    (programText_slice (programLoaded_codeIn stateV.loaded) 0xfab7 loadBytesCode
      (by decide +kernel) (by decide +kernel)) preV
  have stateW := stateV.after_registers readyW effectW.agrees
    (by simp [loadEffect, Effect.components, Component.Covers])
    (by simp [loadEffect, Effect.components])
  have limb (j : Nat) (hj : j < 4) :
      (Operand.mem (stackPtr v + BitVec.ofNat 64 (40 + 8*j)) : Operand 64).read v =
        BitVec.ofNat 64 (Arith.uint input / 2^(64*j)) := by
    have ha : stackPtr v + BitVec.ofNat 64 (40 + 8*j) =
        stackPtr s - 112 + BitVec.ofNat 64 (8*j) := by
      rw [BitVec.ofNat_add, ← BitVec.add_assoc]
      have hb : stackPtr v + 40#64 = stackPtr s - 112 :=
        Program.ScalarFrame.scalar_stack_address (frameOffset := 152) stateV.rsp (by decide) (offset := 40) (by decide)
      rw [hb]
    rw [ha]
    exact valueV.memLoad_limb j hj
  have w0 : w.regValue .r15 = BitVec.ofNat 64 (Arith.uint input) :=
    effectW.writes.1.trans (by simpa only [Nat.mul_zero, Nat.pow_zero, Nat.div_one,
      Nat.add_zero, BitVec.ofNat_eq_ofNat] using (limb 0 (by decide)))
  have w1 : w.regValue .r12 = BitVec.ofNat 64 (Arith.uint input / 2^64) :=
    effectW.writes.2.1.trans (limb 1 (by decide))
  have w2 : w.regValue .r13 = BitVec.ofNat 64 (Arith.uint input / 2^128) :=
    effectW.writes.2.2.1.trans (limb 2 (by decide))
  have w3 : w.regValue .rbp = BitVec.ofNat 64 (Arith.uint input / 2^192) :=
    effectW.writes.2.2.2.trans (limb 3 (by decide))
  have number : (Compare.compareInput w).toNat = Arith.uint input := by
    change (w.regValue .r15).toNat + 2^64 * ((w.regValue .r12).toNat +
      2^64 * ((w.regValue .r13).toNat + 2^64 * (w.regValue .rbp).toNat)) = _
    rw [w0, w1, w2, w3]
    exact P256.Proofs.SecretKeyFromBytes.Scalar.limbs_ofNat_toNat (Arith.uint input) valueV.1

  have slot : stackPtr w + 8 = stackPtr s - 144 :=
    Program.ScalarFrame.scalar_stack_address (frameOffset := 152) stateW.rsp (by decide) (offset := 8) (by decide)
  have preW : Compare.BorrowSlotPre 0x10facb w := by
    refine ⟨effectW.rip, ?_, ?_⟩
    · rw [slot]
      exact P256.Proofs.Program.writable_of_grow (P256.Proofs.Program.stack_sub_writable8 pre.stack
        (fun a ha hp => pre.avoids (Stack.region s 288) (by simp) a ha (.inr hp))
        (offset := 144) (by decide) (by decide)) stateW.allocated
    · intro a ha hin
      apply pre.avoids (Stack.region s 288) (by simp) a ?_ (.inl hin)
      rw [slot] at ha
      exact Program.ScalarFrame.stack_contains pre (offset := 144) (by decide) (by decide) ha
  obtain ⟨k, t, runT, readyT, _, preT, agreesT, validT⟩ :=
    Compare.compare_correct pre.outerBoundary readyW stateW.loaded preW
  have writesT : WritesWithin (Compare.compareFrame w) #v[registerRegion s .rdi 40, Program.ScalarFrame.workRegion s 288] := by
    intro c hc a hv
    simp only [Compare.compareFrame, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hv.elim
    rw [slot] at hv
    exact ⟨Program.ScalarFrame.workRegion s 288, by simp, Program.ScalarFrame.work_contains pre (offset := 144) (by decide) (by decide) hv⟩
  have stateT := Program.ScalarFrame.FrameState.after_effect (frameOffset := 152) pre (by decide) stateW readyT agreesT writesT (by simp [Compare.compareFrame])
  obtain ⟨n, runU⟩ := state.execution
  refine ⟨t, ⟨stateT, ⟨n + 2 + m + k, ((runU.trans runV).trans runW).trans runT⟩,
    preT.rip, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact (agreesT.read (n := 64) (r := 3) (by simp [Compare.compareFrame])).trans
      ((effectW.agrees.read (n := 64) (r := 3) (by simp [loadEffect, Effect.components])).trans
      ((agreesV.read (n := 64) (r := 3) (by simp)).trans state.output))
  · exact (agreesT.read (n := 64) (r := 14) (by simp [Compare.compareFrame])).trans
      ((effectW.agrees.read (n := 64) (r := 14) (by simp [loadEffect, Effect.components])).trans
      ((agreesV.read (n := 64) (r := 14) (by simp)).trans state.tag))
  · simpa only [number] using validT
  · exact (agreesT.read (n := 64) (r := 15) (by simp [Compare.compareFrame])).trans w0
  · exact (agreesT.read (n := 64) (r := 12) (by simp [Compare.compareFrame])).trans w1
  · exact (agreesT.read (n := 64) (r := 13) (by simp [Compare.compareFrame])).trans w2
  · exact (agreesT.read (n := 64) (r := 5) (by simp [Compare.compareFrame])).trans w3

end P256.Proofs.SignatureFromDer.Fixed.Scalar
