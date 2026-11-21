import P256.Proofs.Signing.Core.Iteration.Memory
import P256.Proofs.Program.FieldCall.Binary

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Components

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame FieldCall Field

theorem binary_nat_call [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {x y reserve : Nat} {entry : BitVec 64} {op : Nat → Nat → Nat}
    (pre : SignPre s boundary) (state : Frame s t)
    (site : BinaryCallSite 4584 2280 entry reserve)
    (routine : ∀ v, BinaryFieldPre v boundary entry reserve →
      SecretKeyFromBytes.Scalar.Nat256At v (v.regValue .rsi) x →
      SecretKeyFromBytes.Scalar.Nat256At v (v.regValue .rdx) y →
      ∃ u, CalleeResult v u boundary 32 reserve ∧
        SecretKeyFromBytes.Scalar.Nat256At u (v.regValue .rdi) (op x y))
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 site.codeOffset)
    (input : t.regValue .rsi = stackPtr s - BitVec.ofNat 64 site.layout.inputOffset)
    (right : t.regValue .rdx = stackPtr s - BitVec.ofNat 64 site.rightOffset)
    (output : t.regValue .rdi = stackPtr s - BitVec.ofNat 64 site.layout.outputOffset)
    (hx : SecretKeyFromBytes.Scalar.Nat256At t (stackPtr s - BitVec.ofNat 64 site.layout.inputOffset) x)
    (hy : SecretKeyFromBytes.Scalar.Nat256At t (stackPtr s - BitVec.ofNat 64 site.rightOffset) y) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧
      u.RIP = Extracted.textAddress + BitVec.ofNat 64 site.codeOffset + (5 : BitVec 64) ∧
      SecretKeyFromBytes.Scalar.Nat256At u (stackPtr s - BitVec.ofNat 64 site.layout.outputOffset) (op x y) ∧
      (∀ r ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15], u.regValue r = t.regValue r) ∧
      (∀ offset len : Nat, offset ≤ 2280 → len ≤ offset + 8 →
        (offset + 32 ≤ site.layout.outputOffset ∨ site.layout.outputOffset + len ≤ offset) →
        ∀ i < len, u.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
          t.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?) ∧
      MemoryWriteFrame t u #v[workRegion s 4584] := by
  have capacity := site.layout.capacity
  have outputAbove := site.layout.outputAbove
  have aligned := site.layout.aligned
  rw [site.stack] at capacity outputAbove aligned
  have saved := site.outputSaved
  have frameBound : 2280 + 8 ≤ 4584 := by omega
  have frameSaved : 48 ≤ 2280 := by omega
  have frameAligned : (2280 + 8) % 8 = 0 := by omega
  have bounds := stack_bounds pre.stack
  obtain ⟨v, run, ready, effect⟩ := scalar_call pre.toCalleePre frameBound frameAligned (NextNonce.scalarFrame state) site.codeOffset site.disp
    (Nat.le_of_lt site.codeBound) site.bytes (by rw [site.target]; exact site.entryLow)
    (by rw [site.target]; exact site.entryProgram) rip
  have frame := (NextNonce.scalarFrame state).after_call pre.toCalleePre frameBound frameSaved ready effect
  have vin : v.regValue .rsi = stackPtr s - BitVec.ofNat 64 site.layout.inputOffset :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans input
  have vright : v.regValue .rdx = stackPtr s - BitVec.ofNat 64 site.rightOffset :=
    (effect.agrees.read (n := 64) (r := 2) (by simp)).trans right
  have vout : v.regValue .rdi = stackPtr s - BitVec.ofNat 64 site.layout.outputOffset :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans output
  have ret : (returnBoundary v).rip = Extracted.textAddress + BitVec.ofNat 64 site.codeOffset + (5 : BitVec 64) := (callEffect_stack effect).1
  have cp : BinaryFieldPre v boundary entry reserve := by
    apply BinaryFieldPre.of_stack pre.toCalleePre site.layout site.rightOffset
    · simpa only [site.stack] using site.rightAbove
    · exact site.rightEnd
    · exact site.rightApart
    · exact frame.bindingsSupported
    · exact frame.machine
    · exact frame.directionFlag
    · exact frame.loaded
    · exact frame.allocated
    · exact effect.rip.trans site.target
    · rw [site.stack]
      exact frame.rsp
    · exact vin
    · exact vright
    · exact vout
    · rw [ret]
      rw [show Extracted.textAddress + BitVec.ofNat 64 site.codeOffset + (5 : BitVec 64) =
        Extracted.textAddress + BitVec.ofNat 64 (site.codeOffset+5) by
          rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl]
      exact inProgram_of_textOffset _ site.codeBound
  have hleft := site.layout.inputAbove
  rw [site.stack] at hleft
  have hleftEnd := site.layout.inputEnd
  have vx : SecretKeyFromBytes.Scalar.Nat256At v (v.regValue .rsi) x := by
    rw [vin]
    exact ⟨hx.1, fun i hi => (scalar_call_byte (frameOffset := 2280) (by omega) (NextNonce.scalarFrame state) effect (by omega) hleftEnd hi).trans (hx.2 i hi)⟩
  have vy : SecretKeyFromBytes.Scalar.Nat256At v (v.regValue .rdx) y := by
    rw [vright]
    exact ⟨hy.1, fun i hi => (scalar_call_byte (frameOffset := 2280) (by omega) (NextNonce.scalarFrame state) effect (by have := site.rightAbove; omega)
      site.rightEnd hi).trans (hy.2 i hi)⟩
  obtain ⟨u, result, value⟩ := routine v cp vx vy
  have hout := site.layout.outputAbove
  rw [site.stack] at hout
  obtain ⟨fuel, run'⟩ := result.execution
  refine ⟨1+fuel, u, run.trans run', NextNonce.coreFrame (after_result pre.toCalleePre frame result (by omega)
    (stack_result_work_frame pre.toCalleePre frame result vout (by omega) site.outputSaved (by omega) frameSaved)), result.rip.trans ret, vout ▸ value, ?_, ?_, ?_⟩
  · intro r hr
    apply (result.calleeSaved r hr).trans
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact effect.agrees.read (n := 64) (r := 3) (by simp)
    · exact effect.agrees.read (n := 64) (r := 5) (by simp)
    · exact effect.agrees.read (n := 64) (r := 12) (by simp)
    · exact effect.agrees.read (n := 64) (r := 13) (by simp)
    · exact effect.agrees.read (n := 64) (r := 14) (by simp)
    · exact effect.agrees.read (n := 64) (r := 15) (by simp)
  · intro offset len ho hl apart i hi
    exact (stack_result_byte pre.toCalleePre frame result vout frameBound (by omega) ho hl apart hi).trans
      (scalar_call_byte (frameOffset := 2280) (by omega) (NextNonce.scalarFrame state) effect ho hl hi)

  · exact memoryWriteFrame_trans (field_call_work_frame pre.toCalleePre (NextNonce.scalarFrame state) frameBound frameSaved effect)
      (stack_result_work_frame pre.toCalleePre frame result vout (by omega) site.outputSaved (by omega) frameSaved)

end P256.Proofs.Signing.Core.Iteration.Components
