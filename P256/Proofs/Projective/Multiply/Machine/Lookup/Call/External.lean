import P256.Proofs.Projective.Multiply.Machine.Lookup.Input

set_option autoImplicit false

open P256.Proofs.Program (CalleePre CalleeResult inProgram_of_textOffset)

namespace P256.Proofs.Projective.Multiply.Machine.Lookup

open P256.Proofs.Field (MontgomeryAt)
open P256.Proofs.Program (readyToStep)
open P256.Spec.Program.Routines
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem external_binary_call [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {entry : BitVec 64} {reserve x y : Nat} {op : Nat → Nat → Nat}
    (pre : CalleePre s boundary 0x1044a0 768 96 496) (state : FrameState s t)
    (site : StackCallSite entry 32 reserve)
    (rightOffset : Nat) (rightBound : rightOffset + 32 ≤ 768)
    (routine : ∀ (v : RamState), P256.Proofs.Field.BinaryFieldPre v boundary entry reserve → v.regValue .rcx = t.regValue .rcx →
      MontgomeryAt v (v.regValue .rsi) x → MontgomeryAt v (v.regValue .rdx) y →
      ∃ u, CalleeResult v u boundary 32 reserve ∧ MontgomeryAt u (v.regValue .rdi) (op x y))
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 site.codeOffset)
    (input : t.regValue .rsi = stackPtr s - BitVec.ofNat 64 site.layout.inputOffset)
    (right : t.regValue .rdx = s.regValue .rsi + BitVec.ofNat 64 rightOffset)
    (output : t.regValue .rdi = stackPtr s - BitVec.ofNat 64 site.layout.outputOffset)
    (hx : MontgomeryAt t (stackPtr s - BitVec.ofNat 64 site.layout.inputOffset) x)
    (hy : MontgomeryAt s (s.regValue .rsi + BitVec.ofNat 64 rightOffset) y) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u ∧
      u.RIP = Extracted.textAddress + BitVec.ofNat 64 site.codeOffset + (5 : BitVec 64) ∧
      MontgomeryAt u (stackPtr s - BitVec.ofNat 64 site.layout.outputOffset) (op x y) ∧
      (∀ r ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15], u.regValue r = t.regValue r) ∧
      (∀ offset len : Nat, offset ≤ 360 → len ≤ offset + 8 →
        (offset + 32 ≤ site.layout.outputOffset ∨ site.layout.outputOffset + len ≤ offset) →
        ∀ i < len, u.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
          t.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?) := by
  obtain ⟨v, run, ready, effect⟩ := Program.ScalarFrame.scalar_call pre (by decide) (by decide) state site.codeOffset site.disp
    (Nat.le_of_lt site.codeBound) site.bytes (by rw [site.target]; exact site.entryLow)
    (by rw [site.target]; exact site.entryProgram) rip
  have frame := state.after_call pre (by decide) (by decide) ready effect
  have vin : v.regValue .rsi = stackPtr s - BitVec.ofNat 64 site.layout.inputOffset :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans input
  have vright : v.regValue .rdx = s.regValue .rsi + BitVec.ofNat 64 rightOffset :=
    (effect.agrees.read (n := 64) (r := 2) (by simp)).trans right
  have vout : v.regValue .rdi = stackPtr s - BitVec.ofNat 64 site.layout.outputOffset :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans output
  have ret : (returnBoundary v).rip = Extracted.textAddress + BitVec.ofNat 64 site.codeOffset + (5 : BitVec 64) := (callEffect_stack effect).1
  have cp : P256.Proofs.Field.BinaryFieldPre v boundary entry reserve := by
    apply binary_pre_external pre frame site.layout site.stack rightOffset rightBound
      (effect.rip.trans site.target) vin vright vout
    · rw [ret]
      rw [show Extracted.textAddress + BitVec.ofNat 64 site.codeOffset + (5 : BitVec 64) =
        Extracted.textAddress + BitVec.ofNat 64 (site.codeOffset+5) by
          rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl]
      exact inProgram_of_textOffset _ site.codeBound
  have hleft := site.layout.inputAbove
  rw [site.stack] at hleft
  have hleftEnd := site.layout.inputEnd
  have vx : MontgomeryAt v (v.regValue .rsi) x := by
    rw [vin]
    exact ⟨hx.1, hx.2.1, fun i hi => (Program.ScalarFrame.scalar_call_byte (frameOffset := 360) (by decide) state effect (by omega) hleftEnd hi).trans (hx.2.2 i hi)⟩
  have vy : MontgomeryAt v (v.regValue .rdx) y := by
    rw [vright]
    exact Lookup.FrameState.input_montgomery pre frame rightBound hy
  obtain ⟨u, result, value⟩ := routine v cp (effect.agrees.read (n := 64) (r := 1) (by simp)) vx vy
  have hout := site.layout.outputAbove
  rw [site.stack] at hout
  have capacity := site.layout.capacity
  rw [site.stack] at capacity
  obtain ⟨fuel, run'⟩ := result.execution
  refine ⟨1+fuel, u, run.trans run', Program.FieldCall.after_result (frameOffset := 360) pre frame result (by decide)
    (Program.FieldCall.stack_result_work_frame (frameOffset := 360) pre frame result vout
      (by omega) site.outputSaved (by omega) (by decide)), result.rip.trans ret, vout ▸ value, ?_, ?_⟩
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
    exact (Program.FieldCall.stack_result_byte (frameOffset := 360) pre frame result vout (by decide) (by omega) ho hl apart hi).trans
      (Program.ScalarFrame.scalar_call_byte (frameOffset := 360) (by decide) state effect ho hl hi)

end P256.Proofs.Projective.Multiply.Machine.Lookup
