import P256.Proofs.Program.FieldCall.Memory

set_option autoImplicit false

namespace P256.Proofs.Program.FieldCall

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Field
open X86 X86.Machine X86.UserProcess X86Proofs

variable {outerEntry : BitVec 64} {outerInput outerOutput outerReserve frameOffset : Nat}

variable {inputRegister : Syntax.Reg}

theorem unary_call [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {entry : BitVec 64} {outputBytes reserve x : Nat} {resultAt : RamState → BitVec 64 → Prop}
    (pre : CalleePre s boundary outerEntry outerInput outerOutput outerReserve inputRegister) (state : FrameState s t outerOutput outerReserve (BitVec.ofNat 64 frameOffset))
    (layout : StackCallLayout outerReserve 32 outputBytes reserve) (layoutStack : layout.stackOffset = frameOffset + 8)
    (outputSaved : outputBytes + 48 ≤ layout.outputOffset)
    (codeOffset : Nat) (disp : BitVec 32) (codeBound : codeOffset + 5 < 118431)
    (bytes : Extracted.textBytes.toListFrom codeOffset 5 = encodeCallRel32 disp)
    (target : branchTarget (Extracted.textAddress + BitVec.ofNat 64 codeOffset) 5 (disp.signExtend 64) = entry)
    (entryLow : entry.toNat < 2^32) (entryProgram : InProgram entry)
    (routine : ∀ (v : RamState), CalleePre v boundary entry 32 outputBytes reserve →
      MontgomeryAt v (v.regValue .rsi) x →
      ∃ u, CalleeResult v u boundary outputBytes reserve ∧ resultAt u (v.regValue .rdi))
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOffset)
    (input : t.regValue .rsi = stackPtr s - BitVec.ofNat 64 layout.inputOffset)
    (output : t.regValue .rdi = stackPtr s - BitVec.ofNat 64 layout.outputOffset)
    (hx : MontgomeryAt t (stackPtr s - BitVec.ofNat 64 layout.inputOffset) x)
 :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u outerOutput outerReserve (BitVec.ofNat 64 frameOffset) ∧
      u.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOffset + (5 : BitVec 64) ∧
      resultAt u (stackPtr s - BitVec.ofNat 64 layout.outputOffset) ∧
      (∀ r ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15], u.regValue r = t.regValue r) ∧
      (∀ offset len : Nat, offset ≤ frameOffset → len ≤ offset + 8 →
        (offset + outputBytes ≤ layout.outputOffset ∨ layout.outputOffset + len ≤ offset) →
        ∀ i < len, u.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
          t.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?) ∧
      MemoryWriteFrame t u #v[workRegion s outerReserve] := by
  have capacity := layout.capacity
  have outputAbove := layout.outputAbove
  have aligned := layout.aligned
  rw [layoutStack] at capacity outputAbove aligned
  have saved := outputSaved
  have frameBound : frameOffset + 8 ≤ outerReserve := by omega
  have frameSaved : 48 ≤ frameOffset := by omega
  have frameAligned : (frameOffset + 8) % 8 = 0 := by omega
  have bounds := stack_bounds pre.stack
  obtain ⟨v, run, ready, effect⟩ := scalar_call pre frameBound frameAligned state codeOffset disp
    (Nat.le_of_lt codeBound) bytes (by rw [target]; exact entryLow)
    (by rw [target]; exact entryProgram) rip
  have frame := state.after_call pre frameBound frameSaved ready effect
  have vin : v.regValue .rsi = stackPtr s - BitVec.ofNat 64 layout.inputOffset :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans input
  have vout : v.regValue .rdi = stackPtr s - BitVec.ofNat 64 layout.outputOffset :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans output
  have ret : (returnBoundary v).rip = Extracted.textAddress + BitVec.ofNat 64 codeOffset + (5 : BitVec 64) := (callEffect_stack effect).1
  have cp : CalleePre v boundary entry 32 outputBytes reserve := by
    apply CalleePre.of_stack pre layout
    · exact frame.bindingsSupported
    · exact frame.machine
    · exact frame.directionFlag
    · exact frame.loaded
    · exact frame.allocated
    · exact effect.rip.trans target
    · rw [layoutStack]
      exact frame.rsp
    · exact vin
    · exact vout
    · rw [ret]
      rw [show Extracted.textAddress + BitVec.ofNat 64 codeOffset + (5 : BitVec 64) =
        Extracted.textAddress + BitVec.ofNat 64 (codeOffset+5) by
          rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl]
      exact inProgram_of_textOffset _ codeBound
  have hleft := layout.inputAbove
  rw [layoutStack] at hleft
  have hleftEnd := layout.inputEnd
  have vx : MontgomeryAt v (v.regValue .rsi) x := by
    rw [vin]
    exact ⟨hx.1, hx.2.1, fun i hi => (scalar_call_byte (frameOffset := frameOffset) (by omega) state effect (by omega) hleftEnd hi).trans (hx.2.2 i hi)⟩
  obtain ⟨u, result, value⟩ := routine v cp vx
  have hout := layout.outputAbove
  rw [layoutStack] at hout
  obtain ⟨fuel, run'⟩ := result.execution
  refine ⟨1+fuel, u, run.trans run', after_result pre frame result (by omega)
    (stack_result_work_frame pre frame result vout (by omega) outputSaved (by omega) frameSaved), result.rip.trans ret, vout ▸ value, ?_, ?_, ?_⟩
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
    exact (stack_result_byte pre frame result vout frameBound (by omega) ho hl apart hi).trans
      (scalar_call_byte (frameOffset := frameOffset) (by omega) state effect ho hl hi)

  · exact memoryWriteFrame_trans (field_call_work_frame pre state frameBound frameSaved effect)
      (stack_result_work_frame pre frame result vout (by omega) outputSaved (by omega) frameSaved)


end P256.Proofs.Program.FieldCall
