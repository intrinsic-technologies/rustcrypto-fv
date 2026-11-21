import P256.Proofs.Sec1.Affine.Uncompressed.Curve.Equality.Correct
import P256.Proofs.Program.FieldCall.Unary
import P256.Proofs.Sec1.Affine.Uncompressed.Interface

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Curve.Equality

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Program.FieldCall
open P256.Proofs.Field X86 X86.Machine X86.UserProcess X86Proofs

def compareLayout : StackCallLayout 3360 32 32 32 :=
  ⟨768, 480, 184, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

set_option maxRecDepth 16384 in
theorem compare_call [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} {x y : Nat} (pre : AffineDecodePre s boundary bytes)
    (state : Frame s t) (rip : t.RIP = 0x110be0)
    (input : t.regValue .rsi = stackPtr s-480)
    (output : t.regValue .rdi = stackPtr s-184)
    (hx : MontgomeryAt t (stackPtr s-480) x)
    (hy : MontgomeryAt t (stackPtr s-184) y) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x110be5 ∧
      (u.regValue .rax).setWidth 8 = (if y=x then 1 else 0) ∧
      (∀ r ∈ [Syntax.Reg.rbx,.rbp,.r12,.r13,.r14,.r15], u.regValue r = t.regValue r) ∧
      (∀ offset len : Nat, offset ≤ 760 → len ≤ offset+8 →
        (offset+32 ≤ 184 ∨ 184+len ≤ offset) → ∀ i < len,
        u.external[stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? =
          t.external[stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]?) ∧
      MemoryWriteFrame t u #v[workRegion s 3360] := by
  let codeOffset : Nat := 0x10be0
  let disp : BitVec 32 := 0x380b
  have codeBound : codeOffset+5 < 118431 := by decide
  have codeBytes : Extracted.textBytes.toListFrom codeOffset 5 = encodeCallRel32 disp := by decide +kernel
  have target : branchTarget (Extracted.textAddress+BitVec.ofNat 64 codeOffset) 5 (disp.signExtend 64) = 0x1143f0 := by decide +kernel
  have entryLow : (0x1143f0#64).toNat < 2^32 := by decide
  have entryProgram : InProgram 0x1143f0 := inProgram_of_textOffset 0x143f0 (by decide)
  have pre := pre.toCalleePre
  let layout := compareLayout
  have layoutStack : layout.stackOffset = 768 := rfl
  have outputSaved : 80 ≤ layout.outputOffset := by decide
  have capacity := layout.capacity
  have outputAbove := layout.outputAbove
  have aligned := layout.aligned
  rw [layoutStack] at capacity outputAbove aligned
  have saved := outputSaved
  have frameBound : 760 + 8 ≤ 3360 := by omega
  have frameSaved : 48 ≤ 760 := by omega
  have frameAligned : (760 + 8) % 8 = 0 := by omega
  have bounds := stack_bounds pre.stack
  obtain ⟨v, run, ready, effect⟩ := scalar_call pre frameBound frameAligned state codeOffset disp
    (Nat.le_of_lt codeBound) codeBytes (by rw [target]; exact entryLow)
    (by rw [target]; exact entryProgram) rip
  have frame := state.after_call pre frameBound frameSaved ready effect
  have vin : v.regValue .rsi = stackPtr s - BitVec.ofNat 64 layout.inputOffset :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans input
  have vout : v.regValue .rdi = stackPtr s - BitVec.ofNat 64 layout.outputOffset :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans output
  have ret : (returnBoundary v).rip = Extracted.textAddress + BitVec.ofNat 64 codeOffset + (5 : BitVec 64) := (callEffect_stack effect).1
  have cp : CalleePre v boundary 0x1143f0 32 32 32 := by
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
    exact ⟨hx.1, hx.2.1, fun i hi => (scalar_call_byte (frameOffset := 760) (by omega) state effect (by omega) hleftEnd hi).trans (hx.2.2 i hi)⟩
  have vy : MontgomeryAt v (v.regValue .rdi) y := by
    rw [vout]
    exact ⟨hy.1, hy.2.1, fun i hi =>
      (scalar_call_byte (frameOffset := 760) (by decide) state effect (by decide)
        (by decide) hi).trans (hy.2.2 i hi)⟩
  obtain ⟨u, result, value⟩ := field_equal_correct cp vy vx
  have hout := layout.outputAbove
  rw [layoutStack] at hout
  obtain ⟨fuel, run'⟩ := result.execution
  refine ⟨1+fuel, u, run.trans run', after_result pre frame result (by omega)
    (stack_result_work_frame pre frame result vout (by omega) outputSaved (by omega) frameSaved), result.rip.trans ret, value, ?_, ?_, ?_⟩
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
      (scalar_call_byte (frameOffset := 760) (by omega) state effect ho hl hi)

  · exact memoryWriteFrame_trans (field_call_work_frame pre state frameBound frameSaved effect)
      (stack_result_work_frame pre frame result vout (by omega) outputSaved (by omega) frameSaved)

end P256.Proofs.Sec1.Affine.Uncompressed.Curve.Equality
