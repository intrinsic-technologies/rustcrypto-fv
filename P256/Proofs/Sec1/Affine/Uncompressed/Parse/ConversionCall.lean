import P256.Proofs.Sec1.Affine.State
import P256.Proofs.Program.FieldCall.Memory
import P256.Proofs.Sec1.Decompress.Convert

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Parse

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Field
open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program.FieldCall
open P256.Proofs.SecretKeyFromBytes.Scalar

theorem conversion_call [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {x : Nat} {bytes : ByteArray}
    (pre : AffineDecodePre s boundary bytes) (state : Frame s t)
    (codeOffset : Nat) (disp : BitVec 32) (codeBound : codeOffset + 5 < 118431)
    (bytes : Extracted.textBytes.toListFrom codeOffset 5 = encodeCallRel32 disp)
    (target : branchTarget (Extracted.textAddress + BitVec.ofNat 64 codeOffset) 5 (disp.signExtend 64) = 0x108f70)
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOffset)
    (input : t.regValue .rsi = stackPtr s - BitVec.ofNat 64 592)
    (output : t.regValue .rdi = stackPtr s - BitVec.ofNat 64 744)
    (hx : Nat256At t (stackPtr s - 592) x)
    (right : t.regValue .rdx = 0x202dc8)
    (modulus : t.regValue .rcx = 0x202d88) (inverse : t.regValue .r8 = 1)
 :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧
      u.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOffset + (5 : BitVec 64) ∧
      MontgomeryAt u (stackPtr s - 744) (x % P256.Spec.Operations.domain.p) ∧
      (∀ r ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15], u.regValue r = t.regValue r) ∧
      (∀ offset len : Nat, offset ≤ 760 → len ≤ offset + 8 →
        (offset + 32 ≤ 744 ∨ 744 + len ≤ offset) →
        ∀ i < len, u.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
          t.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?) ∧
      MemoryWriteFrame t u #v[workRegion s 3360] := by
  let layout : StackCallLayout 3360 32 32 160 :=
    ⟨768,592,744,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩
  have layoutStack : layout.stackOffset = 760+8 := rfl
  have outputSaved : 32+48 ≤ 744 := by decide
  have frameBound : 760+8 ≤ 3360 := by decide
  have frameSaved : 48 ≤ 760 := by decide
  have frameAligned : (760+8)%8=0 := by decide
  have bounds := stack_bounds pre.stack
  obtain ⟨v, run, ready, effect⟩ := scalar_call pre.toCalleePre frameBound frameAligned state codeOffset disp
    (Nat.le_of_lt codeBound) bytes (by rw [target]; decide)
    (by rw [target]; exact inProgram_of_textOffset 0x0 (by decide)) rip
  have frame := state.after_call pre.toCalleePre frameBound frameSaved ready effect
  have vin : v.regValue .rsi = stackPtr s - BitVec.ofNat 64 592 :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans input
  have vout : v.regValue .rdi = stackPtr s - BitVec.ofNat 64 744 :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans output
  have ret : (returnBoundary v).rip = Extracted.textAddress + BitVec.ofNat 64 codeOffset + (5 : BitVec 64) := (callEffect_stack effect).1
  have cp : Decompress.Convert.Pre v boundary := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply CalleePre.of_stack pre.toCalleePre layout
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
    · exact (effect.agrees.read (n := 64) (r := 2) (by simp)).trans right
    · exact (effect.agrees.read (n := 64) (r := 1) (by simp)).trans modulus
    · exact (effect.agrees.read (n := 64) (r := 8) (by simp)).trans inverse
  have hleft := layout.inputAbove
  rw [layoutStack] at hleft
  have hleftEnd := layout.inputEnd
  have vx : Nat256At v (v.regValue .rsi) x := by
    rw [vin]
    exact ⟨hx.1, fun i hi => (scalar_call_byte (frameOffset := 760) (by omega) state effect (by omega) hleftEnd hi).trans (hx.2 i hi)⟩
  obtain ⟨u, result, value⟩ := Decompress.Convert.convert_correct cp vx
  have hout := layout.outputAbove
  rw [layoutStack] at hout
  obtain ⟨fuel, run'⟩ := result.execution
  refine ⟨1+fuel, u, run.trans run', after_result pre.toCalleePre frame result (by omega)
    (stack_result_work_frame pre.toCalleePre frame result vout (by omega) outputSaved (by omega) frameSaved), result.rip.trans ret, vout ▸ value, ?_, ?_, ?_⟩
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
      (scalar_call_byte (frameOffset := 760) (by omega) state effect ho hl hi)

  · exact memoryWriteFrame_trans (field_call_work_frame pre.toCalleePre state frameBound frameSaved effect)
      (stack_result_work_frame pre.toCalleePre frame result vout (by omega) outputSaved (by omega) frameSaved)


end P256.Proofs.Sec1.Affine.Uncompressed.Parse
