import P256.Proofs.Sec1.Affine.State
import P256.Proofs.Program.FieldCall.Memory
import P256.Proofs.Sec1.Affine.Uncompressed.Parse.LimbPre
import P256.Proofs.Field.Preserve

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Parse

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Field
open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program.FieldCall
open P256.Proofs.SecretKeyFromBytes.Scalar

theorem limb_call [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {x out : Nat} {bytes : ByteArray} {select : Bool}
    (pre : AffineDecodePre s boundary bytes) (state : Frame s t)
    (outputBound : 80 ≤ out) (outputTop : out ≤ 712)
    (codeOffset : Nat) (disp : BitVec 32) (codeBound : codeOffset + 5 < 118431)
    (bytes : Extracted.textBytes.toListFrom codeOffset 5 = encodeCallRel32 disp)
    (target : branchTarget (Extracted.textAddress + BitVec.ofNat 64 codeOffset) 5 (disp.signExtend 64) = 0x1191c0)
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOffset)
    (counts : t.regValue .rsi = 4 ∧ t.regValue .rcx = 4)
    (input : t.regValue .rdx = stackPtr s - 744)
    (output : t.regValue .rdi = stackPtr s - BitVec.ofNat 64 out)
    (left : MontgomeryAt t (stackPtr s - BitVec.ofNat 64 out) 0)
    (right : MontgomeryAt t (stackPtr s - 744) x)
    (choice : t.regValue .r8 = if select then 1 else 0)
 :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧
      u.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOffset + (5 : BitVec 64) ∧
      MontgomeryAt u (stackPtr s - BitVec.ofNat 64 out) (if select then x else 0) ∧
      (∀ r ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15], u.regValue r = t.regValue r) ∧
      (∀ offset len : Nat, offset ≤ 760 → len ≤ offset + 8 →
        (offset + 32 ≤ out ∨ out + len ≤ offset) →
        ∀ i < len, u.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
          t.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?) ∧
      MemoryWriteFrame t u #v[workRegion s 3360] := by
  let layout : StackCallLayout 3360 32 32 80 :=
    ⟨768,744,out,by decide,by decide,by decide,by omega,by decide,by omega,.inl (by omega)⟩
  have layoutStack : layout.stackOffset = 760+8 := rfl
  have outputSaved : 32+48 ≤ out := outputBound
  have frameBound : 760+8 ≤ 3360 := by decide
  have frameSaved : 48 ≤ 760 := by decide
  have frameAligned : (760+8)%8=0 := by decide
  have bounds := stack_bounds pre.stack
  obtain ⟨v, run, ready, effect⟩ := scalar_call pre.toCalleePre frameBound frameAligned state codeOffset disp
    (Nat.le_of_lt codeBound) bytes (by rw [target]; decide)
    (by rw [target]; exact inProgram_of_textOffset 0x191c0 (by decide)) rip
  have frame := state.after_call pre.toCalleePre frameBound frameSaved ready effect
  have vin : v.regValue .rdx = stackPtr s - 744 :=
    (effect.agrees.read (n := 64) (r := 2) (by simp)).trans input
  have vout : v.regValue .rdi = stackPtr s - BitVec.ofNat 64 out :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans output
  have ret : (returnBoundary v).rip = Extracted.textAddress + BitVec.ofNat 64 codeOffset + (5 : BitVec 64) := (callEffect_stack effect).1
  have cp := limb_call_pre layout rfl rfl rfl pre.toCalleePre frame frame.rsp
    (effect.rip.trans target)
    ((effect.agrees.read (n := 64) (r := 6) (by simp)).trans counts.1)
    ((effect.agrees.read (n := 64) (r := 1) (by simp)).trans counts.2) vin vout (by
      rw [ret]
      have addr : Extracted.textAddress + BitVec.ofNat 64 codeOffset + (5 : BitVec 64) =
          Extracted.textAddress + BitVec.ofNat 64 (codeOffset+5) := by
        rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl
      rw [addr]
      exact inProgram_of_textOffset _ codeBound)
  have vl : MontgomeryAt v (v.regValue .rdi) 0 := by
    rw [vout]
    exact left.of_bytes_eq (fun i hi => scalar_call_byte (frameOffset := 760) (by decide) state effect (by omega) (by omega) hi)
  have vr : MontgomeryAt v (v.regValue .rdx) x := by
    rw [vin]
    exact right.of_bytes_eq (fun i hi => scalar_call_byte (frameOffset := 760) (by decide) state effect (by decide) (by decide) hi)
  have vc : v.regValue .r8 = if select then 1 else 0 :=
    (effect.agrees.read (n := 64) (r := 8) (by simp)).trans choice
  obtain ⟨u,result,selected⟩ := LimbSelect.limb_select32_correct cp vc
  have value : MontgomeryAt u (v.regValue .rdi) (if select then x else 0) := by
    cases select with
    | false => exact vl.of_bytes_eq (fun i hi => by simpa only [LimbSelect.SelectedBytesAt, Bool.false_eq_true, ite_false] using selected i hi)
    | true => exact vr.of_bytes_eq (fun i hi => by simpa only [LimbSelect.SelectedBytesAt, Bool.true_eq, ite_true] using selected i hi)
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
