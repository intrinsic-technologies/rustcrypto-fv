import P256.Proofs.Verifying.Core.Products.Correct
import P256.Proofs.Verifying.Core.Memory
import P256.Proofs.Program.FieldCall.Binary

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Scalars

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame FieldCall Field

def productSite (second : Bool) : BinaryCallSite 9992 1176 0x113320 280 :=
  if second then
    ⟨0xdd64,0x55b7,by decide,by decide +kernel,by decide +kernel,by decide,
      inProgram_of_textOffset 0x13320 (by decide),
      ⟨1184,1048,344,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩,
      rfl,by decide,408,by decide,by decide,by decide⟩
  else
    ⟨0xdd18,0x5603,by decide,by decide +kernel,by decide +kernel,by decide,
      inProgram_of_textOffset 0x13320 (by decide),
      ⟨1184,208,376,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩,
      rfl,by decide,1048,by decide,by decide,by decide⟩

theorem product_call [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {x y : Nat}
    (pre : Core.Pre s boundary) (state : Frame s t) (second : Bool)
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 (productSite second).codeOffset)
    (input : t.regValue .rsi = stackPtr s - BitVec.ofNat 64 (productSite second).layout.inputOffset)
    (right : t.regValue .rdx = stackPtr s - BitVec.ofNat 64 (productSite second).rightOffset)
    (output : t.regValue .rdi = stackPtr s - BitVec.ofNat 64 (productSite second).layout.outputOffset)
    (hx : SecretKeyFromBytes.Scalar.Nat256At t (stackPtr s - BitVec.ofNat 64 (productSite second).layout.inputOffset) x)
    (hy : SecretKeyFromBytes.Scalar.Nat256At t (stackPtr s - BitVec.ofNat 64 (productSite second).rightOffset) y) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧
      u.RIP = Extracted.textAddress + BitVec.ofNat 64 (productSite second).codeOffset + (5 : BitVec 64) ∧
      SecretKeyFromBytes.Scalar.Nat256At u (stackPtr s - BitVec.ofNat 64 (productSite second).layout.outputOffset) (x*y % Operations.domain.n) ∧
      (∀ r ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15], u.regValue r = t.regValue r) ∧
      (∀ offset len : Nat, offset ≤ 1176 → len ≤ offset + 8 →
        (offset + 32 ≤ (productSite second).layout.outputOffset ∨ (productSite second).layout.outputOffset + len ≤ offset) →
        ∀ i < len, u.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
          t.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?) ∧
      MemoryWriteFrame t u (prefixRegions s) := by
  let site := productSite second
  have capacity := (productSite second).layout.capacity
  have outputAbove := (productSite second).layout.outputAbove
  have aligned := (productSite second).layout.aligned
  rw [(productSite second).stack] at capacity outputAbove aligned
  have saved := (productSite second).outputSaved
  have frameBound : 1176 + 8 ≤ 9992 := by omega
  have frameSaved : 48 ≤ 1176 := by omega
  have frameAligned : (1176 + 8) % 8 = 0 := by omega
  have bounds := stack_bounds pre.stack
  obtain ⟨v, run, ready, effect⟩ := scalar_call pre.toCalleePre frameBound frameAligned state (productSite second).codeOffset (productSite second).disp
    (Nat.le_of_lt (productSite second).codeBound) (productSite second).bytes (by rw [(productSite second).target]; exact (productSite second).entryLow)
    (by rw [(productSite second).target]; exact (productSite second).entryProgram) rip
  have frame := state.after_call pre.toCalleePre frameBound frameSaved ready effect
  have vin : v.regValue .rsi = stackPtr s - BitVec.ofNat 64 (productSite second).layout.inputOffset :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans input
  have vright : v.regValue .rdx = stackPtr s - BitVec.ofNat 64 (productSite second).rightOffset :=
    (effect.agrees.read (n := 64) (r := 2) (by simp)).trans right
  have vout : v.regValue .rdi = stackPtr s - BitVec.ofNat 64 (productSite second).layout.outputOffset :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans output
  have ret : (returnBoundary v).rip = Extracted.textAddress + BitVec.ofNat 64 (productSite second).codeOffset + (5 : BitVec 64) := (callEffect_stack effect).1
  have cp : BinaryFieldPre v boundary 0x113320 280 := by
    apply BinaryFieldPre.of_stack pre.toCalleePre (productSite second).layout (productSite second).rightOffset
    · simpa only [(productSite second).stack] using (productSite second).rightAbove
    · exact (productSite second).rightEnd
    · exact (productSite second).rightApart
    · exact frame.bindingsSupported
    · exact frame.machine
    · exact frame.directionFlag
    · exact frame.loaded
    · exact frame.allocated
    · exact effect.rip.trans (productSite second).target
    · rw [(productSite second).stack]
      exact frame.rsp
    · exact vin
    · exact vright
    · exact vout
    · rw [ret]
      rw [show Extracted.textAddress + BitVec.ofNat 64 (productSite second).codeOffset + (5 : BitVec 64) =
        Extracted.textAddress + BitVec.ofNat 64 ((productSite second).codeOffset+5) by
          rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl]
      exact inProgram_of_textOffset _ (productSite second).codeBound
  have hleft := (productSite second).layout.inputAbove
  rw [(productSite second).stack] at hleft
  have hleftEnd := (productSite second).layout.inputEnd
  have vx : SecretKeyFromBytes.Scalar.Nat256At v (v.regValue .rsi) x := by
    rw [vin]
    exact ⟨hx.1, fun i hi => (scalar_call_byte (frameOffset := 1176) (by omega) state effect (by omega) hleftEnd hi).trans (hx.2 i hi)⟩
  have vy : SecretKeyFromBytes.Scalar.Nat256At v (v.regValue .rdx) y := by
    rw [vright]
    exact ⟨hy.1, fun i hi => (scalar_call_byte (frameOffset := 1176) (by omega) state effect (by have := (productSite second).rightAbove; omega)
      (productSite second).rightEnd hi).trans (hy.2 i hi)⟩
  obtain ⟨u, result, value⟩ := Core.Products.multiply_correct cp vx vy
  have hout := (productSite second).layout.outputAbove
  rw [(productSite second).stack] at hout
  obtain ⟨fuel, run'⟩ := result.execution
  refine ⟨1+fuel, u, run.trans run', after_result pre.toCalleePre frame result (by omega)
    (stack_result_work_frame pre.toCalleePre frame result vout (by omega) (productSite second).outputSaved (by omega) frameSaved), result.rip.trans ret, vout ▸ value, ?_, ?_, ?_⟩
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
      (scalar_call_byte (frameOffset := 1176) (by omega) state effect ho hl hi)

  · apply memoryWriteFrame_trans (prefix_call pre state effect)
    apply prefix_result pre frame result (offset := if second then 832 else 800)
    · rw [vout]
      cases second <;> simp only [productSite,Bool.false_eq_true,ite_false,ite_true,
        frameBase,BitVec.sub_eq_add_neg,BitVec.add_assoc] <;> rfl
    · cases second <;> decide
    · decide

end P256.Proofs.Verifying.Core.Scalars
