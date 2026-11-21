import P256.Proofs.PublicPoint.Normalize.OutputSelect.Result
import P256.Proofs.Projective.Multiply.Machine.Lookup.Select.Correct

set_option autoImplicit false

namespace P256.Proofs.PublicPoint.Normalize.OutputSelect

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open Program Program.ScalarFrame Field X86 X86.Machine X86.UserProcess X86Proofs

structure Site where
  codeOffset : Nat
  disp : BitVec 32
  codeBound : codeOffset + 5 < 118431
  bytes : Extracted.textBytes.toListFrom codeOffset 5 = encodeCallRel32 disp
  target : branchTarget (Extracted.textAddress + BitVec.ofNat 64 codeOffset) 5 (disp.signExtend 64) = 0x114380
  leftOffset : Nat
  leftAbove : leftOffset ≤ 1944
  leftEnd : 24 ≤ leftOffset
  rightOffset : Nat
  rightAbove : rightOffset ≤ 1944
  rightEnd : 24 ≤ rightOffset
  outputOffset : Nat
  outputBound : outputOffset + 32 ≤ 65

theorem select_call [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x y : Nat} {flag : Bool}
    (pre : CalleePre s boundary 0x10e6f0 32 65 3352) (state : FrameState s t 65 3352 1944)
    (site : Site)
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 site.codeOffset)
    (input : t.regValue .rsi = stackPtr s - BitVec.ofNat 64 site.leftOffset)
    (right : t.regValue .rdx = stackPtr s - BitVec.ofNat 64 site.rightOffset)
    (output : t.regValue .rdi = s.regValue .rdi + BitVec.ofNat 64 site.outputOffset)
    (hx : MontgomeryAt t (stackPtr s - BitVec.ofNat 64 site.leftOffset) x)
    (hy : MontgomeryAt t (stackPtr s - BitVec.ofNat 64 site.rightOffset) y)
    (choice : (t.regValue .rcx).setWidth 8 = if flag then 1 else 0) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 65 3352 1944 ∧
      u.RIP = Extracted.textAddress + BitVec.ofNat 64 site.codeOffset + (5 : BitVec 64) ∧
      MontgomeryAt u (s.regValue .rdi + BitVec.ofNat 64 site.outputOffset) (if flag then y else x) ∧
      (∀ r ∈ [Syntax.Reg.rbx,.rbp,.r12,.r13,.r14,.r15],u.regValue r = t.regValue r) ∧
      (∀ offset len : Nat, offset ≤ 1944 → len ≤ offset + 8 → ∀ i < len,
        u.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
          t.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?) ∧
      (∀ i < 65, (i < site.outputOffset ∨ site.outputOffset + 32 ≤ i) →
        u.external[s.regValue .rdi + BitVec.ofNat 64 i]? =
          t.external[s.regValue .rdi + BitVec.ofNat 64 i]?) := by
  obtain ⟨v,run,ready,effect⟩ := scalar_call (frameOffset := 1944) pre (by decide) (by decide)
    state site.codeOffset site.disp (Nat.le_of_lt site.codeBound) site.bytes
    (by rw [site.target]; decide)
    (by rw [site.target]; exact inProgram_of_textOffset 0x14380 (by decide)) rip
  have frame := state.after_call (frameOffset := 1944) pre (by decide) (by decide) ready effect
  have vin : v.regValue .rsi = stackPtr s - BitVec.ofNat 64 site.leftOffset :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans input
  have vr : v.regValue .rdx = stackPtr s - BitVec.ofNat 64 site.rightOffset :=
    (effect.agrees.read (n := 64) (r := 2) (by simp)).trans right
  have vd : v.regValue .rdi = s.regValue .rdi + BitVec.ofNat 64 site.outputOffset :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans output
  have ret : (returnBoundary v).rip = Extracted.textAddress + BitVec.ofNat 64 site.codeOffset + (5 : BitVec 64) :=
    (callEffect_stack effect).1
  have cp := binary_pre pre frame site.leftAbove site.leftEnd site.rightAbove site.rightEnd
    site.outputBound (effect.rip.trans site.target) vin vr vd (by
      rw [ret]
      have h := inProgram_of_textOffset (site.codeOffset+5) site.codeBound
      simpa only [BitVec.ofNat_add,BitVec.add_assoc,BitVec.ofNat_eq_ofNat] using h)
  have vx : MontgomeryAt v (v.regValue .rsi) x := by
    rw [vin]
    exact hx.of_bytes_eq (fun i hi => scalar_call_byte (frameOffset := 1944) (by decide)
      state effect site.leftAbove (by have := site.leftEnd; omega) hi)
  have vy : MontgomeryAt v (v.regValue .rdx) y := by
    rw [vr]
    exact hy.of_bytes_eq (fun i hi => scalar_call_byte (frameOffset := 1944) (by decide)
      state effect site.rightAbove (by have := site.rightEnd; omega) hi)
  have vc : (v.regValue .rcx).setWidth 8 = if flag then 1 else 0 :=
    (congrArg (BitVec.setWidth 8) (effect.agrees.read (n := 64) (r := 1) (by simp))).trans choice
  obtain ⟨u,result,value⟩ := Projective.Multiply.Machine.Lookup.Select.field_select_low8_correct cp vx vy vc
  obtain ⟨fuel,run'⟩ := result.execution
  refine ⟨1+fuel,u,run.trans run',after_result pre frame result vd site.outputBound,
    result.rip.trans ret,vd ▸ value,?_,?_,?_⟩
  · intro r hr
    apply (result.calleeSaved r hr).trans
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact effect.agrees.read (n := 64) (r := 3) (by simp)
    · exact effect.agrees.read (n := 64) (r := 5) (by simp)
    · exact effect.agrees.read (n := 64) (r := 12) (by simp)
    · exact effect.agrees.read (n := 64) (r := 13) (by simp)
    · exact effect.agrees.read (n := 64) (r := 14) (by simp)
    · exact effect.agrees.read (n := 64) (r := 15) (by simp)
  · intro offset len ho hl i hi
    exact (result_stack_byte pre frame result vd site.outputBound ho hl hi).trans
      (scalar_call_byte (frameOffset := 1944) (by decide) state effect ho hl hi)
  · intro i hi apart
    exact (result_output_byte pre frame result vd site.outputBound hi apart).trans
      (call_output_byte pre state effect hi)

end P256.Proofs.PublicPoint.Normalize.OutputSelect
