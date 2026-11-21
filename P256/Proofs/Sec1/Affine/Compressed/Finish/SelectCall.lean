import P256.Proofs.Program.FieldCall.Binary
import P256.Proofs.Projective.Multiply.Machine.Lookup.Select.Correct

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Compressed.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open P256.Proofs.Program P256.Proofs.Program.FieldCall P256.Proofs.Program.ScalarFrame P256.Proofs.Field
open X86 X86.Machine X86.UserProcess X86Proofs

variable {outerEntry : BitVec 64} {outerInput outerOutput outerReserve frameOffset : Nat}

variable {inputRegister : Syntax.Reg}

theorem select_bytes_call [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {select : Bool}
    (pre : CalleePre s boundary outerEntry outerInput outerOutput outerReserve inputRegister) (state : FrameState s t outerOutput outerReserve (BitVec.ofNat 64 frameOffset))
    (site : BinaryCallSite outerReserve frameOffset 0x114380 128)
    (choice : (t.regValue .rcx).setWidth 8 = if select then 1 else 0)
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 site.codeOffset)
    (input : t.regValue .rsi = stackPtr s - BitVec.ofNat 64 site.layout.inputOffset)
    (right : t.regValue .rdx = stackPtr s - BitVec.ofNat 64 site.rightOffset)
    (output : t.regValue .rdi = stackPtr s - BitVec.ofNat 64 site.layout.outputOffset)
 :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u outerOutput outerReserve (BitVec.ofNat 64 frameOffset) ∧
      u.RIP = Extracted.textAddress + BitVec.ofNat 64 site.codeOffset + (5 : BitVec 64) ∧
      (∀ i < 32, u.external[stackPtr s - BitVec.ofNat 64 site.layout.outputOffset + BitVec.ofNat 64 i]? =
        t.external[(if select then stackPtr s - BitVec.ofNat 64 site.rightOffset else
          stackPtr s - BitVec.ofNat 64 site.layout.inputOffset) + BitVec.ofNat 64 i]?) ∧
      (∀ r ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15], u.regValue r = t.regValue r) ∧
      (∀ offset len : Nat, offset ≤ frameOffset → len ≤ offset + 8 →
        (offset + 32 ≤ site.layout.outputOffset ∨ site.layout.outputOffset + len ≤ offset) →
        ∀ i < len, u.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
          t.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?) ∧
      MemoryWriteFrame t u #v[workRegion s outerReserve] := by
  have capacity := site.layout.capacity
  have outputAbove := site.layout.outputAbove
  have aligned := site.layout.aligned
  rw [site.stack] at capacity outputAbove aligned
  have saved := site.outputSaved
  have frameBound : frameOffset + 8 ≤ outerReserve := by omega
  have frameSaved : 48 ≤ frameOffset := by omega
  have frameAligned : (frameOffset + 8) % 8 = 0 := by omega
  have bounds := stack_bounds pre.stack
  obtain ⟨v, run, ready, effect⟩ := scalar_call pre frameBound frameAligned state site.codeOffset site.disp
    (Nat.le_of_lt site.codeBound) site.bytes (by rw [site.target]; exact site.entryLow)
    (by rw [site.target]; exact site.entryProgram) rip
  have frame := state.after_call pre frameBound frameSaved ready effect
  have vin : v.regValue .rsi = stackPtr s - BitVec.ofNat 64 site.layout.inputOffset :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans input
  have vright : v.regValue .rdx = stackPtr s - BitVec.ofNat 64 site.rightOffset :=
    (effect.agrees.read (n := 64) (r := 2) (by simp)).trans right
  have vout : v.regValue .rdi = stackPtr s - BitVec.ofNat 64 site.layout.outputOffset :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans output
  have ret : (returnBoundary v).rip = Extracted.textAddress + BitVec.ofNat 64 site.codeOffset + (5 : BitVec 64) := (callEffect_stack effect).1
  have cp : BinaryFieldPre v boundary 0x114380 128 := by
    apply BinaryFieldPre.of_stack pre site.layout site.rightOffset
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
  have selectV : (v.regValue .rcx).setWidth 8 = if select then 1 else 0 :=
    (congrArg (BitVec.setWidth 8) (effect.agrees.read (n := 64) (r := 1) (by simp))).trans choice
  obtain ⟨u, result, value⟩ :=
    P256.Proofs.Projective.Multiply.Machine.Lookup.Select.field_select_bytes_correct cp selectV
  have hout := site.layout.outputAbove
  rw [site.stack] at hout
  obtain ⟨fuel, run'⟩ := result.execution
  refine ⟨1+fuel, u, run.trans run', after_result pre frame result (by omega)
    (stack_result_work_frame pre frame result vout (by omega) site.outputSaved (by omega) frameSaved), result.rip.trans ret, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have h := value i hi
    rw [vout] at h
    apply h.trans
    cases select
    · change v.external[v.regValue .rsi + BitVec.ofNat 64 i]? = _
      rw [vin]
      exact scalar_call_byte (frameOffset := frameOffset) (by omega) state effect (by omega) hleftEnd hi
    · change v.external[v.regValue .rdx + BitVec.ofNat 64 i]? = _
      rw [vright]
      exact scalar_call_byte (frameOffset := frameOffset) (by omega) state effect
        (by have := site.rightAbove; omega) site.rightEnd hi
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
      (stack_result_work_frame pre frame result vout (by omega) site.outputSaved (by omega) frameSaved)


end P256.Proofs.Sec1.Affine.Compressed.Finish
