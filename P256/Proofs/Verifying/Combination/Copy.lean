import P256.Proofs.Verifying.Combination.Call
import P256.Proofs.Program.Copy
import P256.Proofs.Program.CalleeStack
import P256.Proofs.Program.FieldCall.Memory

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Spec.Program.Routines

structure CopyCallSite (n : Nat) where
  codeOffset : Nat
  codeBound : codeOffset + 3 < 118431
  bytes : Extracted.textBytes.toListFrom codeOffset 3 = [0x41, 0xff, 0xd6]
  layout : StackCallLayout 8808 n n 8
  stack : layout.stackOffset = 6560
  outputSaved : n + 48 ≤ layout.outputOffset

theorem copy_call [Bindings] {s t : RamState} {boundary : ReturnBoundary} {n : Nat}
    (pre : CalleePre s boundary 0x106500 256 96 8808) (state : State s t)
    (site : CopyCallSite n)
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 site.codeOffset)
    (target : t.regValue .r14 = 0x11c930)
    (count : t.regValue .rdx = BitVec.ofNat 64 n)
    (input : t.regValue .rsi = stackPtr s - BitVec.ofNat 64 site.layout.inputOffset)
    (output : t.regValue .rdi = stackPtr s - BitVec.ofNat 64 site.layout.outputOffset) :
    ∃ fuel u, Advances boundary fuel t u ∧ State s u ∧
      u.RIP = Extracted.textAddress + BitVec.ofNat 64 site.codeOffset + 3#64 ∧
      (∀ i < n, u.external[stackPtr s - BitVec.ofNat 64 site.layout.outputOffset + BitVec.ofNat 64 i]? =
        t.external[stackPtr s - BitVec.ofNat 64 site.layout.inputOffset + BitVec.ofNat 64 i]?) ∧
      (∀ r ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15], u.regValue r = t.regValue r) ∧
      (∀ offset len : Nat, offset ≤ 6552 → len ≤ offset + 8 →
        (offset + n ≤ site.layout.outputOffset ∨ site.layout.outputOffset + len ≤ offset) →
        ∀ i < len, u.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
          t.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?) := by
  obtain ⟨v, run, frame, effect⟩ := call_copy pre state site.codeOffset site.codeBound
    site.bytes rip target
  have vin : v.regValue .rsi = stackPtr s - BitVec.ofNat 64 site.layout.inputOffset :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans input
  have vout : v.regValue .rdi = stackPtr s - BitVec.ofNat 64 site.layout.outputOffset :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans output
  have ret : (returnBoundary v).rip =
      Extracted.textAddress + BitVec.ofNat 64 site.codeOffset + 3#64 := (callEffect_stack effect).1
  have retProg : InProgram (returnBoundary v).rip := by
    rw [ret]
    have h := inProgram_of_textOffset (site.codeOffset + 3) site.codeBound
    simpa only [BitVec.ofNat_add, BitVec.add_assoc] using h
  have cp : CalleePre v boundary 0x11c930 n n 8 :=
    CalleePre.of_stack pre site.layout frame.bindingsSupported frame.machine frame.directionFlag
      frame.loaded frame.allocated effect.rip
      (by rw [site.stack]; exact frame.rsp) vin vout retProg
  have count' : v.regValue .rdx = BitVec.ofNat 64 n :=
    (effect.agrees.read (n := 64) (r := 2) (by simp)).trans count
  have above := site.layout.inputAbove
  have finish := site.layout.inputEnd
  have outAbove := site.layout.outputAbove
  have capacity := site.layout.capacity
  rw [site.stack] at above outAbove capacity
  obtain ⟨u, result, bytes, _⟩ := memcpy_correct cp count' (by omega)
  obtain ⟨fuel, run'⟩ := result.execution
  have work := FieldCall.stack_result_work_frame (frameOffset := 6552) pre frame result vout
    (by omega) site.outputSaved (by omega) (by decide)
  refine ⟨1 + fuel, u, run.trans run', FieldCall.after_result pre frame result (by decide) work,
    result.rip.trans ret, ?_, ?_, ?_⟩
  · intro i hi
    have h := bytes i hi
    rw [vin, vout] at h
    exact h.trans (scalar_call_byte (frameOffset := 6552) (by decide) state effect (by omega) finish hi)
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
    exact (FieldCall.stack_result_byte (frameOffset := 6552) pre frame result vout (by decide) (by omega) ho hl apart hi).trans
      (scalar_call_byte (frameOffset := 6552) (by decide) state effect ho hl hi)

end P256.Proofs.Verifying.Combination
