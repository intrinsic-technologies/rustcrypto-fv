import P256.Proofs.Program.Compare.Tail.Dispatch

namespace P256.Proofs.Program.Compare.Tail

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Spec.Program P256.Spec.Program.Routines

def byteChanges : List Component := [.reg 0, .reg 1, .reg 2, .flags, .rip]

theorem byte_result [Bindings] (boundary : ReturnBoundary) (s : RamState)
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programSections.toCodeMap s)
    (hPre : ByteComparePre s) (hBoundary : RegisterBoundary boundary s)
    (hZero : (Operand.reg 0 : Operand 32).read s = 0) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programSections.toCodeMap t ∧ stackPtr t = stackPtr s ∧
      AgreesExcept byteChanges s t ∧ (t.RIP = 0x11ce9e ∨ t.RIP = 0x11ce0d) ∧
      ((Operand.reg 0 : Operand 32).read t = 0 ↔
        BytesEqual s ((Operand.reg 6 : Operand 64).read s)
          ((Operand.reg 2 : Operand 64).read s) 1) := by
  obtain ⟨fuel, u, hRun, hu, hcu, he, hsp⟩ :=
    byte_dispatch boundary s hReady hCode hPre hBoundary
  have heqv : BytesEqual s ((Operand.reg 6 : Operand 64).read s)
      ((Operand.reg 2 : Operand 64).read s) 1 ↔ lastByteLeft s = lastByteRight s :=
    bytesEqual_iff_load (width := 8)
  by_cases heq : lastByteLeft s = lastByteRight s
  · refine ⟨fuel, u, hRun, hu, hcu, hsp, ?_, ?_, ?_⟩
    · apply he.agrees.mono
      simp [byteDispatchEffect, byteCompareEffect, byteChanges, Effect.components,
        Write.component, Operand.component]
    · exact Or.inl (by simpa only [byteDispatchEffect, ite_eq_left heq] using he.rip)
    · have hz : (Operand.reg 0 : Operand 32).read u = 0 :=
        (he.agrees.read (by simp [byteDispatchEffect, byteCompareEffect,
          Effect.components, Write.component, Operand.component])).trans hZero
      exact ⟨fun _ ↦ heqv.mpr heq, fun _ ↦ hz⟩
  · have hp : u.RIP = 0x11ce09 := by
      simpa only [byteDispatchEffect, ite_eq_right heq] using he.rip
    have hc : CodeIn (codeRange 0x11ce09 [0x29, 0xd1, 0x89, 0xc8]) u :=
      program_text_slice hcu 0x1ce09 4 (by decide +kernel)
    obtain ⟨nf, t, hFinish, ht, _, hf, hsp'⟩ :=
      byte_difference boundary u hu hc hp (hBoundary.of_stack_eq hsp)
    have hct : CodeIn Extracted.programSections.toCodeMap t :=
      hf.codeIn (Effect.Avoids.of_noMem (by simp [byteDifferenceEffect, Effect.components,
        Write.component, Operand.component, Component.Covers]) _) hcu
    refine ⟨fuel + nf, t, hRun.trans hFinish, ht, hct, hsp'.trans hsp, ?_,
      Or.inr hf.rip, ?_⟩
    · apply (he.agrees.trans hf.agrees).mono
      simp [byteDispatchEffect, byteCompareEffect, byteDifferenceEffect, byteChanges,
        Effect.components, Write.component, Operand.component]
    · have hl : (Operand.reg 1 : Operand 32).read u = (lastByteLeft s).setWidth 32 := by
        have hh := congrArg (BitVec.setWidth 32) he.writes.1
        simpa [byteDispatchEffect, byteCompareEffect, Operand.read] using hh
      have hr : (Operand.reg 2 : Operand 32).read u = (lastByteRight s).setWidth 32 := by
        have hh := congrArg (BitVec.setWidth 32) he.writes.2
        simpa [byteDispatchEffect, byteCompareEffect, Operand.read] using hh
      constructor
      · intro hz
        have hh := (byte_difference_zero_iff hf).mp hz
        rw [hl, hr] at hh
        have he' : lastByteLeft s = lastByteRight s := by
          simpa using congrArg (BitVec.setWidth 8) hh
        exact False.elim (heq he')
      · intro hbytes
        exact False.elim (heq (heqv.mp hbytes))

end P256.Proofs.Program.Compare.Tail
