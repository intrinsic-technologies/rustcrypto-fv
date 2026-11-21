import P256.Proofs.Program.Compare.Tail.Support

namespace P256.Proofs.Program.Compare.Tail

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Spec.Program P256.Spec.Program.Routines

structure EightPhasePre (s : RamState) : Prop where
  rip : s.RIP = 0x11cd30
  count : maskedLength s 24 = 0
  left : MemReadable s ((Operand.reg 6 : Operand 64).read s) (maskedLength s 24).toNat
  right : MemReadable s ((Operand.reg 2 : Operand 64).read s) (maskedLength s 24).toNat

theorem eight_phase [Bindings] (boundary : ReturnBoundary) (s : RamState)
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programSections.toCodeMap s)
    (hb : RegisterBoundary boundary s) (hp : EightPhasePre s) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programSections.toCodeMap t ∧ AgreesExcept changes s t ∧
      ((PhaseSuccess s t (maskedLength s 24).toNat 0x11cd70 ∧
          (Operand.reg 8 : Operand 64).read t = (Operand.reg 6 : Operand 64).read t) ∨
        PhaseFailure s t (maskedLength s 24).toNat) := by
  obtain ⟨na, a, ha, hra, hca, hea, hspa⟩ := eight_gate boundary s hr hc hp.rip hb
  have hfa : AgreesExcept [.reg 8, .reg 9, .flags, .rip] s a := hea.agrees.mono
    (by simp [eightGateEffect, eightPrepareEffect, Effect.components,
      Write.component, Operand.component])
  have hcount := hp.count
  refine ⟨na, a, ha, hra, hca, hfa.mono (by simp [changes]), Or.inl ⟨?_, ?_⟩⟩
  · refine ⟨?_, hfa.read (by decide), ?_, ?_, ?_⟩
    · simpa only [eightGateEffect, hcount, beq_self_eq_true, ite_true] using hea.rip
    · rw [hcount]
      exact (hfa.read (n := 64) (r := 6) (by decide)).trans (BitVec.add_zero _).symm
    · rw [hcount]
      exact (hfa.read (n := 64) (r := 2) (by decide)).trans (BitVec.add_zero _).symm
    · intro i hi
      rw [hcount] at hi
      change i < 0 at hi
      omega
  · rw [hfa.read (n := 64) (r := 6) (by decide)]
    have hwrite : (Operand.reg 8 : Operand 64).read a =
        (Operand.reg 6 : Operand 64).read s + maskedLength s 24 := hea.writes.2
    rw [hcount] at hwrite
    exact hwrite.trans (BitVec.add_zero _)

end P256.Proofs.Program.Compare.Tail
