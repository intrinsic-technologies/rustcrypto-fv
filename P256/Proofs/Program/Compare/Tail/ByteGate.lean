import P256.Proofs.Program.Compare.Tail.ByteResult

namespace P256.Proofs.Program.Compare.Tail

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Spec.Program P256.Spec.Program.Routines

def byteLength (s : RamState) : Nat := ((Operand.reg 1 : Operand 8).read s &&& 1).toNat

structure ByteTailPre (s : RamState) : Prop where
  rip : s.RIP = 0x11cdf0
  left : MemReadable s ((Operand.reg 6 : Operand 64).read s) (byteLength s)
  right : MemReadable s ((Operand.reg 2 : Operand 64).read s) (byteLength s)

theorem byte_tail_result [Bindings] (boundary : ReturnBoundary) (s : RamState)
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programSections.toCodeMap s)
    (hPre : ByteTailPre s) (hBoundary : RegisterBoundary boundary s) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programSections.toCodeMap t ∧ stackPtr t = stackPtr s ∧
      AgreesExcept byteChanges s t ∧ (t.RIP = 0x11ce9e ∨ t.RIP = 0x11ce0d) ∧
      ((Operand.reg 0 : Operand 32).read t = 0 ↔
        BytesEqual s ((Operand.reg 6 : Operand 64).read s)
          ((Operand.reg 2 : Operand 64).read s) (byteLength s)) := by
  have hc : CodeIn (codeRange 0x11cdf0 [0x31, 0xc0, 0xf6, 0xc1, 0x01]) s :=
    program_text_slice hCode 0x1cdf0 5 (by decide +kernel)
  obtain ⟨na, u, ha, hu, _, he, hsp⟩ :=
    byte_prepare boundary s hReady hc hPre.rip hBoundary
  have hcu : CodeIn Extracted.programSections.toCodeMap u :=
    he.codeIn (Effect.Avoids.of_noMem (by simp [bytePrepareEffect, Effect.components,
      Write.component, Operand.component, Component.Covers]) _) hCode
  have hcb : CodeIn (codeRange 0x11cdf5 (0x0f :: jccOpcode32 4 :: immBytes 32 0xa3)) u :=
    program_text_slice hcu 0x1cdf5 6 (by decide +kernel)
  obtain ⟨nb, v, hb, hv, _, hf, hsp'⟩ :=
    branch32 0x11cdf5 4 0xa3 (by unfold InRoutine; decide +kernel)
      (by unfold InRoutine; decide +kernel) boundary u hu hcb he.rip
      (hBoundary.of_stack_eq hsp)
  have hcv : CodeIn Extracted.programSections.toCodeMap v :=
    hf.codeIn (branchEffect_avoids _ _ _ _) hcu
  have hag : AgreesExcept [.reg 0, .flags, .rip] s v := by
    apply (he.agrees.trans hf.agrees).mono
    simp [bytePrepareEffect, jccEffect, branchEffect, Effect.components,
      Write.component, Operand.component]
  have hspv := hsp'.trans hsp
  have hz : (StatusFlags.ofRFLAGS u.RFLAGS).ZF =
      (((Operand.reg 1 : Operand 8).read s &&& 1) == 0) := he.flags.2.2.2.1
  have hzv : (Operand.reg 0 : Operand 32).read v = 0 := by
    rw [hf.agrees.read (n := 32) (r := 0) (by simp [jccEffect])]
    simpa [bytePrepareEffect, Operand.read] using congrArg (BitVec.setWidth 32) he.writes
  by_cases hlen : byteLength s = 0
  · have hbit : (Operand.reg 1 : Operand 8).read s &&& 1 = 0 := by
      apply BitVec.eq_of_toNat_eq
      exact hlen
    refine ⟨na + nb, v, ha.trans hb, hv, hcv, hspv, ?_, ?_, ?_⟩
    · exact hag.mono (by simp [byteChanges])
    · apply Or.inl
      rw [hf.rip]
      change (if (StatusFlags.ofRFLAGS u.RFLAGS).ZF then 0x11ce9e else 0x11cdfb) = _
      rw [hz, hbit]
      rfl
    · constructor
      · intro _ i hi
        rw [hlen] at hi
        omega
      · intro _
        exact hzv
  · have hone : byteLength s = 1 := by
      have h : ∀ x : BitVec 8, (x &&& 1).toNat ≤ 1 := by decide +kernel
      have := h ((Operand.reg 1 : Operand 8).read s)
      change byteLength s ≤ 1 at this
      omega
    have hbit : (Operand.reg 1 : Operand 8).read s &&& 1 ≠ 0 := by
      intro heq
      exact hlen (congrArg BitVec.toNat heq)
    have hp : v.RIP = 0x11cdfb := by
      rw [hf.rip]
      change (if (StatusFlags.ofRFLAGS u.RFLAGS).ZF then 0x11ce9e else 0x11cdfb) = _
      rw [hz, beq_eq_false_iff_ne.mpr hbit]
      rfl
    have hmem : v.external = s.external := hag.external (by simp [Component.Covers])
    have hl : (Operand.reg 6 : Operand 64).read v = (Operand.reg 6 : Operand 64).read s :=
      hag.read (by simp)
    have hr : (Operand.reg 2 : Operand 64).read v = (Operand.reg 2 : Operand 64).read s :=
      hag.read (by simp)
    have hbp : ByteComparePre v := by
      refine ⟨hp, ?_, ?_⟩
      · rw [hl]
        exact (hone ▸ hPre.left).of_external_eq hmem
      · rw [hr]
        exact (hone ▸ hPre.right).of_external_eq hmem
    obtain ⟨nc, t, hcRun, ht, hct, hspt, hframe, hip, hres⟩ :=
      byte_result boundary v hv hcv hbp (hBoundary.of_stack_eq hspv) hzv
    refine ⟨na + nb + nc, t, (ha.trans hb).trans hcRun, ht, hct, hspt.trans hspv,
      ?_, hip, ?_⟩
    · apply (hag.trans hframe).mono
      simp [byteChanges]
    · simpa only [hone, BytesEqual, hl, hr, hmem] using hres

end P256.Proofs.Program.Compare.Tail
