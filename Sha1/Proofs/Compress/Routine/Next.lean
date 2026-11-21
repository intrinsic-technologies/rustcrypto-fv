import Sha1.Proofs.Compress.Routine.Interface
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.RM.Triple
import X86Proofs.Instructions.Branch.Triple

namespace Sha1.Proofs.Compress.Routine

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Sha1.Proofs.Refine
open Sha1.Spec Sha1.Spec.Program Standards.NIST

private theorem next_frame {c : Context} {s t : RamState} (hf : Frame c s)
    (ha : AgreesExcept [.reg 6, .flags, .rip] s t) : Frame c t := by
  have hm : t.external = s.external := ha.external (by simp [Component.Covers])
  refine ⟨(ha.read (r := 4) (n := 64) (by decide)).trans hf.stackPointer,
    hf.writable.of_external_eq hm, ?_, ?_, ?_, ?_, ?_,
    ha.rest.trans hf.controls, ha.directionFlagClear (by decide) hf.directionFlag⟩
  · rw [hm]
    exact hf.memory
  · rw [hm]
    exact hf.saved
  · rw [hm]
    exact hf.output
  · rw [hm]
    exact hf.inputEnd
  · rw [hm]
    exact hf.callerReturn

private theorem next_registers {H : Vector (BitVec 32) 5} {s t : RamState}
    (hr : Machine.LoopRegisters H s) (ha : AgreesExcept [.reg 6, .flags, .rip] s t) :
    Machine.LoopRegisters H t := by
  rcases hr with ⟨h11, h8, h2, h10, h0⟩
  exact ⟨(ha.read (by decide)).trans h11, (ha.read (by decide)).trans h8,
    (ha.read (by decide)).trans h2, (ha.read (by decide)).trans h10,
    (ha.read (by decide)).trans h0⟩

private theorem next_not_boundary {c : Context} {s : RamState}
    (hf : Frame c s) : s.GPR[4] ≠ (returnBoundary c.initial).rsp := by
  intro he
  change stackPtr s = c.sp + 8 at he
  rw [hf.stackPointer] at he
  change c.sp - 208 = c.sp + 8 at he
  have he' := congrArg (fun x : BitVec 64 ↦ x + 208) he
  rw [BitVec.sub_add_cancel, BitVec.add_assoc] at he'
  have hh : c.sp = c.sp + (216 : BitVec 64) := he'
  have hz := BitVec.self_eq_add_right.mp hh
  contradiction

private theorem next_input_add (c : Context) (k : Nat) : c.input k + 64 = c.input (k + 1) := by
  simp only [Context.input, Nat.mul_add, Nat.mul_one, BitVec.ofNat_add, BitVec.add_assoc]
  rfl

private theorem next_input_eq_iff {c : Context} {bindings : Bindings}
    (hv : c.Valid bindings) {k : Nat} (hk : k < c.count) :
    c.input (k + 1) = c.input c.count ↔ k + 1 = c.count := by
  constructor
  · intro he
    have hs := hv.call.inputInMemory.2.1
    change (c.initial.regValue .rsi).toNat + c.blocks.size < 2 ^ 32 at hs
    have hm : 64 * c.count ≤ c.blocks.size := Nat.mul_div_le _ _
    have h1 : 64 * (k + 1) < 2 ^ 64 := by omega
    have h2 : 64 * c.count < 2 ^ 64 := by omega
    change c.initial.regValue .rsi + BitVec.ofNat 64 (64 * (k + 1)) =
      c.initial.regValue .rsi + BitVec.ofNat 64 (64 * c.count) at he
    have hh := congrArg BitVec.toNat ((BitVec.add_right_inj _).mp he)
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1,
      Nat.mod_eq_of_lt h2] at hh
    omega
  · exact fun he ↦ congrArg c.input he

set_option maxHeartbeats 800000 in
theorem nextAdvanceCorrect : NextAdvanceCorrect := by
  intro bindings boundary c hv hBoundary k H s hk hReady hCode hRip hAt
  letI := bindings
  have hCode1 : CodeIn (codeRange 0x1036a2 [0x48, 0x83, 0xc6, 0x40]) s :=
    Machine.program_text_slice hCode 0x36a2 4 (by decide +kernel)
  obtain ⟨s1, hs1, hr1, he1⟩ :=
    add_r64_imm8_effect_step 0x1036a2 0x48 0xc6 0x40
      (by decide +kernel) (by decide +kernel) (by decide +kernel) s hReady hCode1 hRip
  have ha1 : AgreesExcept [.reg 6, .flags, .rip] s s1 := he1.agrees
  have hf1 := next_frame hAt.frame ha1
  have hp1 : s1.RIP = 0x1036a6 := he1.rip
  have adv1 := Advances.of_step hs1 (Or.inl (by
    rw [hp1]
    exact Machine.outsideCompression_ne hBoundary (by decide) (by decide)))
  have hm1 : s1.external = s.external := ha1.external (by simp [Component.Covers])
  have hc1 := CodeIn.of_external_eq hm1 hCode
  have hi1 : s1.regValue .rsi = c.input (k + 1) := by
    have hw := he1.writes
    change (Operand.reg 6 : Operand 64).read s1 =
      (Operand.reg 6 : Operand 64).read s + 64 at hw
    exact hw.trans ((congrArg (fun x : BitVec 64 ↦ x + 64) hAt.inputPointer).trans
      (next_input_add c k))
  have hRead : LoadPre 0x1036a6
      (fun t ↦ (AddrMode.sib 4 none 0 (.d32 0x88)).addr t
        (0x1036a6 + BitVec.ofNat 64 (movLoadLen (.sib 4 none 0 (.d32 0x88))))) 8 s1 := by
    refine ⟨hp1, ?_⟩
    change MemReadable s1 (stackPtr s1 + 136) 8
    rw [hf1.stackPointer]
    exact Machine.memReadable_slice hf1.writable.readable 136 8 (by decide +kernel)
  have hCode2 : CodeIn (codeRange 0x1036a6 [0x48, 0x3b, 0xb4, 0x24, 0x88, 0, 0, 0]) s1 :=
    Machine.program_text_slice hc1 0x36a6 8 (by decide +kernel)
  obtain ⟨s2, hs2, hr2, he2⟩ :=
    cmp_r64_m64_effect_step 0x1036a6 0x48 (by decide +kernel) 6
      (.sib 4 none 0 (.d32 0x88)) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) s1 hr1 hCode2 hRead
  have ha2 : AgreesExcept [.reg 6, .flags, .rip] s1 s2 :=
    he2.agrees.mono (by simp [cmpR64M64Effect_components])
  have hf2 := next_frame hf1 ha2
  have hp2 : s2.RIP = 0x1036ae := he2.rip
  have adv2 := Advances.of_step hs2 (Or.inl (by
    rw [hp2]
    exact Machine.outsideCompression_ne hBoundary (by decide) (by decide)))
  have hm2 : s2.external = s1.external := he2.agrees.external (by simp [Component.Covers])
  have hc2 := CodeIn.of_external_eq hm2 hc1
  have hz : (StatusFlags.ofRFLAGS s2.RFLAGS).ZF =
      (c.input (k + 1) == c.input c.count) := by
    have hh := he2.flags
    change (StatusFlagsOutcome.ofStatusFlags
      (cmpSpec (s1.regValue .rsi)
        (memLoad s1.external (stackPtr s1 + 136) 64))).Allows
      (StatusFlags.ofRFLAGS s2.RFLAGS) at hh
    have hz := hh.2.2.2.1
    change (StatusFlags.ofRFLAGS s2.RFLAGS).ZF =
      (cmpSpec (s1.regValue .rsi)
        (memLoad s1.external (stackPtr s1 + 136) 64)).ZF at hz
    rw [hi1, hf1.stackPointer, hf1.inputEnd, cmpSpec_ZF] at hz
    exact hz
  have hCode3 : CodeIn (codeRange 0x1036ae
      (0x0f :: jccOpcode32 5 :: immBytes 32 (0xffffee7c : BitVec 32))) s2 :=
    Machine.program_text_slice hc2 0x36ae 6 (by decide +kernel)
  obtain ⟨t, hst, hrt, het⟩ :=
    jcc_rel32_effect_step 0x1036ae 5 0xffffee7c s2 hr2 hCode3
      ⟨hp2, fun _ ↦ by decide +kernel⟩
  have hat : AgreesExcept [.reg 6, .flags, .rip] s2 t := by
    apply het.agrees.mono
    simp only [jccEffect, branchEffect_components]
    simp
  have hft := next_frame hf2 hat
  have hnext : t.RIP = (if k + 1 < c.count then 0x102530 else 0x1036b4) := by
    have ht := het.rip
    simp only [jccEffect, branchEffect, condHolds_5, hz] at ht
    by_cases hlt : k + 1 < c.count
    · have hne : c.input (k + 1) ≠ c.input c.count := by
        intro he
        have heq := (next_input_eq_iff hv hk).mp he
        omega
      have htgt : branchTarget 0x1036ae 6 ((0xffffee7c : BitVec 32).signExtend 64) = 0x102530 := by decide +kernel
      simpa only [hlt, ↓reduceIte, beq_eq_false_iff_ne.mpr hne, Bool.not_false, htgt] using ht
    · have heq : k + 1 = c.count := by omega
      have hei := congrArg c.input heq
      have hn : (0x1036ae : BitVec 64) + BitVec.ofNat 64 6 = 0x1036b4 := by decide +kernel
      simpa only [hlt, ↓reduceIte, hei, BEq.rfl, Bool.not_true, Bool.false_eq_true, hn] using ht
  have adv3 := Advances.of_step hst (Or.inl (by
    rw [hnext]
    split <;> exact Machine.outsideCompression_ne hBoundary (by decide) (by decide)))
  have hmt : t.external = s2.external := hat.external (by simp [Component.Covers])
  have hc := CodeIn.of_external_eq hmt hc2
  have har : AgreesExcept [.reg 6, .flags, .rip] s1 t :=
    (ha2.trans hat).mono (by simp)
  have hal : AgreesExcept [.reg 6, .flags, .rip] s t :=
    (ha1.trans har).mono (by simp)
  refine ⟨3, t, adv1.trans (adv2.trans adv3), hrt, hc, ?_,
    ⟨hft, next_registers hAt.registers hal, ?_, ?_⟩, ?_⟩
  · have ht := het.rip
    simp only [jccEffect, branchEffect, condHolds_5, hz] at ht
    by_cases hlt : k + 1 < c.count
    · have hne : c.input (k + 1) ≠ c.input c.count := by
        intro he
        have := (next_input_eq_iff hv hk).mp he
        omega
      have htgt : branchTarget 0x1036ae 6
          ((0xffffee7c : BitVec 32).signExtend 64) = 0x102530 := by decide +kernel
      simpa only [hlt, ↓reduceIte, beq_eq_false_iff_ne.mpr hne, Bool.not_false, htgt] using ht
    · have he : k + 1 = c.count := by omega
      have hei := congrArg c.input he
      have hn : (0x1036ae : BitVec 64) + BitVec.ofNat 64 6 = 0x1036b4 := by decide +kernel
      simpa only [hlt, ↓reduceIte, hei, BEq.rfl, Bool.not_true, Bool.false_eq_true, hn] using ht
  · have hre : (Operand.reg 6 : Operand 64).read t =
        (Operand.reg 6 : Operand 64).read s1 :=
      (he2.agrees.trans het.agrees).read (by simp [jccEffect, branchEffect_components])
    exact hre.trans hi1
  · exact (hAt.agrees.trans hal).mono (by simp [frameComponents, Machine.scratchComponents])
  · exact (hAt.agrees.trans hal).mono (by simp [frameComponents, Machine.scratchComponents])


theorem nextCorrect : NextCorrect := by
  intro bindings c hv k H s hk hReady hCode hRip hAt
  obtain ⟨n, t, ha, hr, hc, hp, hat, _⟩ :=
    nextAdvanceCorrect bindings (returnBoundary c.initial) c hv hv.outside k H s hk hReady hCode hRip hAt
  exact ⟨n, t, ha, hr, hc, hp, hat, by assumption⟩

end Sha1.Proofs.Compress.Routine
