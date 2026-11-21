import Md5.Proofs.Block.Entry
import X86Proofs.Instructions.Test.Generated.RR.Triple

namespace Md5.Proofs.Block

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

def OutsideCompression (address : BitVec 64) : Prop :=
  address.toNat < 0x101ba0 ∨ 0x102459 ≤ address.toNat

theorem outsideCompression_of_not_inProgram {address : BitVec 64}
    (h : ¬ InProgram address) : OutsideCompression address := by
  apply Classical.byContradiction
  intro hOutside
  have hLow : 0x101ba0 ≤ address.toNat := by
    unfold OutsideCompression at hOutside
    omega
  have hHigh : address.toNat < 0x102459 := by
    unfold OutsideCompression at hOutside
    omega
  have hSize : 0x2459 ≤ Extracted.textBytes.size := by decide +kernel
  have hOffset : address.toNat - 0x100000 < Extracted.textBytes.size := by omega
  have hAddress : Extracted.textAddress + BitVec.ofNat 64 (address.toNat - 0x100000) =
      address := by
    change BitVec.ofNat 64 0x100000 + BitVec.ofNat 64 (address.toNat - 0x100000) = address
    rw [← BitVec.ofNat_add,
      show 0x100000 + (address.toNat - 0x100000) = address.toNat by omega,
      BitVec.ofNat_toNat, BitVec.setWidth_eq]
  exact h (hAddress ▸ text_address_in_program _ hOffset)

theorem outsideCompression_ne {address pc : BitVec 64} (h : OutsideCompression address)
    (hLow : 0x101ba0 ≤ pc.toNat) (hHigh : pc.toNat < 0x102459) : pc ≠ address := by
  intro hEq
  subst pc
  unfold OutsideCompression at h
  omega

theorem compression_nonempty [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hEntry : s.RIP = 0x101ba0) (hCount : s.regValue .rdx ≠ 0)
    (hBoundary : OutsideCompression boundary.rip) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = 0x101ba9 ∧ AgreesExcept [.flags, .rip] s t := by
  have hBytes : CodeIn (codeRange 0x101ba0 [0x48, 0x85, 0xd2]) s :=
    program_text_slice hCode 0x1ba0 3 (by decide +kernel)
  have hTest : StepEffect (fun s ↦ s.RIP = 0x101ba0)
      (codeRange 0x101ba0 [0x48, 0x85, 0xd2]) (testR64R64Effect 0x101ba0 2 2) :=
    test_r64_r64_effect_step _ _ _ (by unfold RexWPrefix; decide) (by decide)
  obtain ⟨u, hAdvance, hReady', hEffect⟩ := hTest.advances hReady hBytes hEntry
    (outsideCompression_ne (pc := 0x101ba3) hBoundary (by decide) (by decide))
  have hCode' := hEffect.codeIn (testR64R64Effect_avoids _ _ _ _ _) hCode
  have hZero : (StatusFlags.ofRFLAGS u.RFLAGS).ZF = false := by
    have hz := hEffect.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS u.RFLAGS).ZF =
      ((s.regValue .rdx &&& s.regValue .rdx) == 0) at hz
    simpa only [BitVec.and_self, beq_eq_false_iff_ne.mpr hCount] using hz
  have hCond : condHolds 4 (StatusFlags.ofRFLAGS u.RFLAGS) = false := hZero
  have hBranchBytes : CodeIn (codeRange 0x101ba3 [0x0f, 0x84, 0xaf, 0x08, 0x00, 0x00]) u :=
    program_text_slice hCode' 0x1ba3 6 (by decide +kernel)
  have hBranch := jcc_rel32_effect_step 0x101ba3 4 0x8af
  have hPre : u.RIP = 0x101ba3 ∧
      (condHolds 4 (StatusFlags.ofRFLAGS u.RFLAGS) = true →
        (branchTarget 0x101ba3 6 ((0x8af#32).signExtend 64)).toNat < 2^32) :=
    ⟨hEffect.rip, fun _ ↦ by decide +kernel⟩
  have hNext : (jccEffect 0x101ba3 6 4 ((0x8af#32).signExtend 64) u).rip = 0x101ba9 := by
    simp only [jccEffect, hCond, branchEffect]
    rfl
  have hNextNe : (jccEffect 0x101ba3 6 4 ((0x8af#32).signExtend 64) u).rip ≠
      boundary.rip := by
    rw [hNext]
    exact outsideCompression_ne hBoundary (by decide) (by decide)
  obtain ⟨t, hAdvance', hReady'', hEffect'⟩ := hBranch.advances (boundary := boundary)
    hReady' hBranchBytes hPre hNextNe
  have hNop := jccEffect_not_taken hCond hEffect'
  refine ⟨t, hAdvance.trans hAdvance', hReady'',
    hNop.codeIn (nopEffect_avoids _ _ _) hCode', hEffect'.rip.trans hNext, ?_⟩
  apply (hEffect.agrees.trans hNop.agrees).mono
  intro c hc
  change c ∈ [.flags, .rip] ++ [.rip] at hc
  simpa only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false, or_self] using hc

end Md5.Proofs.Block
