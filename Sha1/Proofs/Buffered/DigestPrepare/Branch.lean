import Sha1.Proofs.Buffered.DigestPrepare.Contracts
import Sha1.Proofs.Compress.Machine.Code
import Sha1.Proofs.Buffered.Finalize.Geometry
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Branch.Triple

namespace Sha1.Proofs.Buffered.DigestPrepare

open Sha1.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs Sha1.Proofs.Compress.Machine
open Sha1.Proofs.Buffered.Finalize (text_address_ne_return rangeApart_text)

theorem branch_condition (size : Nat) (hSize : size < 2^64) :
    condHolds 7 (cmpSpec (BitVec.ofNat 64 size) 63) = decide (64 ≤ size) := by
  change Bool.not (decide ((BitVec.ofNat 64 size).toNat < 63) ||
    ((BitVec.ofNat 64 size - 63) == 0)) = decide (64 ≤ size)
  have hn : (BitVec.ofNat 64 size).toNat = size := Nat.mod_eq_of_lt hSize
  have hz : (BitVec.ofNat 64 size - (63 : BitVec 64) = 0) ↔ size = 63 := by
    constructor
    · intro hz
      have hh := congrArg BitVec.toNat hz
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.reduceToNat] at hh
      omega
    · intro hz
      subst size
      decide
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not,
    beq_eq_false_iff_ne, decide_eq_true_eq, hn, Bool.not_eq_eq_eq_not, Bool.not_true,
    BitVec.ofNat_eq_ofNat]
  change (¬ size < 63 ∧ ¬ (BitVec.ofNat 64 size - (63 : BitVec 64)) = 0) ↔ 64 ≤ size
  rw [hz]
  omega

theorem entry_branch [Bindings] {boundary : ReturnBoundary} {s : RamState} {size : Nat}
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hOutside : ¬ InProgram boundary.rip) (hRip : s.RIP = 0x100072)
    (hSize : size < 2^64)
    (hLength : (Operand.reg 15 : Operand 64).read s = BitVec.ofNat 64 size) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = (if 64 ≤ size then 0x100093 else 0x100078) ∧
      AgreesExcept [.flags, .rip] s t := by
  have hCmp := cmp_r64_imm8_effect_step 0x100072 0x49 0xff 63
    (by unfold RexWPrefix; decide) (by decide) (by decide)
  have hBytes : CodeIn (codeRange 0x100072 [0x49, 0x83, 0xff, 63]) s :=
    program_text_slice hCode 0x72 4 (by decide +kernel)
  obtain ⟨u, ha, hu, he⟩ := hCmp.advances hReady hBytes hRip
    (text_address_ne_return hOutside 0x76 (by decide +kernel))
  have hcu := he.codeIn (cmpR64Imm8Effect_avoids _ _ _ _ _) hCode
  have hCond : condHolds 7 (StatusFlags.ofRFLAGS u.RFLAGS) = decide (64 ≤ size) := by
    change Bool.not ((StatusFlags.ofRFLAGS u.RFLAGS).CF || (StatusFlags.ofRFLAGS u.RFLAGS).ZF) = _
    rw [he.flags.1, he.flags.2.2.2.1]
    change condHolds 7 (cmpSpec ((Operand.reg 15 : Operand 64).read s) 63) = _
    rw [hLength]
    exact branch_condition size hSize
  have hBranchBytes : CodeIn (codeRange 0x100076 [0x77, 0x1b]) u :=
    program_text_slice hcu 0x76 2 (by decide +kernel)
  have hNext : (jccEffect 0x100076 2 7 ((0x1b#8).signExtend 64) u).rip =
      (if 64 ≤ size then 0x100093 else 0x100078) := by
    simp only [jccEffect, branchEffect, hCond, decide_eq_true_eq]
    rfl
  have hNotBoundary : (jccEffect 0x100076 2 7 ((0x1b#8).signExtend 64) u).rip ≠
      boundary.rip := by
    rw [hNext]
    split
    · exact text_address_ne_return hOutside 0x93 (by decide +kernel)
    · exact text_address_ne_return hOutside 0x78 (by decide +kernel)
  obtain ⟨t, hb, ht, he'⟩ := (jcc_rel8_effect_step 0x100076 7 0x1b).advances
    hu hBranchBytes ⟨he.rip, fun _ ↦ by decide +kernel⟩ hNotBoundary
  refine ⟨t, ha.trans hb, ht,
    he'.codeIn (branchEffect_avoids _ _ _ _) hcu, he'.rip.trans hNext, ?_⟩
  apply (he.agrees.trans he'.agrees).mono
  intro c hc
  simpa only [cmpR64Imm8Effect_components, jccEffect, branchEffect_components,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_self, or_assoc] using hc

end Sha1.Proofs.Buffered.DigestPrepare
