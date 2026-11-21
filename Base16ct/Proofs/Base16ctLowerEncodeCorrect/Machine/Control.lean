import Base16ct.Proofs.Base16ctLowerEncodeCorrect.Machine.Interface
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Branch.Triple

namespace Base16ct.Proofs.LowerEncode

open Base16ct.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem cmp_unsigned_le {n : Nat} (x y : BitVec n) :
    condHolds 6 (cmpSpec x y) = decide (x.toNat ≤ y.toNat) := by
  change (decide (x.toNat < y.toNat) || (x - y == 0)) = decide (x.toNat ≤ y.toNat)
  apply Bool.eq_iff_iff.mpr
  have hz : (0 : BitVec n) + y = y := by simp
  simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq,
    BitVec.sub_eq_iff_eq_add, hz]
  rw [← BitVec.toNat_inj]
  omega

def capacityCheckEffect (s : RamState) : Effect :=
  { rip := if ((Operand.reg 2 : Operand 64).read s +
        (Operand.reg 2 : Operand 64).read s).toNat ≤ ((Operand.reg 8 : Operand 64).read s).toNat
      then 0x100548 else 0x10053c
    writes := [⟨(.reg 0 : Operand 64), (Operand.reg 7 : Operand 64).read s⟩,
      ⟨(.reg 7 : Operand 64), (Operand.reg 2 : Operand 64).read s +
        (Operand.reg 2 : Operand 64).read s⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem capacity_check_run [Bindings] {boundary : ReturnBoundary}
    (hOutside : ¬ InProgram boundary.rip) {s : RamState}
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hRip : s.RIP = 0x100530) :
    ∃ t, Advances boundary 4 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      (capacityCheckEffect s).Holds s t := by
  have hMovCode : CodeIn (codeRange 0x100530 [0x48, 0x89, 0xf8]) s :=
    program_text_slice hCode 0x530 3 (by decide +kernel)
  obtain ⟨a, hRun₁, hReady₁, hMov⟩ :=
    (mov_r64_r64_effect_step 0x100530 0x48 0xf8 (by simp [RexWPrefix]) (by decide)).advances
      hReady hMovCode hRip (text_address_ne_return hOutside 0x533 (by decide +kernel))
  change (movR64R64Effect 0x100530 0 7 s).Holds s a at hMov
  have hCode₁ := hMov.agrees.codeIn (by simp [Effect.components, movR64R64Effect,
    Component.Covers]) hCode
  have hLeaCode : CodeIn (codeRange 0x100533 [0x48, 0x8d, 0x3c, 0x12]) a :=
    program_text_slice hCode₁ 0x533 4 (by decide +kernel)
  obtain ⟨b, hRun₂, hReady₂, hLea⟩ :=
    (lea_r64_effect_step 0x100533 0x48 (by simp [RexWPrefix]) 7
      (.sib 2 (some 2) 0 .none) ⟨by decide, fun _ => by decide⟩
      (by decide) (by decide)).advances
      hReady₁ hLeaCode hMov.rip
      (text_address_ne_return hOutside 0x537 (by decide +kernel))
  change (leaR64Effect 0x100533 7 (.sib 2 (some 2) 0 .none) a).Holds a b at hLea
  have hCode₂ := hLea.agrees.codeIn (by simp [Effect.components, leaR64Effect,
    Component.Covers]) hCode₁
  have hCmpCode : CodeIn (codeRange 0x100537 [0x4c, 0x39, 0xc7]) b :=
    program_text_slice hCode₂ 0x537 3 (by decide +kernel)
  obtain ⟨c, hRun₃, hReady₃, hCmp⟩ :=
    (cmp_r64_r64_effect_step 0x100537 0x4c 0xc7 (by simp [RexWPrefix]) (by decide)).advances
      hReady₂ hCmpCode hLea.rip
      (text_address_ne_return hOutside 0x53a (by decide +kernel))
  change (cmpR64R64Effect 0x100537 7 8 b).Holds b c at hCmp
  have hCode₃ := hCmp.agrees.codeIn (by simp [Component.Covers]) hCode₂
  have hRdx : (Operand.reg 2 : Operand 64).read a = (Operand.reg 2 : Operand 64).read s :=
    hMov.agrees.read (by simp)
  have hRdi : (Operand.reg 7 : Operand 64).read b =
      (Operand.reg 2 : Operand 64).read s + (Operand.reg 2 : Operand 64).read s := by
    have hv : (Operand.reg 7 : Operand 64).read b =
        (Operand.reg 2 : Operand 64).read a + (Operand.reg 2 : Operand 64).read a := by
      simpa [leaR64Effect, Write.AllHold, AddrMode.addr, AddrMode.reg64, Disp.value]
        using hLea.writes
    simpa only [hRdx] using hv
  have hR8 : (Operand.reg 8 : Operand 64).read b = (Operand.reg 8 : Operand 64).read s :=
    (hLea.agrees.read (by simp)).trans (hMov.agrees.read (by simp))
  have hFlags : condHolds 6 (StatusFlags.ofRFLAGS c.RFLAGS) =
      decide (((Operand.reg 2 : Operand 64).read s +
        (Operand.reg 2 : Operand 64).read s).toNat ≤
        ((Operand.reg 8 : Operand 64).read s).toNat) := by
    have hCF := hCmp.flags.1
    have hZF := hCmp.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS c.RFLAGS).CF =
      (cmpSpec ((Operand.reg 7 : Operand 64).read b)
        ((Operand.reg 8 : Operand 64).read b)).CF at hCF
    change (StatusFlags.ofRFLAGS c.RFLAGS).ZF =
      (cmpSpec ((Operand.reg 7 : Operand 64).read b)
        ((Operand.reg 8 : Operand 64).read b)).ZF at hZF
    change ((StatusFlags.ofRFLAGS c.RFLAGS).CF || (StatusFlags.ofRFLAGS c.RFLAGS).ZF) = _
    rw [hCF, hZF]
    change condHolds 6 (cmpSpec _ _) = _
    rw [cmp_unsigned_le, hRdi, hR8]
  have hNext : (jccEffect 0x10053a 2 6 ((12#8).signExtend 64) c).rip =
      (capacityCheckEffect s).rip := by
    simp only [jccEffect, branchEffect, hFlags, capacityCheckEffect, decide_eq_true_eq]
    rfl
  have hBoundary : (capacityCheckEffect s).rip ≠ boundary.rip := by
    unfold capacityCheckEffect
    split
    · exact text_address_ne_return hOutside 0x548 (by decide +kernel)
    · exact text_address_ne_return hOutside 0x53c (by decide +kernel)
  have hJumpCode : CodeIn (codeRange 0x10053a [0x76, 0x0c]) c :=
    program_text_slice hCode₃ 0x53a 2 (by decide +kernel)
  obtain ⟨t, hRun₄, hReady₄, hJump⟩ :=
    (jcc_rel8_effect_step 0x10053a 6 12).advances hReady₃ hJumpCode
      ⟨hCmp.rip, fun _ => by decide +kernel⟩ (hNext ▸ hBoundary)
  have hAgrees : AgreesExcept [.rip] c t := hJump.agrees
  refine ⟨t, ((hRun₁.trans hRun₂).trans hRun₃).trans hRun₄, hReady₄,
    hAgrees.codeIn (by simp [Component.Covers]) hCode₃, hJump.rip.trans hNext, ?_, ?_, ?_⟩
  · constructor
    · exact (hAgrees.read (n := 64) (r := 0) (by simp)).trans
        ((hCmp.agrees.read (by simp)).trans ((hLea.agrees.read (by simp)).trans hMov.writes))
    · exact (hAgrees.read (n := 64) (r := 7) (by simp)).trans
        ((hCmp.agrees.read (by simp)).trans hRdi)
  · simp [capacityCheckEffect, Effect.FlagsHold, StatusFlagsOutcome.Allows, FlagAllows]
  · apply (((hMov.agrees.trans hLea.agrees).trans hCmp.agrees).trans hAgrees).mono
    simp [capacityCheckEffect, Effect.components, movR64R64Effect, leaR64Effect,
      cmpR64R64Effect]

end Base16ct.Proofs.LowerEncode
