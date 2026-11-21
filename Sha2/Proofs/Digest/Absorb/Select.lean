import Sha2.Proofs.Common.SHA256.Blocks.Digest.Absorb
import Sha2.Proofs.Wrapper512.Variant

set_option autoImplicit false

namespace Sha2.Proofs.Digest.Absorb

open Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field Sha2.Proofs.Common.Machine
open Sha2.Proofs.Wrapper512

def selectBytes : List UInt8 := [0x49,0x83,0xfe,0x7f,0x77,0x1b]

def selectEffect (p : BitVec 64) (s : RamState) : Effect :=
  { rip := if (s.regValue .r14).toNat ≤ 127 then p + 6 else p + 33,
    flags := some ⟨none,none,none,none,none,none⟩ }

theorem select_code (v : Variant) {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange (v.pc 0xca .digest) selectBytes) s := by
  apply programText_slice (programLoaded_codeIn loaded) (v.textOffset .digest + 0xca)
  · cases v <;> decide +kernel
  · cases v <;> decide +kernel

theorem select_run [Bindings] (p : BitVec 64) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) (inside : BlockInProgram p selectBytes.length)
    (target : InProgram (p + 33)) :
    AdvanceTriple boundary (fun s => s.RIP = p) (codeRange p selectBytes)
      (Effect.post (selectEffect p)) := by
  intro s ready loaded pre
  have cmpCode : CodeIn (codeRange p [0x49,0x83,0xfe,0x7f]) s := by
    apply loaded.mono
    x86_sub
  obtain ⟨t, cmpStep, readyT, cmp⟩ := (cmp_r64_imm8_effect_step
    p 0x49 0xfe 127 (by simp [RexWPrefix]) rfl rfl).advances
    (boundary := boundary) ready cmpCode pre
    (boundary_ne_program outside (inside 4 (by decide)))
  have loadedT : CodeIn (codeRange p selectBytes) t :=
    cmp.codeIn (by
      apply Effect.Avoids.of_noMem
      simp [cmpR64Imm8Effect, Effect.components, Component.Covers]) loaded
  have branchCode : CodeIn (codeRange (p + 4) [0x77,0x1b]) t := by
    apply loadedT.mono
    x86_sub
  have low : (branchTarget (p + 4) 2 ((27 : BitVec 8).signExtend 64)).toNat < 2^32 := by
    obtain ⟨byte, mem⟩ := target
    have bound := programSections_low.codeLow (_, byte) mem
    simpa [branchTarget, BitVec.add_assoc, Prelude.userAddressLimit] using bound
  obtain ⟨u, branchStep, readyU, branch⟩ := jcc_rel8_effect_step (p + 4) 7 27
    t readyT branchCode ⟨cmp.rip, fun _ => low⟩
  have cf : (StatusFlags.ofRFLAGS t.RFLAGS).CF = (s.regValue .r14).ult 127 := cmp.flags.1
  have zf : (StatusFlags.ofRFLAGS t.RFLAGS).ZF = (s.regValue .r14 - 127 == 0) := cmp.flags.2.2.2.1
  have choose : (!((s.regValue .r14).ult 127 || (s.regValue .r14 - 127 == 0))) =
      decide (¬ (s.regValue .r14).toNat ≤ 127) := by
    have eq : (s.regValue .r14 - 127 == 0) = decide ((s.regValue .r14).toNat = 127) := by
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq, decide_eq_true_eq, BitVec.sub_eq_iff_eq_add, BitVec.reduceAdd]
      constructor
      · exact congrArg BitVec.toNat
      · intro h
        exact BitVec.eq_of_toNat_eq h
    rw [eq]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.not_eq_true', Bool.or_eq_false_iff, BitVec.ult_eq_decide,
      decide_eq_false_iff_not, BitVec.reduceToNat, decide_eq_true_eq]
    omega
  have rip : u.RIP = (selectEffect p s).rip := by
    rw [branch.rip]
    change (if !((StatusFlags.ofRFLAGS t.RFLAGS).CF || (StatusFlags.ofRFLAGS t.RFLAGS).ZF)
      then branchTarget (p + 4) 2 ((27 : BitVec 8).signExtend 64) else (p + 4) + 2) = _
    rw [cf, zf, choose]
    by_cases small : (s.regValue .r14).toNat ≤ 127 <;>
      simp [selectEffect, small, branchTarget, BitVec.add_assoc]
  have run : Advances boundary 1 t u := by
    apply Advances.of_step branchStep
    left
    rw [rip]
    change (if (s.regValue .r14).toNat ≤ 127 then p + 6 else p + 33) ≠ boundary.rip
    split
    · exact boundary_ne_program outside (inside 6 (by decide))
    · exact boundary_ne_program outside target
  refine ⟨2, u, cmpStep.trans run, readyU, ?_, rip, trivial, ?_, ?_⟩
  · exact branch.codeIn (branchEffect_avoids _ _ _ _) loadedT
  · exact ⟨trivial,trivial,trivial,trivial,trivial,trivial⟩
  · apply (cmp.agrees.trans branch.agrees).mono
    simp [cmpR64Imm8Effect, jccEffect, branchEffect, selectEffect, Effect.components]


end Sha2.Proofs.Digest.Absorb
