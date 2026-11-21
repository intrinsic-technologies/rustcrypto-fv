import Sha2.Proofs.Wrapper.Absorb.Blocks.State
import Sha2.Proofs.Wrapper.Absorb.Arithmetic
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper.Absorb.Blocks

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

def countPC (empty : Bool) (v : Variant := .sha256) : BitVec 64 := if empty then (v.pc 0x1b0) else (v.pc 0x14c)

set_option maxHeartbeats 800000 in
theorem select [Bindings] {v : Variant} {initial s : RamState} {inputs : Array Program.Input}
    {index consumed : Nat} (ctx : Context (v := v) initial inputs)
    (input : Input (v := v) initial s inputs index consumed) (empty : Bool)
    (rip : s.RIP = countPC empty v) :
    ∃ t, Input (v := v) initial t inputs index consumed ∧
      t.regValue .rdx = BitVec.ofNat 64 (((inputs[index]'input.remaining).bytes.size - consumed) / 64) ∧
      t.RIP = if ((inputs[index]'input.remaining).bytes.size - consumed) / 64 = 0
        then (v.pc 0x16d) else (v.pc 0x155) := by
  have outside := (validCall_returnBoundary ctx.machine ctx.call).2.2
  obtain ⟨u,runU,readyU,mov⟩ :=
    (mov_r64_r64_effect_step (countPC empty v) 0x48 0xea (by simp [RexWPrefix]) rfl).advances
      (supportedMachine_readyToStep input.machine)
      (by cases empty
          · exact programText_slice (programLoaded_codeIn input.loaded) (v.textOffset + 0x14c) _ (by cases v <;> decide) (by cases v <;> decide +kernel)
          · exact programText_slice (programLoaded_codeIn input.loaded) (v.textOffset + 0x1b0) _ (by cases v <;> decide) (by cases v <;> decide +kernel)) rip
      (by
        change countPC empty v + BitVec.ofNat 64 3 ≠ (returnBoundary initial).rip
        cases empty <;> simp only [countPC, Bool.false_eq_true, ↓reduceIte, Variant.pc_add]
        · exact boundary_ne_program outside (Variant.pc_inProgram v (by decide))
        · exact boundary_ne_program outside (Variant.pc_inProgram v (by decide)))
  change (movR64R64Effect (countPC empty v) 2 5 s).Holds s u at mov
  have uInput := input.of_agrees ctx runU readyU mov.agrees
    (by simp [Component.Covers]) (by simp)
  obtain ⟨mid,runV,readyV,shr⟩ :=
    (shr_r64_imm8_effect_step (countPC empty v + 3) 0x48 0xea 6 (by simp [RexWPrefix]) rfl rfl).advances
      readyU (by
        cases empty
        · change CodeIn (codeRange (v.pc 0x14c + BitVec.ofNat 64 3) [0x48,0xc1,0xea,6]) u
          rw [Variant.pc_add]
          exact programText_slice (programLoaded_codeIn uInput.loaded) (v.textOffset + 0x14f) _
            (by cases v <;> decide) (by cases v <;> decide +kernel)
        · change CodeIn (codeRange (v.pc 0x1b0 + BitVec.ofNat 64 3) [0x48,0xc1,0xea,6]) u
          rw [Variant.pc_add]
          exact programText_slice (programLoaded_codeIn uInput.loaded) (v.textOffset + 0x1b3) _
            (by cases v <;> decide) (by cases v <;> decide +kernel)) mov.rip
      (by
        change (countPC empty v + BitVec.ofNat 64 3) + BitVec.ofNat 64 4 ≠ (returnBoundary initial).rip
        cases empty <;> simp only [countPC, Bool.false_eq_true, ↓reduceIte, Variant.pc_add]
        · exact boundary_ne_program outside (Variant.pc_inProgram v (by decide))
        · exact boundary_ne_program outside (Variant.pc_inProgram v (by decide)))
  change (shrR64Effect (countPC empty v+3) 4 2 6 u).Holds u mid at shr
  have vInput := uInput.of_agrees ctx runV readyV shr.agrees
    (by simp [Component.Covers]) (by simp)
  have bounded := validCall_input_bounded ctx.call (⟨index,input.remaining⟩ : Fin inputs.size)
  have lengthNat : (s.regValue .rbp).toNat = (inputs[index]'input.remaining).bytes.size-consumed := by
    rw [input.length,BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
    change (inputs[index]'input.remaining).address.toNat + (inputs[index]'input.remaining).bytes.size < 2^32 at bounded
    omega
  have shifted : u.regValue .rdx >>> 6 =
      BitVec.ofNat 64 (((inputs[index]'input.remaining).bytes.size-consumed)/64) := by
    have value : u.regValue .rdx = s.regValue .rbp := mov.writes
    rw [value, block_count, lengthNat]
  have count : mid.regValue .rdx =
      BitVec.ofNat 64 (((inputs[index]'input.remaining).bytes.size-consumed)/64) :=
    shr.writes.trans shifted
  have zero : (StatusFlags.ofRFLAGS mid.RFLAGS).ZF =
      decide (((inputs[index]'input.remaining).bytes.size-consumed)/64 = 0) := by
    change _ = _
    rw [shr.flags.2.2.2.1]
    change (u.regValue .rdx >>> 6 == 0) = _
    rw [shifted]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq,decide_eq_true_eq]
    constructor
    · intro h
      have hn := congrArg BitVec.toNat h
      change (((inputs[index]'input.remaining).bytes.size-consumed)/64) % 2^64 = 0 at hn
      have sn := BitVec.isLt (s.regValue .rbp)
      rw [lengthNat] at sn
      omega
    · intro h
      rw [h]
      rfl
  obtain ⟨w,stepW,readyW,branch⟩ := jcc_rel8_effect_step (countPC empty v+7)
    (if empty then 5 else 4) (if empty then 0x9c else 0x18) mid readyV
    (by
      cases empty
      · change CodeIn (codeRange (v.pc 0x14c + BitVec.ofNat 64 7) [0x74,0x18]) mid
        rw [Variant.pc_add]
        exact programText_slice (programLoaded_codeIn vInput.loaded) (v.textOffset + 0x153) _
          (by cases v <;> decide) (by cases v <;> decide +kernel)
      · change CodeIn (codeRange (v.pc 0x1b0 + BitVec.ofNat 64 7) [0x75,0x9c]) mid
        rw [Variant.pc_add]
        exact programText_slice (programLoaded_codeIn vInput.loaded) (v.textOffset + 0x1b7) _
          (by cases v <;> decide) (by cases v <;> decide +kernel))
    ⟨shr.rip.trans (by cases empty <;> cases v <;> rfl),
      by cases empty <;> cases v <;> exact fun _ => by decide⟩
  have target : w.RIP = if ((inputs[index]'input.remaining).bytes.size-consumed)/64 = 0
      then (if empty then (v.pc 0x1b9) else (v.pc 0x16d)) else (v.pc 0x155) := by
    rw [branch.rip]
    by_cases hz : ((inputs[index]'input.remaining).bytes.size-consumed)/64 = 0
    all_goals cases empty <;> cases v <;>
      simp [jccEffect, branchEffect, condHolds, countPC, Variant.pc, Variant.textOffset, Extracted.textAddress, branchTarget, zero, hz]
  have runW : Advances (returnBoundary initial) 1 mid w := by
    apply Advances.of_step stepW
    left
    rw [target]
    split
    · cases empty
      · exact boundary_ne_program outside (inProgram_of_textOffset (v.textOffset + 0x16d) (by cases v <;> decide))
      · exact boundary_ne_program outside (inProgram_of_textOffset (v.textOffset + 0x1b9) (by cases v <;> decide))
    · exact boundary_ne_program outside (inProgram_of_textOffset (v.textOffset + 0x155) (by cases v <;> decide))
  have wInput := vInput.of_agrees ctx runW readyW branch.agrees
    (by simp [jccEffect,Component.Covers]) (by simp [jccEffect]) (by simp [jccEffect])
  have countW := (branch.agrees.read (n := 64) (r := 2) (by simp [jccEffect])).trans count
  by_cases hzero : ((inputs[index]'input.remaining).bytes.size-consumed)/64 = 0
  · cases empty
    · exact ⟨w,wInput,countW,by simpa [hzero] using target⟩
    · have ripW : w.RIP = (v.pc 0x1b9) := by simpa [hzero] using target
      obtain ⟨t,runT,readyT,jump⟩ := (jmp_rel8_effect_step (v.pc 0x1b9) 0xb2 (by cases v <;> decide)).advances
        readyW (programText_slice (programLoaded_codeIn wInput.loaded) (v.textOffset + 0x1b9) _
          (by cases v <;> decide) (by cases v <;> decide +kernel)) ripW
        (by
          cases v
          · exact boundary_ne_program outside (inProgram_of_textOffset 0x41d (by decide))
          · exact boundary_ne_program outside (inProgram_of_textOffset 0x201d (by decide)))
      exact ⟨t,wInput.of_agrees ctx runT readyT jump.agrees
          (by simp [Component.Covers]) (by simp),
        (jump.agrees.read (n := 64) (r := 2) (by simp)).trans countW,
        by cases v <;> simpa [hzero,jmpEffect,branchTarget, Variant.pc, Variant.textOffset, Extracted.textAddress] using jump.rip⟩
  · exact ⟨w,wInput,countW,by simpa [hzero] using target⟩

end Sha2.Proofs.Wrapper.Absorb.Blocks
