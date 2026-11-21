import Sha2.Proofs.Wrapper512.Absorb.Large.Blocks.State
import Sha2.Proofs.Wrapper512.Absorb.Arithmetic
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Absorb.Large.Blocks

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine
open Sha2.Proofs.Wrapper512.Absorb.Blocks

def countOffset (variant : Variant) (empty : Bool) (form : Form := .slices) : Nat :=
  if empty then (variant.traversal form).exit - 11 else (variant.traversal form).blocksCall - 37

def countPC (variant : Variant) (empty : Bool) (form : Form := .slices) : BitVec 64 :=
  variant.pc (countOffset variant empty form) form

def tailOffset (variant : Variant) (form : Form := .slices) : Nat :=
  (variant.traversal form).blocksCall +
    if (variant.traversal form).dataReg = 6 then 8 else 5

def tailPC (variant : Variant) (form : Form := .slices) : BitVec 64 :=
  variant.pc (tailOffset variant form) form

def compressPC (variant : Variant) (form : Form := .slices) : BitVec 64 :=
  countPC variant false form + (9 : BitVec 64)

private def selectRex (variant : Variant) (form : Form) : UInt8 :=
  if variant.restRegister form < 8 then 0x48 else 0x4c

private def selectModrm (variant : Variant) (form : Form) : UInt8 :=
  UInt8.ofNat (0xc2 + 8 * ((variant.restRegister form).toNat % 8))

private def selectDisp (variant : Variant) (empty : Bool) (form : Form) : BitVec 8 :=
  ((if empty then compressPC variant form else tailPC variant form) -
    (countPC variant empty form + (9 : BitVec 64))).setWidth 8

private def jumpDisp (variant : Variant) (form : Form) : BitVec 8 :=
  (tailPC variant form - (countPC variant true form + (11 : BitVec 64))).setWidth 8

macro "select_finite" form:ident variant:ident : tactic => `(tactic|
  (cases ($form) with
   | slices => cases ($variant) <;> decide +kernel
   | digest => contradiction
   | reset stage =>
     have h : stage = 0 ∨ stage = 1 ∨ stage = 2 := by omega
     rcases h with h | h | h <;> rw [h] <;> cases ($variant) <;> decide +kernel
   | finalizeIntoReset b | traitFinalizeIntoReset b => cases b <;> cases ($variant) <;> decide +kernel))

set_option maxRecDepth 2048 in
set_option maxHeartbeats 2000000 in
theorem select [Bindings] {variant : Variant} {form : Form} {initial s : RamState} {inputs : Array Program.Input}
    {index consumed : Nat} (ctx : Context variant initial inputs form)
    (input : Input variant initial s inputs index consumed form) (empty : Bool)
    (rip : s.RIP = countPC variant empty form) (eligible : form ≠ .digest) :
    ∃ t, Input variant initial t inputs index consumed form ∧
      t.regValue .rdx = BitVec.ofNat 64 (((inputs[index]'input.remaining).bytes.size - consumed) / 128) ∧
      (t.RIP = if ((inputs[index]'input.remaining).bytes.size - consumed) / 128 = 0
        then tailPC variant form else compressPC variant form) ∧
      (∃ fuel, Advances (returnBoundary initial) fuel s t) ∧
      MemoryWriteFrame s t #v[Stack.region initial (variant.routine form).minStackBytes] := by
  have outside := (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2
  have inside (n : Nat) (hn : n ≤ 11) :
      countPC variant empty form + BitVec.ofNat 64 n ≠ (returnBoundary initial).rip := by
    apply boundary_ne_program outside
    change InProgram (variant.pc (countOffset variant empty form) form + BitVec.ofNat 64 n)
    rw [Variant.pc_add variant _ _ form]
    apply inProgram_of_textOffset
    have h : variant.textOffset form + countOffset variant empty form + 11 < 71757 := by
      cases empty <;> select_finite form variant
    omega
  have kept (r : BitVec 5)
      (hr : r ∈ ([4, 3, 5, 12, 13, 14, variant.restRegister form,
        BitVec.ofNat 5 (variant.traversal form).dataReg,
        BitVec.ofNat 5 (variant.traversal form).indexReg,
        BitVec.ofNat 5 ((variant.traversal form).countReg.getD 0)] : List (BitVec 5))) : r ≠ 2 := by
    have h : ∀ r ∈ ([4, 3, 5, 12, 13, 14, variant.restRegister form,
        BitVec.ofNat 5 (variant.traversal form).dataReg,
        BitVec.ofNat 5 (variant.traversal form).indexReg,
        BitVec.ofNat 5 ((variant.traversal form).countReg.getD 0)] : List (BitVec 5)), r ≠ 2 := by
      select_finite form variant
    exact h r hr
  obtain ⟨u,runU,readyU,mov⟩ :=
    (mov_r64_r64_effect_step (countPC variant empty form)
      (selectRex variant form) (selectModrm variant form)
      (by unfold RexWPrefix; select_finite form variant) (by select_finite form variant)).advances
      (supportedMachine_readyToStep input.machine)
      (by
        apply programText_slice (programLoaded_codeIn input.loaded)
          (variant.textOffset form + countOffset variant empty form)
        · cases empty <;> select_finite form variant
        · cases empty <;> select_finite form variant) rip (inside 3 (by omega))
  have dst : gprNumber 0 (rexB (selectRex variant form).toBitVec)
      (modrmRm (selectModrm variant form)) = 2 := by select_finite form variant
  have source : gprNumber 0 (rexR (selectRex variant form).toBitVec)
      (modrmReg (selectModrm variant form)) = variant.restRegister form := by select_finite form variant
  rw [dst, source] at mov
  have uInput := input_of_agrees ctx input runU readyU mov.agrees
    (by simp [Component.Covers]) (by simpa using kept)
    (by simp) (by simp) (by intro h; subst form; left; cases variant <;> simp)
  obtain ⟨v,runV,readyV,shr⟩ :=
    (shr_r64_imm8_effect_step (countPC variant empty form + (3 : BitVec 64)) 0x48 0xea 7
      (by simp [RexWPrefix]) rfl rfl).advances readyU
      (by
        change CodeIn (codeRange (variant.pc (countOffset variant empty form) form + BitVec.ofNat 64 3) _) u
        rw [Variant.pc_add variant _ _ form]
        apply programText_slice (programLoaded_codeIn uInput.loaded)
          (variant.textOffset form + (countOffset variant empty form + 3))
        · cases empty <;> select_finite form variant
        · cases empty <;> select_finite form variant) mov.rip
      (by
        change (countPC variant empty form + (3 : BitVec 64)) + 4 ≠ (returnBoundary initial).rip
        rw [BitVec.add_assoc]; exact inside 7 (by omega))
  change (shrR64Effect (countPC variant empty form+ (3 : BitVec 64)) 4 2 7 u).Holds u v at shr
  have vInput := input_of_agrees ctx uInput runV readyV shr.agrees
    (by simp [Component.Covers]) (by simpa using kept)
    (by simp) (by simp) (by intro h; subst form; left; cases variant <;> simp)
  have bounded := (ctx.inputInMemory (⟨index,input.remaining⟩ : Fin inputs.size)).2.1
  have lengthNat : ((.reg (variant.restRegister form) : Operand 64).read s).toNat =
      (inputs[index]'input.remaining).bytes.size-consumed := by
    rw [input.length,BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
    change (inputs[index]'input.remaining).address.toNat + (inputs[index]'input.remaining).bytes.size < 2^32 at bounded
    omega
  have shifted : u.regValue .rdx >>> 7 =
      BitVec.ofNat 64 (((inputs[index]'input.remaining).bytes.size-consumed)/128) := by
    have value : u.regValue .rdx = (.reg (variant.restRegister form) : Operand 64).read s := mov.writes
    rw [value, block_count, lengthNat]
  have count : v.regValue .rdx =
      BitVec.ofNat 64 (((inputs[index]'input.remaining).bytes.size-consumed)/128) :=
    shr.writes.trans shifted
  have zero : (StatusFlags.ofRFLAGS v.RFLAGS).ZF =
      decide (((inputs[index]'input.remaining).bytes.size-consumed)/128 = 0) := by
    change _ = _
    rw [shr.flags.2.2.2.1]
    change (u.regValue .rdx >>> 7 == 0) = _
    rw [shifted]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq,decide_eq_true_eq]
    constructor
    · intro h
      have hn := congrArg BitVec.toNat h
      change (((inputs[index]'input.remaining).bytes.size-consumed)/128) % 2^64 = 0 at hn
      have sn := BitVec.isLt ((.reg (variant.restRegister form) : Operand 64).read s)
      rw [lengthNat] at sn
      omega
    · intro h
      rw [h]
      rfl
  obtain ⟨w,stepW,readyW,branch⟩ := jcc_rel8_effect_step (countPC variant empty form+ (7 : BitVec 64))
    (if empty then 5 else 4) (selectDisp variant empty form) v readyV
    (by
      change CodeIn (codeRange (variant.pc (countOffset variant empty form) form + BitVec.ofNat 64 7) _) v
      rw [Variant.pc_add variant _ _ form]
      apply programText_slice (programLoaded_codeIn vInput.loaded)
        (variant.textOffset form + (countOffset variant empty form + 7))
      · cases empty <;> select_finite form variant
      · cases empty <;> select_finite form variant)
    ⟨shr.rip.trans (by change (countPC variant empty form + (3 : BitVec 64)) + 4 = _; rw [BitVec.add_assoc]; rfl),
      by cases empty <;> exact fun _ => by select_finite form variant⟩
  have taken : branchTarget (countPC variant empty form + (7 : BitVec 64)) 2
      ((selectDisp variant empty form).signExtend 64) =
      if empty then compressPC variant form else tailPC variant form := by
    cases empty <;> select_finite form variant
  have target : w.RIP = if ((inputs[index]'input.remaining).bytes.size-consumed)/128 = 0
      then (if empty then countPC variant true form + (9 : BitVec 64) else tailPC variant form)
      else compressPC variant form := by
    rw [branch.rip]
    cases empty
    · change (if (StatusFlags.ofRFLAGS v.RFLAGS).ZF then _ else _) = _
      rw [zero, taken]
      simp only [BitVec.add_assoc]
      change (if _ then _ else _) = _
      simp [compressPC]
    · change (if !(StatusFlags.ofRFLAGS v.RFLAGS).ZF then _ else _) = _
      rw [zero, taken]
      simp only [BitVec.add_assoc]
      change (if _ then _ else _) = _
      by_cases hz : ((inputs[index]'input.remaining).bytes.size-consumed)/128 = 0 <;> simp [hz]
  have tailInside : InProgram (tailPC variant form) := by
    apply inProgram_of_textOffset
    select_finite form variant
  have compressInside : InProgram (compressPC variant form) := by
    change InProgram (variant.pc (countOffset variant false form) form + BitVec.ofNat 64 9)
    rw [Variant.pc_add variant _ _ form]
    apply inProgram_of_textOffset
    select_finite form variant
  have runW : Advances (returnBoundary initial) 1 v w := by
    apply Advances.of_step stepW
    left
    rw [target]
    split
    · cases empty
      · exact boundary_ne_program outside tailInside
      · exact inside 9 (by omega)
    · exact boundary_ne_program outside compressInside
  have wInput := input_of_agrees ctx vInput runW readyW branch.agrees
    (by simp [jccEffect,Component.Covers]) (by simp [jccEffect]) (by simp [jccEffect])
    (by simp [jccEffect]) (by intro h; left; simp [jccEffect])
  have countW := (branch.agrees.read (n := 64) (r := 2) (by simp [jccEffect])).trans count
  have runSW := (runU.trans runV).trans runW
  have memSU := mov.agrees.external (by simp [movR64R64Effect, Effect.components, Component.Covers])
  have memUV := shr.agrees.external (by simp [shrR64Effect, Effect.components, Component.Covers])
  have memVW := branch.agrees.external (by simp [jccEffect, branchEffect, Effect.components, Component.Covers])
  have memSW := memVW.trans (memUV.trans memSU)
  have frameSW : MemoryWriteFrame s w #v[Stack.region initial (variant.routine form).minStackBytes] := by
    intro a ha
    rw [memSW]
  by_cases hzero : ((inputs[index]'input.remaining).bytes.size-consumed)/128 = 0
  · cases empty
    · exact ⟨w,wInput,countW,by simpa [hzero] using target, ⟨_,runSW⟩, frameSW⟩
    · have ripW : w.RIP = countPC variant true form + (9 : BitVec 64) := by simpa [hzero] using target
      have jumpTarget : branchTarget (countPC variant true form + (9 : BitVec 64)) 2
          ((jumpDisp variant form).signExtend 64) = tailPC variant form := by select_finite form variant
      obtain ⟨t,runT,readyT,jump⟩ :=
        (jmp_rel8_effect_step (countPC variant true form + (9 : BitVec 64)) (jumpDisp variant form)
          (by select_finite form variant)).advances readyW
          (by
            change CodeIn (codeRange (variant.pc (countOffset variant true form) form + BitVec.ofNat 64 9) _) w
            rw [Variant.pc_add variant _ _ form]
            apply programText_slice (programLoaded_codeIn wInput.loaded)
              (variant.textOffset form + (countOffset variant true form + 9))
            · select_finite form variant
            · select_finite form variant) ripW
          (by change branchTarget _ _ _ ≠ (returnBoundary initial).rip; rw [jumpTarget]; exact boundary_ne_program outside tailInside)
      exact ⟨t,input_of_agrees ctx wInput runT readyT jump.agrees
          (by simp [Component.Covers]) (by simp) (by simp) (by simp)
          (by intro h; left; simp),
        (jump.agrees.read (n := 64) (r := 2) (by simp)).trans countW,
        by simpa only [ite_eq_left hzero] using jump.rip.trans jumpTarget,
        ⟨_,runSW.trans runT⟩, by
          intro a ha
          rw [jump.agrees.external (by simp [Component.Covers]), memSW]⟩
  · exact ⟨w,wInput,countW,by simpa [hzero] using target, ⟨_,runSW⟩, frameSW⟩

end Sha2.Proofs.Wrapper512.Absorb.Large.Blocks
