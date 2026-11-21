import Sha2.Proofs.Wrapper.Buffered
import X86Proofs.Instructions.Inc.Generated.R.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper.Absorb

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine
open Sha2.Proofs.Wrapper

def counterPC (large : Bool) (v : Variant := .sha256) : BitVec 64 := if large then (v.pc 0x19f) else (v.pc 0xc1)

def counterBranchCC (large : Bool) : BitVec 4 := if large then 5 else 4

def counterBranchDisplacement (large : Bool) : BitVec 32 := if large then 0xffffff22 else 0xee

set_option maxHeartbeats 1000000 in
theorem advance_iteration [Bindings] {v : Variant} {initial s : RamState} {inputs : Array Input} {index : Nat}
    (ctx : Context initial inputs v) (input : Buffered initial s (prefixMessage inputs (index+1)) v)
    (large : Bool) (rip : s.RIP = counterPC large v)
    (indexRegister : s.regValue .r14 = BitVec.ofNat 64 index)
    (countRegister : s.regValue .r15 = BitVec.ofNat 64 inputs.size)
    (remaining : index < inputs.size) :
    ∃ t, LoopState initial t inputs (index+1) v ∨
      (Buffered initial t (message inputs) v ∧ t.RIP = (v.pc 0x1bb)) := by
  have outside := (validCall_returnBoundary ctx.machine ctx.call).2.2
  have incCode : CodeIn (codeRange (counterPC large v) [0x49,0xff,0xc6]) s := by
    cases large
    · exact programText_slice (programLoaded_codeIn input.loaded) (v.textOffset + 0xc1) _ (by cases v <;> decide) (by cases v <;> decide +kernel)
    · exact programText_slice (programLoaded_codeIn input.loaded) (v.textOffset + 0x19f) _ (by cases v <;> decide) (by cases v <;> decide +kernel)
  have pcInc : counterPC large v + 3 = v.pc (if large then 0x1a2 else 0xc4) := by
    cases large
    · exact Variant.pc_add v 0xc1 3
    · exact Variant.pc_add v 0x19f 3
  have afterInc : InProgram (counterPC large v+3) := by
    rw [pcInc]
    exact Variant.pc_inProgram v (by cases large <;> decide)
  obtain ⟨u,incRun,incReady,inc⟩ :=
    (inc_r64_effect_step (counterPC large v) 0x49 0xc6 (by simp [RexWPrefix]) rfl rfl).advances
      (supportedMachine_readyToStep input.machine) incCode rip (boundary_ne_program outside afterInc)
  have incFrame : AgreesExcept [.reg 14,.flags,.rip] s u := inc.agrees
  have current := buffered_of_agrees ctx input incRun incReady incFrame
    (by simp [Component.Covers]) (by simp)
  have countU : u.regValue .r15 = BitVec.ofNat 64 inputs.size :=
    (incFrame.read (n := 64) (r := 15) (by simp)).trans countRegister
  have indexU : u.regValue .r14 = BitVec.ofNat 64 (index+1) := by
    have write : u.regValue .r14 = s.regValue .r14 + 1 := inc.writes
    rw [write,indexRegister,BitVec.ofNat_add]
    rfl
  have cmpCode : CodeIn (codeRange (counterPC large v+3) [0x4d,0x39,0xf7]) u := by
    rw [pcInc]
    cases large
    · exact programText_slice (programLoaded_codeIn current.loaded) (v.textOffset + 0xc4)
        [0x4d,0x39,0xf7] (by cases v <;> decide) (by cases v <;> decide +kernel)
    · exact programText_slice (programLoaded_codeIn current.loaded) (v.textOffset + 0x1a2)
        [0x4d,0x39,0xf7] (by cases v <;> decide) (by cases v <;> decide +kernel)
  have pcCmp : counterPC large v + 3 + 3 = v.pc (if large then 0x1a5 else 0xc7) := by
    rw [pcInc]
    cases large
    · exact Variant.pc_add v 0xc4 3
    · exact Variant.pc_add v 0x1a2 3
  have pcBranch : counterPC large v + 6 = v.pc (if large then 0x1a5 else 0xc7) := by
    rw [← pcCmp, BitVec.add_assoc]
    rfl
  have afterCmp : InProgram (counterPC large v+3+3) := by
    rw [pcCmp]
    exact Variant.pc_inProgram v (by cases large <;> decide)
  obtain ⟨uCmp,cmpRun,cmpReady,cmp⟩ :=
    (cmp_r64_r64_effect_step (counterPC large v+3) 0x4d 0xf7 (by simp [RexWPrefix]) rfl).advances
      incReady cmpCode inc.rip (boundary_ne_program outside afterCmp)
  have cmpFrame : AgreesExcept [.flags,.rip] u uCmp := cmp.agrees
  have currentV := buffered_of_agrees ctx current cmpRun cmpReady cmpFrame
    (by simp [Component.Covers]) (by simp)
  have branchCode : CodeIn (codeRange (counterPC large v+6)
      (0x0f :: jccOpcode32 (counterBranchCC large) :: immBytes 32 (counterBranchDisplacement large))) uCmp := by
    rw [pcBranch]
    cases large
    · exact programText_slice (programLoaded_codeIn currentV.loaded) (v.textOffset + 0xc7)
        [0x0f,0x84,0xee,0,0,0] (by cases v <;> decide) (by cases v <;> decide +kernel)
    · exact programText_slice (programLoaded_codeIn currentV.loaded) (v.textOffset + 0x1a5)
        [0x0f,0x85,0x22,0xff,0xff,0xff] (by cases v <;> decide) (by cases v <;> decide +kernel)
  have targetBound : (branchTarget (counterPC large v+6) 6
      ((counterBranchDisplacement large).signExtend 64)).toNat < 2^32 := by
    cases v <;> cases large <;> decide +kernel
  obtain ⟨w,branchStep,branchReady,branch⟩ := jcc_rel32_effect_step (counterPC large v+6)
    (counterBranchCC large) (counterBranchDisplacement large) uCmp cmpReady branchCode
      ⟨by
        have h : uCmp.RIP = (counterPC large v + (3 : BitVec 64)) + (3 : BitVec 64) := cmp.rip
        exact h.trans (by rw [BitVec.add_assoc]; rfl), fun _ => targetBound⟩
  have countBound := validCall_count_bound ctx.call
  have eqWord : ((BitVec.ofNat 64 inputs.size : BitVec 64) - BitVec.ofNat 64 (index+1) == 0) =
      decide (index+1 = inputs.size) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq, BitVec.sub_eq_iff_eq_add ]
    change (BitVec.ofNat 64 inputs.size = (0 : BitVec 64) + BitVec.ofNat 64 (index+1)) ↔ _
    have zeroAdd : (0 : BitVec 64) + BitVec.ofNat 64 (index+1) = BitVec.ofNat 64 (index+1) := by
      exact BitVec.zero_add _
    rw [zeroAdd]
    constructor
    · intro eq
      have hn := congrArg BitVec.toNat eq
      simp only [BitVec.toNat_ofNat] at hn
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hn
      omega
    · intro eq
      rw [eq]
  have zero : (StatusFlags.ofRFLAGS uCmp.RFLAGS).ZF = decide (index+1=inputs.size) := by
    rw [cmp.flags.2.2.2.1]
    change (u.regValue .r15 - u.regValue .r14 == 0) = _
    rw [countU,indexU]
    exact eqWord
  have target : w.RIP = if index+1=inputs.size then
      (if large then (v.pc 0x1ab) else (v.pc 0x1bb)) else (v.pc 0xcd) := by
    rw [branch.rip]
    cases v <;> cases large
    all_goals simp only [counterPC, counterBranchCC, counterBranchDisplacement,
      Bool.false_eq_true, ite_false, ite_true, jccEffect, branchEffect, branchTarget]
    all_goals change (if _ then _ else _) = _
    all_goals first
    | (change (if (StatusFlags.ofRFLAGS uCmp.RFLAGS).ZF then _ else _) = _
       rw [zero]
       by_cases he : index+1=inputs.size <;> simp [he, Variant.pc, Variant.textOffset])
    | (change (if !(StatusFlags.ofRFLAGS uCmp.RFLAGS).ZF then _ else _) = _
       rw [zero]
       by_cases he : index+1=inputs.size <;> simp [he, Variant.pc, Variant.textOffset])
    all_goals decide +kernel
  have branchRun : Advances (returnBoundary initial) 1 uCmp w := by
    apply Advances.of_step branchStep
    left
    rw [target]
    split
    · cases large
      · exact boundary_ne_program outside (Variant.pc_inProgram v (by decide : 0x1bb < 1024))
      · exact boundary_ne_program outside (Variant.pc_inProgram v (by decide : 0x1ab < 1024))
    · exact boundary_ne_program outside (Variant.pc_inProgram v (by decide : 0xcd < 1024))
  have branchFrame : AgreesExcept [.rip] uCmp w := branch.agrees
  have currentW := buffered_of_agrees ctx currentV branchRun branchReady branchFrame
    (by simp [Component.Covers]) (by simp)
  by_cases last : index+1=inputs.size
  · have final : Buffered initial w (message inputs) v := by
      simpa only [last,prefixMessage_size] using currentW
    cases large
    · exact ⟨w,Or.inr ⟨final,by simpa only [last,ite_true,Bool.false_eq_true,ite_false] using target⟩⟩
    · have jumpRip : w.RIP=(v.pc 0x1ab) := by simpa only [last,ite_true] using target
      obtain ⟨t,run,ready,jump⟩ := (jmp_rel8_effect_step (v.pc 0x1ab) 0x0e (by cases v <;> decide)).advances
        branchReady (programText_slice (programLoaded_codeIn final.loaded) (v.textOffset + 0x1ab) [0xeb,0x0e]
          (by cases v <;> decide) (by cases v <;> decide +kernel)) jumpRip
        (by
          have h : branchTarget (v.pc 0x1ab) 2 ((0x0e : BitVec 8).signExtend 64) = v.pc 0x1bb := by cases v <;> decide
          change branchTarget _ _ _ ≠ _
          rw [h]
          exact boundary_ne_program outside (Variant.pc_inProgram v (by decide : 0x1bb < 1024)))
      have frame : AgreesExcept [.rip] w t := jump.agrees
      exact ⟨t,Or.inr ⟨buffered_of_agrees ctx final run ready frame (by simp [Component.Covers]) (by simp),by
        have h : branchTarget (v.pc 0x1ab) 2 ((0x0e : BitVec 8).signExtend 64) = v.pc 0x1bb := by cases v <;> decide
        exact jump.rip.trans h⟩⟩
  · refine ⟨w,Or.inl ⟨currentW,?_,?_,?_,by omega⟩⟩
    · simpa only [last,ite_false] using target
    · exact (branchFrame.read (n := 64) (r := 14) (by simp)).trans
        ((cmpFrame.read (n := 64) (r := 14) (by simp)).trans indexU)
    · exact (branchFrame.read (n := 64) (r := 15) (by simp)).trans
        ((cmpFrame.read (n := 64) (r := 15) (by simp)).trans countU)

end Sha2.Proofs.Wrapper.Absorb
