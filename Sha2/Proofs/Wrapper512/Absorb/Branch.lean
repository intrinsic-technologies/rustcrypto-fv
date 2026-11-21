import Sha2.Proofs.Wrapper512.Absorb.Loaded
import Sha2.Proofs.Wrapper512.Absorb.Prepare
import Sha2.Proofs.Wrapper512.Absorb.SmallSetup
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512

def Variant.largeOffset (v : Variant) (form : Form := .slices) : Nat :=
  v.loadedOffset form + 16

end Sha2.Proofs.Wrapper512

namespace Sha2.Proofs.Wrapper512.Absorb
open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

def sizeDisplacement : Form → BitVec 8
  | .slices | .digest => 0xa8
  | .reset stage => if stage.val = 0 then 0xae else if stage.val = 1 then 0xb1 else 0xb5
  | .finalizeIntoReset second => if second then 0xb2 else 0xab
  | .traitFinalizeIntoReset second => if second then 0x86 else 0x83

theorem size_branch_target (v : Variant) (form : Form) :
    branchTarget (v.pc (v.loadedOffset form + 14) form) 2
      ((sizeDisplacement form).signExtend 64) = v.pc (v.shortOffset form) form := by
  cases form with
  | slices | digest => cases v <;> decide +kernel
  | reset stage => revert stage; cases v <;> decide +kernel
  | finalizeIntoReset second => revert second; cases v <;> decide +kernel
  | traitFinalizeIntoReset second => revert second; cases v <;> decide +kernel

theorem size_branch_code {v : Variant} {form : Form} {s : RamState}
    (table : form ≠ .digest) (loaded : ProgramLoaded s) :
    CodeIn (codeRange (v.pc (v.loadedOffset form + 14) form)
      [0x72, UInt8.ofBitVec (sizeDisplacement form)]) s := by
  apply programText_slice (programLoaded_codeIn loaded)
    (v.textOffset form + (v.loadedOffset form + 14))
  · cases form with
    | slices => cases v <;> decide +kernel
    | digest => exact (table rfl).elim
    | reset stage => revert stage; cases v <;> decide +kernel
    | finalizeIntoReset second => revert second; cases v <;> decide +kernel
    | traitFinalizeIntoReset second => revert second; cases v <;> decide +kernel
  · cases form with
    | slices => cases v <;> decide +kernel
    | digest => exact (table rfl).elim
    | reset stage => revert stage; cases v <;> decide +kernel
    | finalizeIntoReset second => revert second; cases v <;> decide +kernel
    | traitFinalizeIntoReset second => revert second; cases v <;> decide +kernel

end Sha2.Proofs.Wrapper512.Absorb

namespace Sha2.Proofs.Wrapper512.Absorb
open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

theorem size_targets_inside (v : Variant) (form : Form) :
    InProgram (v.pc (v.shortOffset form) form) ∧
      InProgram (v.pc (v.largeOffset form) form) := by
  constructor <;> apply inProgram_of_textOffset
  all_goals cases form with
  | slices | digest => cases v <;> decide +kernel
  | reset stage => revert stage; cases v <;> decide +kernel
  | finalizeIntoReset second => revert second; cases v <;> decide +kernel
  | traitFinalizeIntoReset second => revert second; cases v <;> decide +kernel

theorem size_target_low (v : Variant) (form : Form) :
    (branchTarget (v.pc (v.loadedOffset form + 14) form) 2
      ((sizeDisplacement form).signExtend 64)).toNat < 2^32 := by
  rw [size_branch_target]
  cases form with
  | slices | digest => cases v <;> decide +kernel
  | reset stage => revert stage; cases v <;> decide +kernel
  | finalizeIntoReset second => revert second; cases v <;> decide +kernel
  | traitFinalizeIntoReset second => revert second; cases v <;> decide +kernel

end Sha2.Proofs.Wrapper512.Absorb

namespace Sha2.Proofs.Wrapper512

def Variant.emptyOffset (v : Variant) (form : Form := .slices) : Nat :=
  (v.traversal form).exit - (match form with | .traitFinalizeIntoReset _ => 19 | _ => 14)

end Sha2.Proofs.Wrapper512

namespace Sha2.Proofs.Wrapper512.Absorb
open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.Instructions

def emptyDisplacement (v : Variant) (form : Form) : BitVec 32 :=
  BitVec.ofNat 32 (v.emptyOffset form - (v.largeOffset form + 9))

theorem empty_test_code {v : Variant} {form : Form} {s : RamState}
    (table : form ≠ .digest) (loaded : ProgramLoaded s) :
    CodeIn (codeRange (v.pc (v.largeOffset form) form)
      (encodeTestR64R64 (BitVec.ofNat 4 (v.traversal form).tailReg)
        (BitVec.ofNat 4 (v.traversal form).tailReg))) s := by
  apply programText_slice (programLoaded_codeIn loaded)
    (v.textOffset form + v.largeOffset form)
  all_goals cases form with
  | slices => cases v <;> decide +kernel
  | digest => exact (table rfl).elim
  | reset stage => revert stage; cases v <;> decide +kernel
  | finalizeIntoReset second => revert second; cases v <;> decide +kernel
  | traitFinalizeIntoReset second => revert second; cases v <;> decide +kernel

theorem empty_branch_code {v : Variant} {form : Form} {s : RamState}
    (table : form ≠ .digest) (loaded : ProgramLoaded s) :
    CodeIn (codeRange (v.pc (v.largeOffset form + 3) form)
      (0x0f :: jccOpcode32 4 :: immBytes 32 (emptyDisplacement v form))) s := by
  apply programText_slice (programLoaded_codeIn loaded)
    (v.textOffset form + (v.largeOffset form + 3))
  all_goals cases form with
  | slices => cases v <;> decide +kernel
  | digest => exact (table rfl).elim
  | reset stage => revert stage; cases v <;> decide +kernel
  | finalizeIntoReset second => revert second; cases v <;> decide +kernel
  | traitFinalizeIntoReset second => revert second; cases v <;> decide +kernel

theorem empty_branch_target (v : Variant) (form : Form) (table : form ≠ .digest) :
    branchTarget (v.pc (v.largeOffset form + 3) form) 6
      ((emptyDisplacement v form).signExtend 64) = v.pc (v.emptyOffset form) form := by
  cases form with
  | slices => cases v <;> decide +kernel
  | digest => exact (table rfl).elim
  | reset stage => revert stage; cases v <;> decide +kernel
  | finalizeIntoReset second => revert second; cases v <;> decide +kernel
  | traitFinalizeIntoReset second => revert second; cases v <;> decide +kernel

theorem empty_sites_inside (v : Variant) (form : Form) :
    BlockInProgram (v.pc (v.largeOffset form) form) 9 ∧
      InProgram (v.pc (v.emptyOffset form) form) ∧
      (v.pc (v.emptyOffset form) form).toNat < 2^32 := by
  constructor
  · apply blockInProgram_of_textOffset
    cases form with
    | slices | digest => cases v <;> decide +kernel
    | reset stage => revert stage; cases v <;> decide +kernel
    | finalizeIntoReset second => revert second; cases v <;> decide +kernel
    | traitFinalizeIntoReset second => revert second; cases v <;> decide +kernel
  · constructor
    · apply inProgram_of_textOffset
      cases form with
      | slices | digest => cases v <;> decide +kernel
      | reset stage => revert stage; cases v <;> decide +kernel
      | finalizeIntoReset second => revert second; cases v <;> decide +kernel
      | traitFinalizeIntoReset second => revert second; cases v <;> decide +kernel
    · cases form with
      | slices | digest => cases v <;> decide +kernel
      | reset stage => revert stage; cases v <;> decide +kernel
      | finalizeIntoReset second => revert second; cases v <;> decide +kernel
      | traitFinalizeIntoReset second => revert second; cases v <;> decide +kernel

end Sha2.Proofs.Wrapper512.Absorb

namespace Sha2.Proofs.Wrapper512.Absorb
open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Wrapper

structure Prepared [Bindings] (v : Variant) (initial s : RamState) (inputs : Array Input)
    (index : Nat) (form : Form := .slices) : Prop
    extends SliceState v initial s inputs index form where
  space : s.regValue .rdx = BitVec.ofNat 64 (128 - (prefixMessage inputs index).size % 128)
  rest : (.reg (v.restRegister form) : Operand 64).read s =
    BitVec.ofNat 64 inputs[index].bytes.size -
      BitVec.ofNat 64 (128 - (prefixMessage inputs index).size % 128)

end Sha2.Proofs.Wrapper512.Absorb

namespace Sha2.Proofs.Wrapper512.Absorb
open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Wrapper

set_option maxHeartbeats 1000000 in
theorem prepare_size [Bindings] {v : Variant} {form : Form} {initial s : RamState}
    {inputs : Array Input} {index : Nat} (ctx : Context v initial inputs form)
    (input : Loaded v initial s inputs index form) (table : form ≠ .digest) :
    ∃ t, Prepared v initial t inputs index form ∧
      t.RIP = v.pc (v.loadedOffset form + 14) form ∧
      (StatusFlags.ofRFLAGS t.RFLAGS).CF =
        decide ((inputs[index]'input.remaining).bytes.size <
          128 - (prefixMessage inputs index).size % 128) ∧
      (∃ fuel, Advances (returnBoundary initial) fuel s t) ∧
      MemoryWriteFrame s t #v[Stack.region initial (v.routine form).minStackBytes] := by
  have outside := (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2
  obtain ⟨fuel,t,run,ready,_,effect⟩ := Prepare.run_form (v := v) (form := form)
    (returnBoundary initial) outside s (supportedMachine_readyToStep input.machine)
    (Prepare.code_form table input.loaded) input.rip
  have restWidth : ((v.restRegister form).setWidth 4).setWidth 5 = v.restRegister form := by
    cases form with
    | slices | digest => cases v <;> decide
    | reset stage =>
      rcases stage with ⟨n, hn⟩
      have h : n = 0 ∨ n = 1 ∨ n = 2 := by omega
      rcases h with rfl | rfl | rfl <;> cases v <;>
        rfl
    | finalizeIntoReset second => cases second <;> cases v <;> decide
    | traitFinalizeIntoReset second => cases second <;> cases v <;> decide
  have tailWidth : (BitVec.ofNat 4 (v.traversal form).tailReg).setWidth 5 =
      BitVec.ofNat 5 (v.traversal form).tailReg := by
    cases form with
    | slices | digest => cases v <;> decide
    | reset stage =>
      rcases stage with ⟨n, hn⟩
      have h : n = 0 ∨ n = 1 ∨ n = 2 := by omega
      rcases h with rfl | rfl | rfl <;> cases v <;>
        rfl
    | finalizeIntoReset second => cases second <;> cases v <;> decide
    | traitFinalizeIntoReset second => cases second <;> cases v <;> decide
  have lengthWidth : (BitVec.ofNat 4 (v.traversal form).lengthReg).setWidth 5 =
      BitVec.ofNat 5 (v.traversal form).lengthReg := by
    cases form with
    | slices | digest => cases v <;> decide
    | reset stage =>
      rcases stage with ⟨n, hn⟩
      have h : n = 0 ∨ n = 1 ∨ n = 2 := by omega
      rcases h with rfl | rfl | rfl <;> cases v <;>
        rfl
    | finalizeIntoReset second => cases second <;> cases v <;> decide
    | traitFinalizeIntoReset second => cases second <;> cases v <;> decide
  have frame : AgreesExcept [.reg 2,.reg (v.restRegister form),.flags,.rip] s t := by
    have h := effect.agrees
    change AgreesExcept [.reg 2, .reg ((v.restRegister form).setWidth 4 |>.setWidth 5),
      .flags, .rip] s t at h
    simpa only [restWidth] using h
  have current := input.toSliceState.of_agrees ctx run ready frame
    (by simp [Component.Covers]) (by
      cases form with
      | slices => cases v <;> decide
      | digest => exact (table rfl).elim
      | reset stage =>
      rcases stage with ⟨n, hn⟩
      have h : n = 0 ∨ n = 1 ∨ n = 2 := by omega
      rcases h with rfl | rfl | rfl <;> cases v <;>
        simp [Variant.traversal, ResetLayout.reset, Variant.restRegister]
      | finalizeIntoReset second => cases second <;> cases v <;> decide
      | traitFinalizeIntoReset second => cases second <;> cases v <;> decide)
    (by simp) (fun h => (table h).elim)
    (by intro h; cases h; simp [Variant.restRegister])
    (by
      cases form with
      | slices | digest => trivial
      | reset stage => intro h; simp [Variant.restRegister, h]
      | finalizeIntoReset second => cases second <;> cases v <;> simp [Variant.restRegister]
      | traitFinalizeIntoReset second => cases second <;> simp [Variant.restRegister])
  have gap : (128 : BitVec 64) - v.tailValue form s =
      BitVec.ofNat 64 (128 - (prefixMessage inputs index).size % 128) := by
    rw [input.position]
    exact BitVec.ofNat_sub_ofNat_of_le 128 _ (by omega) (by omega)
  have writes := effect.writes
  simp only [Prepare.registerEffect, Write.AllHold, restWidth,
    Common.SHA256.Absorb.Blocks.readReg, tailWidth, lengthWidth] at writes
  change t.regValue .rdx = 128 - v.tailValue form s ∧
    (.reg (v.restRegister form) : Operand 64).read t =
      v.lengthValue form s - (128 - v.tailValue form s) at writes
  refine ⟨t, ⟨current, writes.1.trans gap, ?_⟩, ?_, ?_, ⟨fuel, run⟩,
    frame.memoryWriteFrame (by simp [WritesWithin, Component.Covers])⟩
  · rw [writes.2, input.length, gap]
  · exact effect.rip.trans (Variant.pc_add v (v.loadedOffset form) 14 form)
  · have bound := (ctx.inputInMemory ⟨index,input.remaining⟩).2.1
    change (inputs[index]'input.remaining).address.toNat +
      (inputs[index]'input.remaining).bytes.size < 2^32 at bound
    rw [effect.flags.1]
    change (Common.SHA256.Absorb.Blocks.readReg s _).ult
      (128 - Common.SHA256.Absorb.Blocks.readReg s _) = _
    simp only [Common.SHA256.Absorb.Blocks.readReg, tailWidth, lengthWidth]
    change (v.lengthValue form s).ult (128 - v.tailValue form s) = _
    rw [input.length, gap, BitVec.ult_eq_decide, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

end Sha2.Proofs.Wrapper512.Absorb

namespace Sha2.Proofs.Wrapper512.Absorb
open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Wrapper

theorem Prepared.of_agrees [Bindings] {v : Variant} {initial s t : RamState}
    {inputs : Array Input} {form : Form} {index fuel : Nat} {components : List Component}
    (ctx : Context v initial inputs form) (input : Prepared v initial s inputs index form)
    (run : Advances (returnBoundary initial) fuel s t) (ready : ReadyToStep t)
    (frame : AgreesExcept components s t)
    (noMem : ∀ c ∈ components, ∀ a, ¬ c.Covers a)
    (kept : ∀ r ∈ ([2,BitVec.ofNat 5 (v.traversal form).lengthReg,4,v.restRegister form,
      BitVec.ofNat 5 (v.traversal form).tailReg,BitVec.ofNat 5 (v.traversal form).dataReg,
      BitVec.ofNat 5 (v.traversal form).indexReg,
      BitVec.ofNat 5 ((v.traversal form).countReg.getD 0)] : List (BitVec 5)),
      Component.reg r ∉ components)
    (hdf : .df ∉ components := by simp)
    (table : form ≠ .digest := by simp)
    (keptBuffer : form = .reset 1 → Component.reg 3 ∉ components := by simp)
    (keptMemcpy : match form with
      | .reset stage => stage.val = 2 → Component.reg 3 ∉ components
      | .finalizeIntoReset true => Component.reg (if v = .sha384 ∨ v = .sha512 then 3 else 12) ∉ components
      | .traitFinalizeIntoReset second => Component.reg (if second then 5 else 13) ∉ components
      | _ => True := by cases form <;> simp <;> split <;> trivial) : Prepared v initial t inputs index form := by
  refine ⟨input.toSliceState.of_agrees ctx run ready frame noMem ?_ hdf
    (fun h => (table h).elim) keptBuffer keptMemcpy,
    (frame.read (n := 64) (r := 2) (kept 2 (by simp))).trans input.space,
    (frame.read (n := 64) (r := v.restRegister form) (kept _ (by simp))).trans input.rest⟩
  intro r hr
  apply kept r
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
  rcases hr with h | h | h | h | h | h <;> simp [h]

end Sha2.Proofs.Wrapper512.Absorb

namespace Sha2.Proofs.Wrapper512.Absorb
open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Wrapper

theorem select_size [Bindings] {v : Variant} {form : Form} {initial s : RamState}
    {inputs : Array Input} {index : Nat} (ctx : Context v initial inputs form)
    (input : Loaded v initial s inputs index form) (table : form ≠ .digest := by simp) :
    ∃ t, Prepared v initial t inputs index form ∧
      t.RIP = (if (inputs[index]'input.remaining).bytes.size <
          128 - (prefixMessage inputs index).size % 128
        then v.pc (v.shortOffset form) form else v.pc (v.largeOffset form) form) ∧
      (∃ fuel, Advances (returnBoundary initial) fuel s t) ∧
      MemoryWriteFrame s t #v[Stack.region initial (v.routine form).minStackBytes] := by
  obtain ⟨u, current, ripU, carry, ⟨fuel, preparedRun⟩, preparedFrame⟩ := prepare_size ctx input table
  obtain ⟨t, step, ready, branch⟩ := jcc_rel8_effect_step
    (v.pc (v.loadedOffset form + 14) form) 2 (sizeDisplacement form)
    u (supportedMachine_readyToStep current.machine) (by simpa [immBytes, immByte, jccOpcode8] using (size_branch_code (v := v) table current.loaded))
    ⟨ripU, fun _ => size_target_low v form⟩
  have target : t.RIP = if (inputs[index]'input.remaining).bytes.size <
      128 - (prefixMessage inputs index).size % 128
      then v.pc (v.shortOffset form) form else v.pc (v.largeOffset form) form := by
    rw [branch.rip]
    simp only [jccEffect, branchEffect, size_branch_target,
      Variant.pc_add v (v.loadedOffset form + 14) 2 form]
    change (if (StatusFlags.ofRFLAGS u.RFLAGS).CF then _ else _) = _
    rw [carry]
    simp only [decide_eq_true_eq, Variant.largeOffset, Nat.add_assoc]
  have run : Advances (returnBoundary initial) 1 u t := by
    apply Advances.of_step step
    left
    rw [target]
    split
    · exact boundary_ne_program
        (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2
        (size_targets_inside v form).1
    · exact boundary_ne_program
        (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2
        (size_targets_inside v form).2
  have frame : AgreesExcept [.rip] u t := branch.agrees
  exact ⟨t, current.of_agrees ctx run ready frame (by simp [Component.Covers])
    (by simp) (by simp) table, target, ⟨_, preparedRun.trans run⟩,
    memoryWriteFrame_trans preparedFrame (frame.memoryWriteFrame (by simp [WritesWithin, Component.Covers]))⟩

end Sha2.Proofs.Wrapper512.Absorb

namespace Sha2.Proofs.Wrapper512.Absorb
open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Wrapper

set_option maxHeartbeats 1000000 in
theorem select_empty [Bindings] {v : Variant} {form : Form} {initial s : RamState}
    {inputs : Array Input} {index : Nat} (ctx : Context v initial inputs form)
    (input : Prepared v initial s inputs index form)
    (rip : s.RIP = v.pc (v.largeOffset form) form) (table : form ≠ .digest := by simp) :
    ∃ t, Prepared v initial t inputs index form ∧
      t.RIP = (if (prefixMessage inputs index).size % 128 = 0
        then v.pc (v.emptyOffset form) form else v.pc (v.largeOffset form + 9) form) ∧
      (∃ fuel, Advances (returnBoundary initial) fuel s t) ∧
      MemoryWriteFrame s t #v[Stack.region initial (v.routine form).minStackBytes] := by
  have outside := (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2
  have inside := (empty_sites_inside v form).1
  have width : ∀ (v : Variant) (form : Form),
      (BitVec.ofNat 4 (v.traversal form).tailReg).setWidth 5 =
        BitVec.ofNat 5 (v.traversal form).tailReg := by
    intro v form
    cases form with
    | slices | digest => cases v <;> decide +kernel
    | reset stage => revert stage; cases v <;> decide +kernel
    | finalizeIntoReset second => revert second; cases v <;> decide +kernel
    | traitFinalizeIntoReset second => revert second; cases v <;> decide +kernel
  obtain ⟨u, run, ready, effect⟩ :=
    (Common.SHA256.Absorb.Blocks.test_step (v.pc (v.largeOffset form) form)
      (BitVec.ofNat 4 (v.traversal form).tailReg)
      (BitVec.ofNat 4 (v.traversal form).tailReg)).advances
      (supportedMachine_readyToStep input.machine) (empty_test_code (v := v) table input.loaded)
      rip (boundary_ne_program outside (inside 3 (by decide)))
  have frame : AgreesExcept [.flags,.rip] s u := effect.agrees
  have current := input.of_agrees ctx run ready frame (by simp [Component.Covers])
    (by simp) (by simp) table
  obtain ⟨t, step, readyT, branch⟩ := jcc_rel32_effect_step
    (v.pc (v.largeOffset form + 3) form) 4 (emptyDisplacement v form) u ready
    (empty_branch_code (v := v) table current.loaded)
    ⟨effect.rip.trans (Variant.pc_add v (v.largeOffset form) 3 form), fun _ => by
      rw [empty_branch_target v form table]
      exact (empty_sites_inside v form).2.2⟩
  have zero : (StatusFlags.ofRFLAGS u.RFLAGS).ZF =
      decide ((prefixMessage inputs index).size % 128 = 0) := by
    rw [effect.flags.2.2.2.1]
    change (((.reg ((BitVec.ofNat 4 (v.traversal form).tailReg).setWidth 5) : Operand 64).read s &&&
      (.reg ((BitVec.ofNat 4 (v.traversal form).tailReg).setWidth 5) : Operand 64).read s) == 0) = _
    rw [width]
    change (v.tailValue form s &&& v.tailValue form s == 0) = _
    rw [BitVec.and_self, input.position]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    constructor
    · intro h
      have hn := congrArg BitVec.toNat h
      change (prefixMessage inputs index).size % 128 % 2^64 = 0 at hn
      omega
    · intro h
      rw [h]
      rfl
  have target : t.RIP = if (prefixMessage inputs index).size % 128 = 0
      then v.pc (v.emptyOffset form) form else v.pc (v.largeOffset form + 9) form := by
    rw [branch.rip]
    simp only [jccEffect, branchEffect, empty_branch_target v form table,
      Variant.pc_add v (v.largeOffset form + 3) 6 form]
    change (if (StatusFlags.ofRFLAGS u.RFLAGS).ZF then _ else _) = _
    rw [zero]
    simp only [decide_eq_true_eq, Nat.add_assoc]
  have advance : Advances (returnBoundary initial) 1 u t := by
    apply Advances.of_step step
    left
    rw [target]
    split
    · exact boundary_ne_program outside (empty_sites_inside v form).2.1
    · apply boundary_ne_program outside
      simpa only [Variant.pc_add v (v.largeOffset form) 9 form] using inside 9 (by decide)
  have branchFrame : AgreesExcept [.rip] u t := branch.agrees
  exact ⟨t,current.of_agrees ctx advance readyT branchFrame
    (by simp [Component.Covers]) (by simp) (by simp) table, target,
    ⟨_, run.trans advance⟩,
    (frame.trans branchFrame).memoryWriteFrame (by simp [WritesWithin, Component.Covers])⟩

end Sha2.Proofs.Wrapper512.Absorb
