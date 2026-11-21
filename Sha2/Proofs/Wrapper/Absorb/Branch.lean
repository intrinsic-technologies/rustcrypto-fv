import Sha2.Proofs.Wrapper.Absorb.Loaded
import Sha2.Proofs.Wrapper.Absorb.Prepare
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper.Absorb

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

structure Prepared [Bindings] (initial s : RamState) (inputs : Array Input) (index : Nat) (v : Variant := .sha256) : Prop
    extends SliceState (v := v) initial s inputs index where
  space : s.regValue .rdx = BitVec.ofNat 64 (64 - (prefixMessage inputs index).size % 64)
  rest : s.regValue .rbp = BitVec.ofNat 64 inputs[index].bytes.size -
    BitVec.ofNat 64 (64 - (prefixMessage inputs index).size % 64)

theorem select_size {v : Variant} [Bindings] {initial s : RamState} {inputs : Array Input} {index : Nat}
    (ctx : Context (v := v) initial inputs) (input : Loaded (v := v) initial s inputs index) :
    ∃ t, Prepared (v := v) initial t inputs index ∧
      t.RIP = if (inputs[index]'input.remaining).bytes.size < 64 - (prefixMessage inputs index).size % 64
        then (v.pc 0xa0) else (v.pc 0xfe) := by
  have outside := (validCall_returnBoundary ctx.machine ctx.call).2.2
  obtain ⟨fuel,u,run,ready,_,effect⟩ := Prepare.run (returnBoundary initial) outside s
    (supportedMachine_readyToStep input.machine) (Prepare.code input.loaded) input.rip
  have frame : AgreesExcept [.reg 2,.reg 5,.flags,.rip] s u := effect.agrees
  have current := input.toSliceState.of_agrees ctx run ready frame
    (by simp [Component.Covers]) (by simp)
  obtain ⟨t,step,readyT,branch⟩ := jcc_rel8_effect_step (v.pc 0xfc) 2 0xa2 u ready
    (programText_slice (programLoaded_codeIn current.loaded) (v.textOffset + 0xfc) [0x72,0xa2]
      (by cases v <;> decide) (by cases v <;> decide +kernel)) ⟨effect.rip, fun _ => by cases v <;> decide⟩
  have gap : (64 : BitVec 64) - s.regValue .r12 =
      BitVec.ofNat 64 (64 - (prefixMessage inputs index).size % 64) := by
    rw [input.position]
    exact BitVec.ofNat_sub_ofNat_of_le 64 _ (by omega) (by omega)
  have bound := validCall_input_bounded ctx.call (⟨index,input.remaining⟩ : Fin inputs.size)
  change (inputs[index]'input.remaining).address.toNat + (inputs[index]'input.remaining).bytes.size < 2^32 at bound
  have carry : (StatusFlags.ofRFLAGS u.RFLAGS).CF =
      decide ((inputs[index]'input.remaining).bytes.size < 64 - (prefixMessage inputs index).size % 64) := by
    change (StatusFlags.ofRFLAGS u.RFLAGS).CF = _
    rw [effect.flags.1]
    change (s.regValue .rbx).ult (64 - s.regValue .r12) = _
    rw [gap,input.length,BitVec.ult_eq_decide,BitVec.toNat_ofNat,BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by change (inputs[index]'input.remaining).bytes.size < 2^64; omega),
      Nat.mod_eq_of_lt (by omega)]
  have target : t.RIP = if (inputs[index]'input.remaining).bytes.size < 64 - (prefixMessage inputs index).size % 64
      then (v.pc 0xa0) else (v.pc 0xfe) := by
    rw [branch.rip]
    have pcTaken : branchTarget (v.pc 0xfc) 2 ((0xa2 : BitVec 8).signExtend 64) = v.pc 0xa0 := by
      cases v <;> decide +kernel
    simp only [jccEffect, branchEffect, pcTaken, Variant.pc_add]
    change (if (StatusFlags.ofRFLAGS u.RFLAGS).CF then (v.pc 0xa0) else (v.pc 0xfe)) = _
    rw [carry]
    simp only [decide_eq_true_eq]
  have advance : Advances (returnBoundary initial) 1 u t := by
    apply Advances.of_step step
    left
    rw [target]
    split
    · exact boundary_ne_program outside (Variant.pc_inProgram v (by decide : 0xa0 < 1024))
    · exact boundary_ne_program outside (Variant.pc_inProgram v (by decide : 0xfe < 1024))
  have branchFrame : AgreesExcept [.rip] u t := branch.agrees
  have result := current.of_agrees ctx advance readyT branchFrame
    (by simp [Component.Covers]) (by simp)
  refine ⟨t, ⟨result, ?_, ?_⟩, target⟩
  · exact (branchFrame.read (n := 64) (r := 2) (by simp)).trans (effect.writes.1.trans gap)
  · exact (branchFrame.read (n := 64) (r := 5) (by simp)).trans
      (effect.writes.2.trans (by rw [input.length,gap]))

theorem Prepared.of_agrees {v : Variant} [Bindings] {initial s t : RamState} {inputs : Array Input}
    {index fuel : Nat} {components : List Component}
    (ctx : Context (v := v) initial inputs) (input : Prepared (v := v) initial s inputs index)
    (run : Advances (returnBoundary initial) fuel s t) (ready : ReadyToStep t)
    (frame : AgreesExcept components s t)
    (noMem : ∀ c ∈ components, ∀ a, ¬ c.Covers a)
    (kept : ∀ r ∈ ([2,3,4,5,12,13,14,15] : List (BitVec 5)), Component.reg r ∉ components)
    (hdf : .df ∉ components := by simp) :
    Prepared (v := v) initial t inputs index := by
  refine ⟨input.toSliceState.of_agrees ctx run ready frame noMem ?_ hdf,
    (frame.read (n := 64) (r := 2) (kept 2 (by simp))).trans input.space,
    (frame.read (n := 64) (r := 5) (kept 5 (by simp))).trans input.rest⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact kept _ (by simp)

theorem select_empty {v : Variant} [Bindings] {initial s : RamState} {inputs : Array Input} {index : Nat}
    (ctx : Context (v := v) initial inputs) (input : Prepared (v := v) initial s inputs index)
    (rip : s.RIP = (v.pc 0xfe)) :
    ∃ t, Prepared (v := v) initial t inputs index ∧
      t.RIP = if (prefixMessage inputs index).size % 64 = 0 then (v.pc 0x1ad) else (v.pc 0x107) := by
  have outside := (validCall_returnBoundary ctx.machine ctx.call).2.2
  obtain ⟨u,run,ready,effect⟩ :=
    (test_r64_r64_effect_step (v.pc 0xfe) 0x4d 0xe4 (by simp [RexWPrefix]) rfl).advances
      (supportedMachine_readyToStep input.machine)
      (programText_slice (programLoaded_codeIn input.loaded) (v.textOffset + 0xfe) [0x4d,0x85,0xe4]
        (by cases v <;> decide) (by cases v <;> decide +kernel)) rip
      (by
        change v.pc 0xfe + BitVec.ofNat 64 3 ≠ _
        rw [Variant.pc_add]
        exact boundary_ne_program outside (Variant.pc_inProgram v (by decide : 0x101 < 1024)))
  have frame : AgreesExcept [.flags,.rip] s u := effect.agrees
  have current := input.of_agrees ctx run ready frame (by simp [Component.Covers]) (by simp)
  obtain ⟨t,step,readyT,branch⟩ := jcc_rel32_effect_step (v.pc 0x101) 4 0xa6 u ready
    (programText_slice (programLoaded_codeIn current.loaded) (v.textOffset + 0x101) [0x0f,0x84,0xa6,0,0,0]
      (by cases v <;> decide) (by cases v <;> decide +kernel)) ⟨effect.rip.trans (Variant.pc_add v 0xfe 3), fun _ => by cases v <;> decide⟩
  have zero : (StatusFlags.ofRFLAGS u.RFLAGS).ZF =
      decide ((prefixMessage inputs index).size % 64 = 0) := by
    rw [effect.flags.2.2.2.1]
    change (s.regValue .r12 &&& s.regValue .r12 == 0) = _
    rw [BitVec.and_self,input.position]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    constructor
    · intro h
      have hn := congrArg BitVec.toNat h
      change (prefixMessage inputs index).size % 64 % 2^64 = 0 at hn
      omega
    · intro h
      rw [h]
      rfl
  have target : t.RIP =
      if (prefixMessage inputs index).size % 64 = 0 then (v.pc 0x1ad) else (v.pc 0x107) := by
    rw [branch.rip]
    have pcTaken : branchTarget (v.pc 0x101) 6 ((0xa6 : BitVec 32).signExtend 64) = v.pc 0x1ad := by
      cases v <;> decide +kernel
    simp only [jccEffect, branchEffect, pcTaken, Variant.pc_add]
    change (if (StatusFlags.ofRFLAGS u.RFLAGS).ZF then (v.pc 0x1ad) else (v.pc 0x107)) = _
    rw [zero]
    simp only [decide_eq_true_eq]
  have advance : Advances (returnBoundary initial) 1 u t := by
    apply Advances.of_step step
    left
    rw [target]
    split
    · exact boundary_ne_program outside (Variant.pc_inProgram v (by decide : 0x1ad < 1024))
    · exact boundary_ne_program outside (Variant.pc_inProgram v (by decide : 0x107 < 1024))
  have branchFrame : AgreesExcept [.rip] u t := branch.agrees
  exact ⟨t,current.of_agrees ctx advance readyT branchFrame (by simp [Component.Covers]) (by simp),target⟩

end Sha2.Proofs.Wrapper.Absorb
