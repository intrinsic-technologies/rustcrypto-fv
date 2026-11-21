import P256.Proofs.Verifying.Combination.Table.Setup

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program)

namespace P256.Proofs.Verifying.Combination.Table

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def addSetupBytes : List UInt8 := [0x4c,0x89,0xf7,0x4c,0x89,0xe6]

def addSetupEffect (p : BitVec 64) (s : RamState) : Effect :=
  { rip := p + 6#64
    writes := [⟨(Operand.reg 7 : Operand 64), s.regValue .r14⟩,
      ⟨(Operand.reg 6 : Operand 64), s.regValue .r12⟩] }

theorem add_setup [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip)
    (p : BitVec 64) (hmid : InProgram (p + 3#64)) (hstop : InProgram (p + 6#64)) :
    AdvanceTriple boundary (fun s => s.RIP = p) (codeRange p addSetupBytes)
      (Effect.post (addSetupEffect p)) := by
  intro s ready code rip
  have first : StepEffect (fun s => s.RIP = p) (codeRange p [0x4c,0x89,0xf7])
      (movR64R64Effect p 7 14) :=
    mov_r64_r64_effect_step p 0x4c 0xf7 (by simp [RexWPrefix]) rfl
  have second : StepEffect (fun s => s.RIP = p + 3#64)
      (codeRange (p + 3#64) [0x4c,0x89,0xe6]) (movR64R64Effect (p + 3#64) 6 12) :=
    mov_r64_r64_effect_step (p + 3#64) 0x4c 0xe6 (by simp [RexWPrefix]) rfl
  obtain ⟨t, run1, ready1, eff1⟩ := first.advances ready
    (code.mono (by simpa [addSetupBytes] using codeRange_slice_subset p addSetupBytes 0 3)) rip
    (boundary_ne_program hout hmid)
  have code1 := eff1.codeIn
    (Effect.Avoids.of_noMem (by simp [Component.Covers]) _) code
  obtain ⟨u, run2, ready2, eff2⟩ := second.advances ready1
    (code1.mono (codeRange_slice_subset p addSetupBytes 3 3)) eff1.rip
    (by simpa only [movR64R64Effect, BitVec.add_assoc, BitVec.reduceAdd] using boundary_ne_program hout hstop)
  have code2 := eff2.codeIn
    (Effect.Avoids.of_noMem (by simp [Component.Covers]) _) code1
  have composed := eff1.seq (by x86_local) (by simp [movR64R64Effect, Write.Full, Operand.Full]) eff2
  refine ⟨2, u, run1.trans run2, ready2, code2, ?_⟩
  apply composed.weaken
  · x86_norm [addSetupEffect, BitVec.add_assoc]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [addSetupEffect]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [addSetupEffect]
  · x86_norm [addSetupEffect]
    all_goals (repeat first | constructor | rfl)

end P256.Proofs.Verifying.Combination.Table
