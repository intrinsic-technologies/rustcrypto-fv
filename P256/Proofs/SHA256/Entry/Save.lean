import P256.Proofs.SHA256.Entry.Branch
import P256.Proofs.Program.CalleeRegisters
import P256.Proofs.Program.SaveRegisters
import P256.Proofs.Program.StackAllocate

set_option autoImplicit false

namespace P256.Proofs.SHA256

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem entry_save [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {hash : Array UInt32} {input : ByteArray} {count : Nat}
    (pre : CompressionPre s boundary hash input count) (positive : 0 < count) :
    ∃ t, Advances boundary 9 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = 0x1159aa ∧ stackPtr t = stackPtr s - 336 ∧
      t.external = saveMemory s ∧ AgreesExcept (saveFrame s ++ [.flags]) s t := by
  obtain ⟨u, branch, ready, rip, frame⟩ := entry_branch pre
  have rip' : u.RIP = 0x115999 := by
    simpa only [ite_eq_right (by omega : count ≠ 0)] using rip
  have memory : u.external = s.external := frame.external (by simp [Component.Covers])
  have reg (r : BitVec 5) : (Operand.reg r : Operand 64).read u =
      (Operand.reg r : Operand 64).read s := frame.read (by simp)
  have cp := pre.toCalleePre.after_registers ready frame memory (reg 4) (reg 6) (reg 7)
    (frame.directionFlagClear (by simp) pre.directionFlag) rip'
  have code : SaveCode 0x15999 := by constructor <;> decide +kernel
  obtain ⟨v, run, readyV, loadedV, ripV, rspV, memoryV, frameV⟩ :=
    save_registers (codeOffset := 0x15999) cp.stack (cp.avoids _ (by simp)) cp.outerBoundary ready cp.loaded
      (by decide) rip' code
  have rspU : stackPtr u = stackPtr s := reg 4
  have frameU : saveFrame u = saveFrame s := by simp only [saveFrame, rspU]
  have saveU : saveMemory u = saveMemory s := by
    have r5 : u.regValue .rbp = s.regValue .rbp := reg 5
    have r15 : u.regValue .r15 = s.regValue .r15 := reg 15
    have r14 : u.regValue .r14 = s.regValue .r14 := reg 14
    have r13 : u.regValue .r13 = s.regValue .r13 := reg 13
    have r12 : u.regValue .r12 = s.regValue .r12 := reg 12
    have r3 : u.regValue .rbx = s.regValue .rbx := reg 3
    simp only [saveMemory, memory, rspU, r5, r15, r14, r13, r12, r3]
  obtain ⟨t, allocate, readyT, loadedT, ripT, rspT, memoryT, frameT⟩ :=
    stack_allocate32 0x159a3 288 readyV loadedV pre.outerBoundary ripV
      (by decide) (by decide +kernel)
  have total : AgreesExcept (saveFrame s ++ [.flags]) s t := by
    rw [frameU] at frameV
    apply ((frame.trans frameV).trans frameT).mono
    simp only [saveFrame, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    intro c hc
    rcases hc with ((rfl | rfl) | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
      rfl | rfl | rfl <;> simp
  refine ⟨t, (branch.trans run).trans allocate, readyT, loadedT, ripT, ?_,
    memoryT.trans (memoryV.trans saveU), total⟩
  rw [rspT, rspV, rspU, BitVec.sub_sub]
  rfl

end P256.Proofs.SHA256
