import P256.Proofs.Field.Interface
import P256.Proofs.Program.CalleeRegisters
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Field

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem BinaryFieldPre.after_rip [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {entry target : BitVec 64} {reserve : Nat} (pre : BinaryFieldPre s boundary entry reserve)
    (ready : ReadyToStep t) (ag : AgreesExcept [.rip] s t) (rip : t.RIP = target) :
    BinaryFieldPre t boundary target reserve := by
  have memory := ag.external (by simp [Component.Covers])
  have regs (r : BitVec 5) : (Operand.reg r : Operand 64).read t =
      (Operand.reg r : Operand 64).read s := ag.read (by simp)
  have rsp : t.regValue .rsp = s.regValue .rsp := regs 4
  have right : t.regValue .rdx = s.regValue .rdx := regs 2
  have output : t.regValue .rdi = s.regValue .rdi := regs 7
  refine ⟨pre.toCalleePre.after_registers ready ag memory rsp (regs 6) output
    (ag.directionFlagClear (by simp) pre.directionFlag) rip, ?_, ?_, ?_, ?_⟩
  · simpa only [registerRegion, right] using pre.rightBounded
  · simpa only [registerRegion, right, memory] using pre.rightAllocated
  · simpa only [registerRegion, right, output] using pre.rightOutput
  · simpa only [registerRegion, right, Stack.region, rsp] using pre.rightStack

theorem result_prepend_rip [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {reserve fuel : Nat} (result : CalleeResult t u boundary 32 reserve)
    (run : Advances boundary fuel s t) (ag : AgreesExcept [.rip] s t) :
    CalleeResult s u boundary 32 reserve := by
  apply result.prepend_registers run (ag.external (by simp [Component.Covers]))
    (ag.read (n := 64) (r := 4) (by simp)) (ag.read (n := 64) (r := 7) (by simp))
    (fun r hr => ?_) (ag.mxcsr (by simp)) (ag.fcw (by simp))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ag.read (n := 64) (r := 3) (by simp)
  · exact ag.read (n := 64) (r := 5) (by simp)
  · exact ag.read (n := 64) (r := 12) (by simp)
  · exact ag.read (n := 64) (r := 13) (by simp)
  · exact ag.read (n := 64) (r := 14) (by simp)
  · exact ag.read (n := 64) (r := 15) (by simp)


end P256.Proofs.Field
