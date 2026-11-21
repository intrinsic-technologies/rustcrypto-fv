import P256.Proofs.Program.Interface
import P256.Proofs.Program.State

set_option autoImplicit false

namespace P256.Proofs.Program

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable {inputRegister : Syntax.Reg}

theorem CalleePre.after_registers [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {entry next : BitVec 64} {inputBytes outputBytes reserve : Nat} {components : List Component}
    (pre : CalleePre s boundary entry inputBytes outputBytes reserve inputRegister)
    (ready : ReadyToStep t) (agrees : AgreesExcept components s t)
    (memory : t.external = s.external) (rsp : t.regValue .rsp = s.regValue .rsp)
    (source : t.regValue inputRegister = s.regValue inputRegister)
    (destination : t.regValue .rdi = s.regValue .rdi)
    (direction : DirectionFlagUnset t) (rip : t.RIP = next) :
    CalleePre t boundary next inputBytes outputBytes reserve inputRegister := by
  have stack : Stack.region t reserve = Stack.region s reserve := by simp only [Stack.region, rsp]
  have input : registerRegion t inputRegister inputBytes = registerRegion s inputRegister inputBytes := by
    simp only [registerRegion, source]
  have output : registerRegion t .rdi outputBytes = registerRegion s .rdi outputBytes := by
    simp only [registerRegion, destination]
  refine ⟨bindingsSupported_of_ready_agrees pre.bindingsSupported ready agrees,
    supportedMachine_of_ready_agrees pre.machine ready agrees, direction,
    ?_, rip, ?_, ?_, ?_, ?_, ?_, ?_, ?_, pre.outerBoundary, ?_⟩
  · simpa only [ProgramLoaded, memory] using pre.loaded
  · simpa only [input] using pre.inputBounded
  · simpa only [input, memory] using pre.inputAllocated
  · simpa only [output] using pre.outputBounded
  · simpa only [output, memory] using pre.outputAllocated
  · simpa only [Stack.Valid, stack, memory, Stack.NoUnderflow, Stack.returnSlot, rsp] using pre.stack
  · simpa only [input, output, stack] using pre.separation
  · simpa only [output, stack] using pre.avoids
  · change InProgram (memLoad t.external (stackPtr t) 64)
    rw [memory, show stackPtr t = stackPtr s from rsp]
    exact pre.returnInProgram

theorem CalleeResult.prepend_registers [Bindings] {s t u : RamState}
    {boundary : ReturnBoundary} {outputBytes reserve fuel : Nat}
    (result : CalleeResult t u boundary outputBytes reserve)
    (run : Advances boundary fuel s t)
    (memory : t.external = s.external) (rsp : t.regValue .rsp = s.regValue .rsp)
    (destination : t.regValue .rdi = s.regValue .rdi)
    (saved : CalleeSavedRegistersUnchanged s t)
    (mxcsr : t.MXCSR = s.MXCSR) (fp87 : t.FP87_Control = s.FP87_Control) :
    CalleeResult s u boundary outputBytes reserve := by
  have ret : returnBoundary t = returnBoundary s := by
    change ({ rip := memLoad t.external (stackPtr t) 64, rsp := stackPtr t + 8 } :
      ReturnBoundary) = { rip := memLoad s.external (stackPtr s) 64, rsp := stackPtr s + 8 }
    rw [memory, show stackPtr t = stackPtr s from rsp]
  obtain ⟨n, execution⟩ := result.execution
  refine ⟨⟨fuel+n, run.trans execution⟩, result.rip.trans (congrArg ReturnBoundary.rip ret),
    result.rsp.trans (congrArg ReturnBoundary.rsp ret), result.bindingsSupported,
    result.machine, ?_, result.directionFlag, result.mxcsr.trans mxcsr,
    result.fp87.trans fp87, ?_, result.loaded, ?_⟩
  · intro r hr
    exact (result.calleeSaved r hr).trans (saved r hr)
  · simpa only [MemoryWriteFrame, registerRegion, Stack.region, destination, rsp, memory]
      using result.frame
  · intro a ha
    apply result.allocated a
    simpa only [memory] using ha

end P256.Proofs.Program
