import Sha2.Proofs.Common.SHA256.Return.RestorePointer
import Sha2.Proofs.Common.SHA256.Return.Stores
import Sha2.Proofs.Common.SHA256.Return.Epilogue

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

theorem compression_return_before_ret [Bindings] {initial current : RamState} {boundary : ReturnBoundary}
    {originalHash hash : Array UInt32} {input : ByteArray} {index count : Nat}
    (pre : CompressionPre initial boundary originalHash input count)
    (state : LoopState initial current hash index count)
    (rip : current.RIP = 0x10dcc4)
    (execution : ∃ fuel, Advances boundary fuel initial current) :
    ∃ final, CalleeResult initial final boundary 32 336 ⟨0x10dcf8, stackPtr initial⟩ ∧
      stackTop final = (returnBoundary initial).rip ∧ MemReadable final (stackPtr final) 8 ∧
      HashStateAt final (initial.regValue .rdi) hash := by
  obtain ⟨restored, run1, state1, rip1⟩ := restore_output_pointer pre state rip
  obtain ⟨stored, run2, state2, rip2, words⟩ := store_output_words pre state1 rip1
  obtain ⟨fuel, run⟩ := execution
  obtain ⟨final, result, top, readable, memory⟩ := compression_epilogue_before_ret pre state2
    ⟨fuel + 1 + 8, (run.trans run1).trans run2⟩ rip2
  refine ⟨final, result, top, readable, words.1, ?_⟩
  intro i hi
  rw [memory]
  exact words.2 i hi

theorem compression_return [Bindings] {initial current : RamState} {boundary : ReturnBoundary}
    {originalHash hash : Array UInt32} {input : ByteArray} {index count : Nat}
    (pre : CompressionPre initial boundary originalHash input count)
    (state : LoopState initial current hash index count)
    (rip : current.RIP = 0x10dcc4)
    (execution : ∃ fuel, Advances boundary fuel initial current)
    (hReturn : InProgram (returnBoundary initial).rip) :
    ∃ final, CalleeResult initial final boundary 32 336 ∧
      HashStateAt final (initial.regValue .rdi) hash := by
  obtain ⟨t, result, top, readable, words⟩ := compression_return_before_ret pre state rip execution
  obtain ⟨final, result', memory⟩ := result.finish top readable pre.outerBoundary hReturn
    (programText_slice (programLoaded_codeIn result.loaded) 0xdcf8 [0xc3]
      (by decide +kernel) (by decide +kernel))
  refine ⟨final, result', words.1, ?_⟩
  intro i hi
  rw [memory]
  exact words.2 i hi

end Sha2.Proofs.Common.SHA256
