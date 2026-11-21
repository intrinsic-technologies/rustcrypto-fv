import Hkdf.Proofs.Common.SHA256.Return.RestorePointer
import Hkdf.Proofs.Common.SHA256.Return.Stores
import Hkdf.Proofs.Common.SHA256.Return.Epilogue

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256

open Hkdf.Spec Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Machine

theorem compression_return [Bindings] {initial current : RamState} {boundary : ReturnBoundary}
    {originalHash hash : Array UInt32} {input : ByteArray} {index count : Nat}
    (pre : CompressionPre initial boundary originalHash input count)
    (state : LoopState initial current hash index count)
    (rip : current.RIP = 0x10bda4)
    (execution : ∃ fuel, Advances boundary fuel initial current) :
    ∃ final, CalleeResult initial final boundary 32 336 ∧
      HashStateAt final (initial.regValue .rdi) hash := by
  obtain ⟨restored, run1, state1, rip1⟩ := restore_output_pointer pre state rip
  obtain ⟨stored, run2, state2, rip2, words⟩ := store_output_words pre state1 rip1
  obtain ⟨fuel, run⟩ := execution
  obtain ⟨final, result, memory⟩ := compression_epilogue pre state2
    ⟨fuel + 1 + 8, (run.trans run1).trans run2⟩ rip2
  refine ⟨final, result, words.1, ?_⟩
  intro i hi
  rw [memory]
  exact words.2 i hi

end Hkdf.Proofs.Common.SHA256
