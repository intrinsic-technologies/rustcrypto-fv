import Sha2.Proofs.Common.SHA256.Compression.Correctness
import Sha2.Proofs.Common.SHA256.Entry.Initialize
import Sha2.Proofs.Common.SHA256.Entry.Zero
import Sha2.Proofs.Common.SHA256.Iteration
import Sha2.Proofs.Common.SHA256.Return

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

theorem loop_to_return [Bindings] (body : Compression.BlockCorrect)
    {initial current : RamState} {boundary : ReturnBoundary}
    {originalHash hash : Array UInt32} {input : ByteArray} {count index remaining : Nat}
    (pre : CompressionPre initial boundary originalHash input count)
    (state : LoopState initial current hash index count) (rip : current.RIP = 0x10b530)
    (positive : 0 < remaining) (total : index + remaining = count) :
    ∃ fuel final, Advances boundary fuel current final ∧ final.RIP = 0x10dcc4 ∧
      LoopState initial final (compressBlocksFrom hash input index remaining) count count := by
  induction remaining generalizing current hash index with
  | zero => omega
  | succ remaining ih =>
    have hi : index < count := by omega
    obtain ⟨next, result⟩ := body current boundary hash
      (input.extract (64*index) (64*(index+1)))
      (supportedMachine_readyToStep state.machine) state.loaded pre.outerBoundary
      (state.block_pre pre rip hi)
    obtain ⟨fuel, execution⟩ := result.execution
    have nextState := state.after_block pre result
    obtain ⟨control, controlRun, controlState, controlRip⟩ := loop_control pre nextState result.rip hi
    have run := execution.trans controlRun
    by_cases hz : remaining = 0
    · subst remaining
      have he : index + 1 = count := by omega
      refine ⟨fuel+3, control, run, ?_, ?_⟩
      · simpa only [he, ite_true] using controlRip
      · change LoopState initial control (NIST.SHA256.compress hash (blockBits input index)) count count
        exact Eq.mp (congrArg (fun k => LoopState initial control
          (NIST.SHA256.compress hash (blockBits input index)) k count) he) controlState
    · have he : index + 1 ≠ count := by omega
      have hr : control.RIP = 0x10b530 := by simpa only [ite_eq_right he] using controlRip
      obtain ⟨restFuel, final, restRun, restRip, restState⟩ := ih controlState hr (by omega) (by omega)
      exact ⟨fuel+3+restFuel, final, run.trans restRun, restRip, restState⟩

theorem compression_correct_of_block [Bindings] (body : Compression.BlockCorrect)
    {initial : RamState} {boundary : ReturnBoundary}
    {hash : Array UInt32} {input : ByteArray} {count : Nat}
    (pre : CompressionPre initial boundary hash input count)
    (hReturn : InProgram (returnBoundary initial).rip) :
    ∃ final, CompressionResult initial final boundary hash input := by
  by_cases hz : count = 0
  · subst count
    obtain ⟨final, result, _⟩ := compression_correct_zero pre hReturn
    exact ⟨final, result⟩
  · obtain ⟨entryFuel, entry, entryRun, entryRip, entryState⟩ := entry_initialize pre (by omega)
    obtain ⟨loopFuel, stored, loopRun, loopRip, loopState⟩ :=
      loop_to_return body pre entryState entryRip (remaining := count) (by omega) (by omega)
    obtain ⟨final, result, words⟩ := compression_return pre loopState loopRip
      ⟨entryFuel+loopFuel, entryRun.trans loopRun⟩ hReturn
    refine ⟨final, result, ?_⟩
    have hcount : input.size / 64 = count := by rw [pre.inputSize]; omega
    simpa only [compressBlocks, hcount] using words

theorem compression_correct [Bindings]
    {initial : RamState} {boundary : ReturnBoundary}
    {hash : Array UInt32} {input : ByteArray} {count : Nat}
    (pre : CompressionPre initial boundary hash input count)
    (hReturn : InProgram (returnBoundary initial).rip) :
    ∃ final, CompressionResult initial final boundary hash input :=
  compression_correct_of_block Compression.block_correct pre hReturn

end Sha2.Proofs.Common.SHA256
