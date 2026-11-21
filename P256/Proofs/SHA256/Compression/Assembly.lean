import P256.Proofs.SHA256.Interface
import P256.Proofs.SHA256.Mathematics.Equivalence
import P256.Proofs.SHA256.Compression.BlockAssembly
import P256.Proofs.SHA256.Compression.Decoded
import P256.Proofs.SHA256.Compression.Safety
import P256.Proofs.SHA256.Compression.Values.Refinement
import P256.Proofs.SHA256.Compression.Values.Registers

set_option autoImplicit false

namespace P256.Proofs.SHA256.Compression

open P256.Proofs.Common.SHA256.Compression

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem BlockPre.initial_state {initial : RamState} {hash : Array UInt32} {block : ByteArray}
    (pre : BlockPre initial hash block) : Safety.State initial initial Safety.before00 := by
  refine ⟨pre.stack.rip, rfl, ?_, ?_⟩
  · intro h
    cases h
  · intro r hr
    have hr' : r = 6 := List.mem_singleton.mp hr
    subst r
    rfl

theorem block_result_of_values [Bindings]
    {initial : RamState} {boundary : ReturnBoundary} {hash : Array UInt32} {block : ByteArray}
    (ready : ReadyToStep initial) (loaded : ProgramLoaded initial)
    (outside : ¬ InProgram boundary.rip) (pre : BlockPre initial hash block)
    (words : Values.hashState
        (Values.run (Values.contextOfRam initial) Values.Program.operations (Values.ofRam initial)) =
      BitVecState.ofState (P256.Proofs.SHA256.State.ofArray
        (Reference.compress hash (Standards.NIST.SHA2.bytesToBits block)))) :
    ∃ final, BlockResult initial final boundary hash block := by
  have safe := Safety.certificate pre
  have state := pre.initial_state
  obtain ⟨finalState, footprint⟩ := safe.result initial state
  have representation := (Values.Refinement.trace initial).result safe initial (Values.ofRam initial) state
    (Values.Represents.initial initial) (fun i hi j hj => Ne.symm (pre.inputSeparate j hj i hi))
  apply block_result_of_trace Decoded.instructions initial boundary hash block
    Extracted.programSections.toCodeMap ready (programLoaded_codeIn loaded)
    (safe.safe initial state boundary outside Decoded.instructions_code_subset)
    finalState.rip (finalState.rsi (by simp only [Safety.after52, List.mem_singleton]))
    (representation.registersAt (compress_size _ _) words)
  intro actual final agree
  exact footprint.frame agree

end P256.Proofs.SHA256.Compression
