import Sha2.Proofs.Common.SHA512.BlockAssembly
import Sha2.Proofs.Common.SHA512.Compression.Decoded
import Sha2.Proofs.Common.SHA512.Compression.Safety
import Sha2.Proofs.Common.SHA512.Compression.Values.Refinement.Trace
import Sha2.Proofs.Common.SHA512.Compression.Values.Program
import Sha2.Proofs.Common.SHA512.Compression.Values.Registers

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression

open Sha2.Spec Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

theorem BlockPre.initial_state {initial : RamState} {hash : Array UInt64} {block : ByteArray}
    (pre : BlockPre initial hash block) : Safety.State initial initial Safety.before00 := by
  refine ⟨pre.stack.rip, rfl, ?_, ?_⟩
  · intro h
    cases h
  · intro r hr
    have hr' : r = 6 := List.mem_singleton.mp hr
    subst r
    rfl

theorem BlockPre.constantsSeparate {initial : RamState} {hash : Array UInt64} {block : ByteArray}
    (pre : BlockPre initial hash block) : RangeApart (stackPtr initial) 416 0x200000 640 := by
  intro i hi j hj he
  apply pre.frameAvoids i hi
  rw [he]
  have bound : j < Extracted.rodataBytes.toList.length := by
    rw [chunked_toList_length, rodataBytes_size]
    omega
  refine ⟨Extracted.rodataBytes.toList[j], ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨⟨Extracted.rodataAddress, Extracted.rodataBytes⟩,
    by simp [Extracted.programSections], ?_⟩
  exact (mem_codeRange_iff _ _ _).mpr ⟨⟨j, bound⟩, by simp [Extracted.rodataAddress]⟩

namespace Values

def Op.preservesStack (offset : Nat) : Op → Bool
  | .store64 dst _ | .addStack64 dst _ | .xorStack64 dst _ => dst != offset
  | _ => true

theorem Op.stack_of_preserves {operation : Op} {offset : Nat}
    (preserves : operation.preservesStack offset = true) (context : ValueContext) (s : Values) :
    (operation.eval context s).stack offset = s.stack offset := by
  cases operation <;> simp_all [Op.preservesStack, Op.eval, writeReg, write64, Ne.symm]

theorem run_stack_of_preserves {ops : List Op} {offset : Nat}
    (preserves : ops.all (Op.preservesStack offset) = true) (context : ValueContext) (s : Values) :
    (run context ops s).stack offset = s.stack offset := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    simp only [List.all_cons, Bool.and_eq_true] at preserves
    exact (ih preserves.2 _).trans (op.stack_of_preserves preserves.1 context s)

set_option maxRecDepth 8192 in
theorem program_rsi_partition : Program.operations =
    [.store64 176 3, .store64 360 6] ++
    (Program.operations.drop 2).take (Program.operations.length - 8) ++
    [.mov64 6 (.mem (.stack 360))] ++ Program.part56 := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem program_preserves_saved_rsi :
    ((Program.operations.drop 2).take (Program.operations.length - 8)).all
      (Op.preservesStack 360) = true := by
  decide +kernel

theorem run_rsi_suffix (context : ValueContext) (s : Values) :
    (run context ([.mov64 6 (.mem (.stack 360))] ++ Program.part56) s).regs 6 =
      s.stack 360 := by rfl

theorem run_rsi (context : ValueContext) (s : Values) :
    (run context Program.operations s).regs 6 = s.regs 6 := by
  rw [program_rsi_partition, List.append_assoc, List.append_assoc]
  rw [run_append, run_append, run_rsi_suffix,
    run_stack_of_preserves program_preserves_saved_rsi]
  rfl

theorem Represents.rsi_eq {context : ValueContext} {values : Values} {model : RamState}
    (rep : Represents context values model) {value : BitVec 64}
    (equal : values.regs 6 = value) : model.regValue .rsi = value :=
  (rep.regs 6).symm.trans equal

end Values

theorem block_result_of_values [Bindings]
    {initial : RamState} {boundary : ReturnBoundary} {hash : Array UInt64} {block : ByteArray}
    (ready : ReadyToStep initial) (loaded : ProgramLoaded initial)
    (outside : ¬ InProgram boundary.rip) (pre : BlockPre initial hash block)
    (words : Values.hashState
        (Values.run (Values.contextOfRam initial) Values.Program.operations (Values.ofRam initial)) =
      BitVecState.ofState (SHA512.State.ofArray
        (NIST.SHA512.compress hash (NIST.Encoding.octetsToBits block)))) :
    ∃ final, BlockResult initial final boundary hash block := by
  have safe := Safety.certificate pre loaded
  have state := pre.initial_state
  obtain ⟨finalState, footprint⟩ := safe.result initial state
  have representation := (Values.Refinement.trace initial).result safe initial (Values.ofRam initial) state
    (Values.Represents.initial initial) (fun i hi j hj => Ne.symm (pre.inputSeparate j hj i hi))
    pre.constantsSeparate
  apply block_result_of_trace Decoded.instructions initial boundary hash block
    Extracted.programSections.toCodeMap ready (programLoaded_codeIn loaded)
    (safe.safe initial state boundary outside Decoded.instructions_code_subset)
    finalState.rip (representation.rsi_eq
      (Values.run_rsi (Values.contextOfRam initial) (Values.ofRam initial)))
    (representation.registersAt (compress_size _ _) words)
  intro actual final agree
  exact footprint.frame agree

end Sha2.Proofs.Common.SHA512.Compression
