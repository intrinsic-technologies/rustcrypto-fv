import Sha2.Proofs.Common.Machine.Relocatable
import Sha2.Proofs.Common.SHA256.Correctness
import X86Proofs.Instructions.Call.Triple

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Blocks.CompressCall

open Sha2.Spec Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field Sha2.Proofs.Common.Machine

structure Pre [Bindings] (p : BitVec 64) (boundary : ReturnBoundary)
    (hash : Array UInt32) (input : ByteArray) (count : Nat) (s : RamState) : Prop where
  call : PushPre p 5 s
  returnInProgram : InProgram (p + 5)
  compression : ∀ u, ReadyToStep u →
    (callEffect (fun _ => 0x10b4e0) (p + 5) s).Holds s u →
    CompressionPre u boundary hash input count

def Post [Bindings] (p : BitVec 64) (boundary : ReturnBoundary)
    (hash : Array UInt32) (input : ByteArray) (s t : RamState) : Prop :=
  t.RIP = (p + (5 : BitVec 64)) ∧ stackPtr t = stackPtr s ∧
    ∃ u, (callEffect (fun _ => 0x10b4e0) (p + 5) s).Holds s u ∧
      CompressionResult u t boundary hash input

theorem run [Bindings] (p : BitVec 64) (disp : BitVec 32) (boundary : ReturnBoundary)
    (target : branchTarget p 5 (disp.signExtend 64) = 0x10b4e0)
    (outside : ¬ InProgram boundary.rip)
    (reload : ∀ t, ProgramLoaded t → CodeIn (codeRange p (encodeCallRel32 disp)) t)
    (hash : Array UInt32) (input : ByteArray) (count : Nat) :
    AdvanceTriple boundary (Pre p boundary hash input count)
      (codeRange p (encodeCallRel32 disp)) (Post p boundary hash input) := by
  intro s ready loaded pre
  obtain ⟨u, step, readyU, effectU⟩ :=
    (call_rel32_effect_step p disp (by rw [target]; decide)).advances ready loaded pre.call
      (by
        change branchTarget p 5 (disp.signExtend 64) ≠ boundary.rip
        rw [target]
        exact boundary_ne_program outside (inProgram_of_textOffset 0xb4e0 (by decide)))
  rw [target] at effectU
  obtain ⟨t, result⟩ := compression_correct (pre.compression u readyU effectU)
    (by
      change InProgram (stackTop u)
      rw [(callEffect_stack effectU).1]
      exact pre.returnInProgram)
  obtain ⟨fuel, run⟩ := result.execution
  refine ⟨1 + fuel, t, step.trans run, supportedMachine_readyToStep result.machine,
    reload t result.loaded, ?_⟩
  have stack := callEffect_stack effectU
  refine ⟨?_, ?_, u, effectU, result⟩
  · exact result.rip.trans stack.1
  · exact result.rsp.trans stack.2

end Sha2.Proofs.Common.SHA256.Blocks.CompressCall
