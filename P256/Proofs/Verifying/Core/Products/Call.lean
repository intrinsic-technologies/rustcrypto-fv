import P256.Proofs.Field.Montgomery.Wrapper.State
import P256.Proofs.Program.Call

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Products

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open P256.Proofs.Field.Montgomery.Wrapper
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [Bindings] {s t : RamState} {boundary : ReturnBoundary} {entryPC : BitVec 64}

theorem call_reduction (pre : CalleePre s boundary entryPC 32 32 280)
    (state : FrameState s t) (rip : t.RIP = 0x11339d) :
    ∃ u, Advances boundary 1 t u ∧ ReadyToStep u ∧
      (callEffect (fun _ => 0x112840) 0x1133a2 t).Holds t u := by
  obtain ⟨u, run, ready, _, effect, _⟩ := call_rel32_exists pre.stack
    (pre.avoids _ (by simp)) pre.outerBoundary
    (readyToStep state.machine state.bindingsSupported) state.loaded state.allocated
    136 0x1339d 0xfffff49e state.rsp (by exact rip) (by decide) (by decide) (by decide)
    (by decide +kernel) (by exact inProgram_of_textOffset 0x12840 (by decide))
  exact ⟨u, run, ready, by exact effect⟩

end P256.Proofs.Verifying.Core.Products
