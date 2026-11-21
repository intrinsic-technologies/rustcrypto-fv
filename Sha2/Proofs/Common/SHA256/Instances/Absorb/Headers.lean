import Sha2.Proofs.Common.SHA256.Instances.Absorb.Chunks

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Instances.Absorption

open Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.SHA256.Absorb

def Loop.reserve : Loop → Nat
  | .resetDiscarded | .resetFirst | .resetLast => 720
  | _ => 832

theorem Loop.wellFormed (loop : Loop) (v : Wrapper.Variant := .sha256) : WellFormed (loop.chunk v) loop.reserve := by
  cases v <;> cases loop <;> constructor <;> decide +kernel

set_option maxHeartbeats 800000 in
theorem Loop.flow (loop : Loop) (v : Wrapper.Variant := .sha256) : Flow (loop.chunk v) := by
  cases v <;> cases loop <;> constructor
  all_goals first
    | decide +kernel
    | simp [Loop.chunk, Loop.stagePC, Stage.effect, Effect.components, Blocks.effect,
        testR64R64Effect, Common.Instructions.AddByte.addR8R8Effect]

  all_goals
    intro stage
    cases stage <;> simp_all [branchEffect]

  all_goals grind

theorem Loop.callTargets (loop : Loop) (v : Wrapper.Variant := .sha256) : CallTargets (loop.chunk v) := by
  cases v <;> cases loop <;> constructor <;> simp [Loop.chunk, branchTarget]

end Sha2.Proofs.Common.SHA256.Instances.Absorption
