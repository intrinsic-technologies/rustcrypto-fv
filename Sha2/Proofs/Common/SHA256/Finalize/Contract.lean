import Sha2.Proofs.Common.SHA256.Finalize.Blocks
import Sha2.Proofs.Common.SHA256.Finalize.State
import Sha2.Proofs.Common.Machine.StackCall
import Sha2.Proofs.Common.Machine.InputCall
import Sha2.Proofs.Common.Memory.Fill

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Finalize

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field Sha2.Proofs.Common.Machine

inductive Stage where
  | mark | fill | branch | firstHead | firstLower | firstSetup | firstCall
  | zero | length | lastHead | lastLower | lastSetup | lastCall

def Stage.pc (stage : Stage) (L : Layout) : BitVec 64 :=
  match stage with
  | .mark => L.entry
  | .fill => L.fillCall
  | .branch => L.branch
  | .firstHead => L.firstHead
  | .firstLower => L.firstLower
  | .firstSetup => L.firstSetup
  | .firstCall => L.firstCall
  | .zero => L.zero
  | .length => L.length
  | .lastHead => L.lastHead
  | .lastLower => L.lastLower
  | .lastSetup => L.lastSetup
  | .lastCall => L.lastCall

def Stage.bytes (stage : Stage) (L : Layout) : List UInt8 :=
  match stage with
  | .mark => Mark.bytes L.variant
  | .fill => encodeCallM64 (.rip L.fillDisp)
  | .branch => Branch.bytes L.variant L.branchDisp
  | .firstHead => FirstHead.bytes L.variant
  | .firstLower | .lastLower => Lower.bytes L.variant
  | .firstSetup => Setup.bytes L.variant false
  | .firstCall => encodeCallRel32 L.firstDisp
  | .zero => Blocks.Zero.bytes L.variant.buffer
  | .length => Blocks.Length.bytes L.variant.registers
  | .lastHead => LastHead.bytes L.variant
  | .lastSetup => Setup.bytes L.variant true
  | .lastCall => encodeCallRel32 L.lastDisp

structure Flow (L : Layout) : Prop where
  mark : L.entry + BitVec.ofNat 64 (Mark.bytes L.variant).length = L.fillCall
  fill : L.fillCall + 6 = L.branch
  branchFallthrough : L.branch + BitVec.ofNat 64 (Branch.bytes L.variant L.branchDisp).length = L.firstHead
  branchTaken : branchTarget
    (L.branch + BitVec.ofNat 64 (Branch.comparisonBytes L.variant).length) 6
    (L.branchDisp.signExtend 64) = L.length
  firstHead : L.firstHead + BitVec.ofNat 64 (FirstHead.bytes L.variant).length = L.firstLower
  firstLower : L.firstLower + BitVec.ofNat 64 (Lower.bytes L.variant).length = L.firstSetup
  firstSetup : L.firstSetup + BitVec.ofNat 64 (Setup.bytes L.variant false).length = L.firstCall
  firstCall : L.firstCall + 5 = L.zero
  zero : L.zero + BitVec.ofNat 64 L.variant.buffer.length = L.length
  length : L.length + BitVec.ofNat 64 L.variant.registers.length = L.lastHead
  lastHead : L.lastHead + BitVec.ofNat 64 (LastHead.bytes L.variant).length = L.lastLower
  lastLower : L.lastLower + BitVec.ofNat 64 (Lower.bytes L.variant).length = L.lastSetup
  lastSetup : L.lastSetup + BitVec.ofNat 64 (Setup.bytes L.variant true).length = L.lastCall
  lastCall : L.lastCall + 5 = L.exit
  fillPointer : L.fillCall + 6 + L.fillDisp.signExtend 64 = 0x200288
  firstTarget : branchTarget L.firstCall 5 (L.firstDisp.signExtend 64) = 0x10b4e0
  lastTarget : branchTarget L.lastCall 5 (L.lastDisp.signExtend 64) = 0x10b4e0

structure CodeFacts (L : Layout) : Prop where
  loaded : ∀ (stage : Stage) (s : RamState), ProgramLoaded s →
    CodeIn (codeRange (stage.pc L) (stage.bytes L)) s
  inside : ∀ stage : Stage, BlockInProgram (stage.pc L) (stage.bytes L).length

structure BlockContracts [Bindings] (L : Layout) (boundary : ReturnBoundary) : Prop where
  mark : AdvanceTriple boundary (Mark.Pre L.entry L.variant)
    (codeRange L.entry (Mark.bytes L.variant)) (Effect.post (Mark.effect L.entry L.variant))
  branch : AdvanceTriple boundary (fun s => s.RIP = L.branch)
    (codeRange L.branch (Branch.bytes L.variant L.branchDisp))
    (Effect.post (Branch.effect L.branch L.variant L.branchDisp))
  firstHead : AdvanceTriple boundary (FirstHead.Pre L.firstHead L.variant)
    (codeRange L.firstHead (FirstHead.bytes L.variant))
    (Effect.post (FirstHead.effect L.firstHead L.variant))
  lower : ∀ p, BlockInProgram p (Lower.bytes L.variant).length →
    AdvanceTriple boundary (Lower.Pre p L.variant)
      (codeRange p (Lower.bytes L.variant)) (Effect.post (Lower.effect p L.variant))
  lastHead : AdvanceTriple boundary (LastHead.Pre L.lastHead L.variant)
    (codeRange L.lastHead (LastHead.bytes L.variant))
    (Effect.post (LastHead.effect L.lastHead L.variant))
  setup : ∀ p last, BlockInProgram p (Setup.bytes L.variant last).length →
    AdvanceTriple boundary (fun s => s.RIP = p)
      (codeRange p (Setup.bytes L.variant last)) (Effect.post (Setup.effect p L.variant last))

def Contract [bindings : Bindings] (L : Layout) : Prop :=
  ∀ {initial s : RamState} {n reserve : Nat}
    {regions : Vector MemoryRegion n} {message : ByteArray},
    WellFormed L reserve → Flow L → CodeFacts L →
    BlockContracts L (returnBoundary initial) →
    UnitStringStride bindings → SupportedMachine bindings initial →
    Stack.Valid initial reserve →
    (Stack.region initial reserve).Avoids (fun a => InProgram a ∨ InPageTables a) →
    ValidReturnAddress initial → ExecutionState initial s regions →
    Prepared L (L.sp initial) message s →
    (∀ region ∈ footprint L (L.sp initial), ∀ a, region.Contains a →
      ∃ outer ∈ regions, outer.Contains a) →
    ∃ t, Finalized L initial s t regions message

end Sha2.Proofs.Common.SHA256.Finalize
