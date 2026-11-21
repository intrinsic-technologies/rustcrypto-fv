import Sha2.Proofs.Common.SHA256.Absorb.State
import Sha2.Proofs.Common.Machine.StackCall
import Sha2.Proofs.Common.Machine.InputCall
import Sha2.Proofs.Common.Memory.Copy
import Sha2.Proofs.Common.SHA256.Blocks.CompressCall

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Absorb

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.SHA256.Absorb.Blocks (readReg)

def Stage.isCall : Stage → Bool
  | .smallCall | .fillCall | .fillCompressCall | .bulkCall | .tailCall => true
  | _ => false

def Stage.code (stage : Stage) (l : Layout) : CodeMap :=
  (l.blocks stage).flatMap Blocks.Site.code

def Stage.effect (stage : Stage) (l : Layout) (sp : BitVec 64) (s : RamState) : Effect :=
  let r := l.registers
  let buffer := l.buffer sp
  let forgotten : Option StatusFlagsOutcome := some ⟨none, none, none, none, none, none⟩
  let regWrite (r : BitVec 4) (value : BitVec 64) : Write :=
    ⟨(.reg (r.setWidth 5) : Operand 64), value⟩
  match stage with
  | .prepare => { (Blocks.effect (l.pc stage) (.prepare r) s) with rip := l.pc .smallBranch }
  | .smallBranch => branchEffect (condHolds 2 (StatusFlags.ofRFLAGS s.RFLAGS))
      (l.pc .emptyTest) (l.pc .smallSetup)
  | .emptyTest => { (testR64R64Effect (l.pc stage) (r.tail.setWidth 5) (r.tail.setWidth 5) s)
      with rip := l.pc .emptyBranch }
  | .emptyBranch => branchEffect (condHolds 4 (StatusFlags.ofRFLAGS s.RFLAGS))
      (l.pc .fillSetup) (l.pc .emptySetup)
  | .smallSetup =>
      { rip := l.smallCall.pc
        writes := [regWrite 7 (buffer + readReg s r.tail), regWrite 6 (readReg s r.source),
          regWrite 2 (readReg s r.length)]
        flags := forgotten }
  | .smallLength => { (Common.Instructions.AddByte.addR8R8Effect (l.pc stage)
      (r.length.setWidth 5) (r.tail.setWidth 5) s) with rip := l.pc .smallStore }
  | .smallStore =>
      { rip := l.smallExit
        writes := [⟨(.mem (buffer + 63) : Operand 8), (.reg (r.length.setWidth 5) : Operand 8).read s⟩] }
  | .fillSetup =>
      { rip := l.fillCall.pc
        writes := [regWrite l.savedSource (readReg s r.source + s.regValue .rdx),
          regWrite 7 (buffer + readReg s r.tail), regWrite 6 (readReg s r.source)]
        flags := forgotten }
  | .increment =>
      { rip := l.pc .fillCompressSetup
        writes := [⟨(.mem (buffer + 96) : Operand 64), memLoad s.external (buffer + 96) 64 + 1⟩]
        flags := forgotten }
  | .fillCompressSetup =>
      { rip := l.fillCompressCall.pc
        writes := [regWrite 2 1, regWrite 7 (buffer + 64), regWrite 6 buffer] ++
          (l.bufferRestore.toList.map fun r => regWrite r buffer) }
  | .clearTail => { rip := l.pc .restoreSource, writes := [⟨(.mem (buffer + 63) : Operand 8), 0⟩] }
  | .restoreSource =>
      { rip := l.pc .count, writes := [regWrite l.alignedSource (readReg s l.savedSource)] }
  | .count => { (Blocks.effect (l.pc stage) (.count r.remaining) s) with rip := l.pc .countBranch }
  | .countBranch => branchEffect (condHolds 4 (StatusFlags.ofRFLAGS s.RFLAGS))
      (l.pc .addBlocks) (l.pc .splitTail)
  | .addBlocks =>
      { rip := l.pc .bulkSetup
        writes := [⟨(.mem (buffer + 96) : Operand 64),
          memLoad s.external (buffer + 96) 64 + s.regValue .rdx⟩]
        flags := forgotten }
  | .bulkSetup =>
      { rip := l.bulkCall.pc
        writes := [regWrite 7 (buffer + 64), regWrite 6 (readReg s l.alignedSource)] ++
          (l.bulkSave.toList.map fun r => regWrite r (readReg s l.alignedSource)) }
  | .bulkRestore =>
      { rip := l.pc .splitTail
        writes := l.bulkSave.toList.map fun r => regWrite l.alignedSource (readReg s r) }
  | .splitTail => { (Blocks.effect (l.pc stage) (.splitTail l.alignedSource r.remaining) s)
      with rip := l.pc .tailStore }
  | .tailStore =>
      { rip := l.pc .tailSetup
        writes := [⟨(.mem (buffer + 63) : Operand 8), (.reg (r.remaining.setWidth 5) : Operand 8).read s⟩] }
  | .tailSetup =>
      { rip := l.tailCall.pc
        writes := [regWrite 7 buffer, regWrite 6 (readReg s l.alignedSource),
          regWrite 2 (readReg s r.remaining)] }
  | .emptySetup =>
      { rip := if readReg s r.length >>> 6 = 0 then l.pc .splitTail else l.pc .addBlocks
        writes := [regWrite r.remaining (readReg s r.length),
          regWrite 2 (readReg s r.length >>> 6)] ++
          (l.bufferRestore.toList.map fun r => regWrite r buffer)
        flags := forgotten }
  | _ => { rip := l.pc stage }

structure Stage.Pre (stage : Stage) (l : Layout) (sp : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = l.pc stage
  rsp : stackPtr s = sp
  tailWritable : Common.Instructions.CrossPageStore.Writable s (l.buffer sp + 63) 1
  counterWritable : Common.Instructions.CrossPageStore.Writable s (l.buffer sp + 96) 8
  tailApart : ∀ site ∈ l.blocks stage,
    RangeApart (l.buffer sp + 63) 1 site.pc (Blocks.bytes site.block).length
  counterApart : ∀ site ∈ l.blocks stage,
    RangeApart (l.buffer sp + 96) 8 site.pc (Blocks.bytes site.block).length
  bufferRegister : ∀ r ∈ l.bufferSource, readReg s r = l.buffer sp
  bufferRestored : stage = .tailSetup → ∀ r ∈ l.bufferRestore, readReg s r = l.buffer sp

structure Flow (l : Layout) : Prop where
  entry : l.entry = l.pc .prepare
  smallCall : l.smallCall.pc = l.pc .smallCall
  fillCall : l.fillCall.pc = l.pc .fillCall
  fillCompressCall : l.fillCompressCall.pc = l.pc .fillCompressCall
  bulkCall : l.bulkCall.pc = l.pc .bulkCall
  tailCall : l.tailCall.pc = l.pc .tailCall
  smallReturn : l.smallCall.pc + BitVec.ofNat 64 l.smallCall.encoding.bytes.length = l.pc .smallLength
  fillReturn : l.fillCall.pc + BitVec.ofNat 64 l.fillCall.encoding.bytes.length = l.pc .increment
  fillCompressReturn : l.fillCompressCall.pc + BitVec.ofNat 64 l.fillCompressCall.encoding.bytes.length = l.pc .clearTail
  bulkReturn : l.bulkCall.pc + BitVec.ofNat 64 l.bulkCall.encoding.bytes.length = l.pc .bulkRestore
  tailReturn : l.tailCall.pc + BitVec.ofNat 64 l.tailCall.encoding.bytes.length = l.largeExit
  alignedSource : l.alignedSource = l.registers.source
  prepareRegisters : [l.registers.tail, l.registers.length, l.registers.remaining, 2].Pairwise (· ≠ ·)
  splitRegisters : [l.alignedSource, l.registers.remaining, 0, 1].Pairwise (· ≠ ·)
  fillRegisters : l.savedSource ≠ l.registers.remaining ∧ l.savedSource ≠ l.registers.tail
  nonvolatile : ∀ r ∈ [l.registers.length, l.registers.tail, l.registers.remaining, l.savedSource],
    r ∈ ([3, 5, 12, 13, 14, 15] : List (BitVec 4))
  bulkSaved : (l.bulkSave = none → l.alignedSource ∈ ([3, 5, 12, 13, 14, 15] : List (BitVec 4))) ∧
    (∀ r ∈ l.bulkSave, r ∈ ([3, 5, 12, 13, 14, 15] : List (BitVec 4)) ∧ r ≠ l.registers.remaining)
  bufferSaved : ∀ r ∈ l.bufferSource, r.setWidth 5 ∉ l.clobbered ∧
    r ∈ ([3, 5, 12, 13, 14, 15] : List (BitVec 4)) ∧
    ∀ (stage : Stage) sp s, Component.reg (r.setWidth 5) ∉ (stage.effect l sp s).components
  restoreIndependent : ∀ r ∈ l.bufferRestore, r ≠ l.savedSource
  restoredSaved : ∀ r ∈ l.bufferRestore,
    r ∈ ([3, 5, 12, 13, 14, 15] : List (BitVec 4)) ∧
    ∀ stage ∈ [Stage.clearTail, .restoreSource, .count, .countBranch, .addBlocks,
        .bulkSetup, .bulkRestore, .splitTail, .tailStore, .tailSetup], ∀ sp s,
      Component.reg (r.setWidth 5) ∉ (stage.effect l sp s).components
  callerClobbers : ∀ r ∈ ([0, 1, 2, 6, 7, 8, 9, 10, 11] : List (BitVec 5)), r ∈ l.clobbered
  blockClobbers : ∀ (stage : Stage) sp s r, Component.reg r ∈ (stage.effect l sp s).components → r ∈ l.clobbered
  sourceNotCount : l.registers.source ≠ (2 : BitVec 4)

structure CodeFacts (l : Layout) : Prop where
  blocks : ∀ (stage : Stage) s, ProgramLoaded s → CodeIn (stage.code l) s
  calls : ∀ call ∈ [l.smallCall, l.fillCall, l.fillCompressCall, l.bulkCall, l.tailCall],
    ∀ s, ProgramLoaded s → CodeIn (codeRange call.pc call.encoding.bytes) s
  inside : ∀ (stage : Stage), InProgram (l.pc stage)
  exits : InProgram l.smallExit ∧ InProgram l.largeExit

structure BlockContracts [Bindings] (l : Layout) (boundary : ReturnBoundary) : Prop where
  run : ∀ (stage : Stage), stage.isCall = false → ∀ sp,
    AdvanceTriple boundary (stage.Pre l sp) (stage.code l) (Effect.post (stage.effect l sp))

structure CallTargets (l : Layout) : Prop where
  copies : ∀ call ∈ [l.smallCall, l.fillCall, l.tailCall],
    match call.encoding with
    | .relative disp => branchTarget call.pc 5 (disp.signExtend 64) = 0x10dd60
    | .memory am => ∃ disp, am = .rip disp ∧ call.pc + 6 + disp.signExtend 64 = 0x200280
    | .register r => r ∈ ([3, 5, 12, 13, 14, 15] : List (BitVec 4)) ∧
        r.setWidth 5 ∉ l.clobbered
  compressions : ∀ call ∈ [l.fillCompressCall, l.bulkCall],
    ∃ disp, call.encoding = .relative disp ∧ branchTarget call.pc 5 (disp.signExtend 64) = 0x10b4e0

def Contract [bindings : Bindings] (l : Layout) : Prop :=
  ∀ {initial s : RamState} {n reserve : Nat} {regions : Vector MemoryRegion n}
    {prior : ByteArray} {input : Input},
    WellFormed l reserve → Flow l → CodeFacts l → CallTargets l →
    BlockContracts l (returnBoundary initial) →
    UnitStringStride bindings → SupportedMachine bindings initial →
    Stack.Valid initial reserve →
    (Stack.region initial reserve).Avoids (fun a => InProgram a ∨ InPageTables a) →
    ValidReturnAddress initial → ExecutionState initial s regions →
    Prepared l (l.sp initial) prior input s → input.region.Disjoint (Stack.region initial reserve) →
    (∀ region ∈ footprint l (l.sp initial), ∀ a, region.Contains a →
      ∃ outer ∈ regions, outer.Contains a) →
    ∃ t, Finished l initial s t regions prior input

end Sha2.Proofs.Common.SHA256.Absorb
