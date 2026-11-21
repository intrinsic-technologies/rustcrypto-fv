import Sha2.Proofs.Common.SHA256.Absorb.Proof.Small.Transport

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Absorb

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

theorem restored_of_stage {l : Layout} {sp : BitVec 64} {s t : RamState}
    (flow : Flow l) {stage : Stage}
    (member : stage ∈ [Stage.clearTail, .restoreSource, .count, .countBranch, .addBlocks,
      .bulkSetup, .bulkRestore, .splitTail, .tailStore, .tailSetup])
    (effect : (stage.effect l sp s).Holds s t)
    (restored : ∀ r ∈ l.bufferRestore, Blocks.readReg s r = l.buffer sp) :
    ∀ r ∈ l.bufferRestore, Blocks.readReg t r = l.buffer sp := by
  intro r hr
  exact (effect.agrees.read ((flow.restoredSaved r hr).2 stage member sp s)).trans (restored r hr)

theorem restored_of_call [Bindings] {l : Layout} {sp : BitVec 64} {s u t : RamState}
    {boundary : ReturnBoundary} {outputBytes reserve : Nat} {target : RamState → BitVec 64}
    {ret : BitVec 64} (flow : Flow l) (effect : (callEffect target ret s).Holds s u)
    (result : CalleeResult u t boundary outputBytes reserve)
    (restored : ∀ r ∈ l.bufferRestore, Blocks.readReg s r = l.buffer sp) :
    ∀ r ∈ l.bufferRestore, Blocks.readReg t r = l.buffer sp := by
  intro r hr
  exact (call_result_register effect result
    (by simpa only [BitVec.toNat_setWidth_of_le (by decide : 4 ≤ 5)] using r.isLt)
    (nonvolatile_extended (flow.restoredSaved r hr).1)).trans (restored r hr)

theorem Preserved.buffer_register [Bindings] {l : Layout} {initial s t : RamState}
    {n : Nat} {regions : Vector MemoryRegion n} (state : Preserved l initial s t regions)
    (flow : Flow l) (buffer : ∀ r ∈ l.bufferSource, Blocks.readReg s r = l.buffer (l.sp initial)) :
    ∀ r ∈ l.bufferSource, Blocks.readReg t r = l.buffer (l.sp initial) := by
  intro r member
  exact (state.frame.registers (r.setWidth 5)
    (by simpa only [BitVec.toNat_setWidth_of_le (by decide : 4 ≤ 5)] using r.isLt)
    (flow.bufferSaved r member).1).trans (buffer r member)

theorem Preserved.copy_register [Bindings] {l : Layout} {initial s t : RamState}
    {n : Nat} {regions : Vector MemoryRegion n} (state : Preserved l initial s t regions)
    (targets : CallTargets l) {site : CallSite} (member : site ∈ [l.smallCall, l.fillCall, l.tailCall])
    (register : ∀ r, site.encoding = .register r → Blocks.readReg s r = 0x10dd60) :
    ∀ r, site.encoding = .register r → Blocks.readReg t r = 0x10dd60 := by
  intro r encoding
  have kept := targets.copies site member
  rw [encoding] at kept
  exact (state.frame.registers (r.setWidth 5)
    (by simpa only [BitVec.toNat_setWidth_of_le (by decide : 4 ≤ 5)] using r.isLt) kept.2).trans
    (register r encoding)

end Sha2.Proofs.Common.SHA256.Absorb
