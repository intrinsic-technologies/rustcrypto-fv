import Md5.Proofs.Memory.Basic
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Not.Generated.R.Triple
import X86Proofs.Instructions.Rol.Generated.R.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Xor.Generated.RM.Triple
import X86Proofs.Instructions.Xor.Generated.MR.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Movs.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple

namespace Md5.Proofs.Buffered.Update.Counter

open X86 X86.Machine X86.UserProcess X86Proofs X86.Helpers

theorem afterStep_rmw_ready [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) {n : Nat} (addr : BitVec 64) (out : RamState → BitVec n × StatusFlags)
    (oracleUsed : Nat) (nextIP : BitVec 64)
    (htables : ∀ i < n / 8, ¬ Md5.Spec.Program.InPageTables (addr + BitVec.ofNat 64 i)) :
    ReadyToStep (afterStep s length fun t ↦ writeRmwOutputs t addr (out t) oracleUsed nextIP) := by
  have hst : SameControls s (afterStep s length fun t ↦
      writeRmwOutputs t addr (out t) oracleUsed nextIP) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hc := h.cpu
  have hr := h.ready
  have hmem : Prelude.IdentityMappedMemory (afterStep s length fun t ↦
      writeRmwOutputs t addr (out t) oracleUsed nextIP) := by
    refine ⟨h.memory.cr3, ?_⟩
    rw [afterStep_rmw_external]
    exact Md5.Proofs.Memory.identityPageTableMemory_memStore h.memory.tables _ _ htables
  exact ⟨⟨hc.cs, hc.ss, hc.ds, hc.es, hc.cpl, hc.cr0, hc.cr4, hc.efer, hc.maxPhysical, hc.early,
      reportsCPUFeature_of_sameControls hst hc.lam, reportsCPUFeature_of_sameControls hst hc.lass,
      hc.debug, hc.aet⟩,
    hmem,
    ⟨hr.event, hr.active, hr.sti, hr.movss, hr.singleStep, hr.taskSwitch, hr.breakpoint,
      hr.busLock, StatusFlags.trapFlagClear_store _ hr.tf, StatusFlags.resumeFlagClear_store _ hr.rf,
      hr.repeatClear, hr.msr⟩,
    smrrUnblocked_of_sameControls hst h.smrr, writeBackMemoryType_of_sameControls hst h.memoryType,
    h.features.of_sameControls hst⟩

@[x86_compose] def incM64Effect (p : BitVec 64) (am : AddrMode) (s : RamState) : Effect :=
  let a := am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))
  { rip := p + BitVec.ofNat 64 (3 + am.tail.length)
    writes := [⟨(.mem a : Operand 64), (Operand.mem a : Operand 64).read s + 1⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

@[x86_compose] def addM64R64Effect (p : BitVec 64) (src : BitVec 5) (am : AddrMode)
    (s : RamState) : Effect :=
  let a := am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))
  { rip := p + BitVec.ofNat 64 (3 + am.tail.length)
    writes := [⟨(.mem a : Operand 64),
      (Operand.mem a : Operand 64).read s + (Operand.reg src : Operand 64).read s⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

@[x86_local] theorem incM64Effect_local (p : BitVec 64) (am : AddrMode) :
    Effect.Local (incM64Effect p am) := by
  refine ⟨fun t t' h ↦ ?_, fun t t' h ↦ ?_, fun t t' h ↦ ?_, fun t t' h i hi ↦ ?_, fun t ↦ ?_⟩
  · simp [incM64Effect]
  · simp [incM64Effect, h.read_mem, AddrMode.addr_obs h]
  · simp [incM64Effect]
  · cases i <;> simp [incM64Effect, Effect.flag, StatusFlagsOutcome.get]
  · simp [incM64Effect, Write.Full, Operand.Full]

@[x86_local] theorem addM64R64Effect_local (p : BitVec 64) (src : BitVec 5) (am : AddrMode) :
    Effect.Local (addM64R64Effect p src am) := by
  refine ⟨fun t t' h ↦ ?_, fun t t' h ↦ ?_, fun t t' h ↦ ?_, fun t t' h i hi ↦ ?_, fun t ↦ ?_⟩
  · simp [addM64R64Effect]
  · simp [addM64R64Effect, h.read_reg, h.read_mem, AddrMode.addr_obs h]
  · simp [addM64R64Effect]
  · cases i <;> simp [addM64R64Effect, Effect.flag, StatusFlagsOutcome.get]
  · simp [addM64R64Effect, Write.Full, Operand.Full]

end Md5.Proofs.Buffered.Update.Counter
