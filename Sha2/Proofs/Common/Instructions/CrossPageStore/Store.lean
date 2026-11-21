import Sha2.Proofs.Common.Instructions.CrossPageStore.Memory
import X86Proofs.Program.ReadWrite.Store

set_option autoImplicit false

namespace Sha2.Proofs.Common.Instructions.CrossPageStore

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

structure Writable (s : RamState) (addr : BitVec 64) (len : Nat) : Prop
    extends MemReadable s addr len where
  tables : PageTableEntriesApart addr.toNat len

theorem Writable.of_external_eq {s t : RamState} {addr : BitVec 64} {len : Nat}
    (h : Writable s addr len) (he : t.external = s.external) : Writable t addr len :=
  ⟨h.toMemReadable.of_external_eq he, h.tables⟩

theorem Writable.of_memWritable {s : RamState} {addr : BitVec 64} {len : Nat}
    (h : X86Proofs.MemWritable s addr len) : Writable s addr len :=
  ⟨h.readable, h.tables⟩

structure Pre (p : BitVec 64) (codeLen : Nat) (addr : RamState → BitVec 64) (len : Nat)
    (s : RamState) : Prop where
  rip : s.RIP = p
  write : Writable s (addr s) len
  code : RangeApart (addr s) len p codeLen

theorem effect_step_of_store_pre [Bindings] {P : RamState → Prop} {p : BitVec 64}
    {bytes : List UInt8} {len : Nat} {n : Nat} (hn : n % 8 = 0) (h64 : n ≤ 128)
    (addr : RamState → BitVec 64) (v : RamState → BitVec n)
    (hpre : ∀ s, P s → Pre p len addr (n / 8) s)
    (hstep : ∀ s, ReadyToStep s → CodeIn (codeRange p bytes) s → P s →
      X86.Machine.step s = some (.next (afterStep s len fun t =>
        writeResult (dataAccess t "store") (.mem (addr s) : Operand n) (v s)
          (BitVec.add p (BitVec.ofNat 64 len))))) :
    StepEffect P (codeRange p bytes) (storeEffect p len addr v) := by
  intro s h hcode hs
  have hp := hpre s hs
  exact ⟨_, hstep s h hcode hs,
    ReadyToStep.afterStep_store h _ _ _ _ hp.write.low hp.write.tables,
    ⟨afterStep_store_rip h _ _ _ _, Operand.read_afterStep_store s _ hn h64 _ _ _, trivial,
      AgreesExcept.afterStep_store s _ _ _ _⟩⟩

theorem effect_step_of_store [Bindings] {p : BitVec 64} {bytes : List UInt8} {len : Nat}
    {n : Nat} (hn : n % 8 = 0) (h64 : n ≤ 128)
    (addr : RamState → BitVec 64) (v : RamState → BitVec n)
    (hstep : ∀ s, ReadyToStep s → CodeIn (codeRange p bytes) s →
      Pre p len addr (n / 8) s →
      X86.Machine.step s = some (.next (afterStep s len fun t =>
        writeResult (dataAccess t "store") (.mem (addr s) : Operand n) (v s)
          (BitVec.add p (BitVec.ofNat 64 len))))) :
    StepEffect (Pre p len addr (n / 8)) (codeRange p bytes) (storeEffect p len addr v) :=
  effect_step_of_store_pre hn h64 addr v (fun _ h => h) hstep

end Sha2.Proofs.Common.Instructions.CrossPageStore
